use cxt::Cxt;
use parser::syntax::{Either, Icit, Raw};
use pattern_match::Compiler;
use syntax::{Locals, Pruning, close_ty};
use pretty::pretty_tm;

use crate::list::List;
use crate::parser_lib::Span;

pub mod cxt;
mod elaboration;
pub mod parser;
mod pattern_match;
mod syntax;
mod unification;
mod typeclass;
pub(crate) mod bump_spine_iter;
mod pretty;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MetaVar(u32);

#[derive(Debug, Clone)]
enum MetaEntry {
    Solved(Rc<Val>, Rc<VTy>),
    Unsolved(Rc<VTy>),
}

#[derive(Debug, Clone, Copy)]
pub struct Ix(u32);

#[derive(Debug, Clone)]
enum BD {
    Bound,
    Defined,
}

#[derive(Clone, Debug)]
pub enum DeclTm {
    Def {
        name: Span<String>,
        typ: Rc<Val>,
        body: Rc<Val>,
    },
    Println(Rc<Tm>),
    Enum {
        //TODO:
    },
    Trait {
        //TODO:
    },
    TraitImpl {
        //TODO:
    },
}

#[derive(Debug, Clone)]
pub enum Tm {
    Var(Ix),
    Obj(Rc<Tm>, Span<String>),
    Lam(Span<String>, Icit, Rc<Tm>),
    App(Rc<Tm>, Rc<Tm>, Icit),
    AppPruning(Rc<Tm>, Pruning),
    U(u32),
    Pi(Span<String>, Icit, Rc<Ty>, Rc<Ty>),
    Let(Span<String>, Rc<Ty>, Rc<Tm>, Rc<Tm>),
    Meta(MetaVar),
    LiteralType,
    LiteralIntro(Span<String>),
    Prim,
    Sum(Span<String>, Vec<(Span<String>, Rc<Tm>, Rc<Ty>, Icit)>, Vec<Span<String>>, bool),
    SumCase {
        typ: Rc<Tm>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Rc<Tm>, Icit)>,
        is_trait: bool,
    },
    Match(Rc<Tm>, Vec<(PatternDetail, Rc<Tm>)>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum PatternDetail {
    Any(Span<()>),
    Bind(Span<String>),
    Con(Span<String>, Vec<PatternDetail>),
}

impl PatternDetail {
    fn bind_count(&self) -> u32 {
        match self {
            PatternDetail::Any(_) => 1,
            PatternDetail::Bind(_) => 1,
            PatternDetail::Con(_, pattern_details) => {
                pattern_details.iter().map(|pattern_detail| pattern_detail.bind_count()).sum::<u32>()
            },
        }
    }
}

/// 已走查臂在某嵌套位置的覆盖贡献（参考版与孪生版共用，保证嵌套覆盖
/// 检查的判定与文案逐字节一致；L07 同款，2026-09-18 评审修复）：全覆盖
/// （var/Any，含路径中途变变量）、贡献某构造子（路径末端是 Con）、不可达
/// 该位置（祖先选了别的构造子）。
pub(crate) enum PosCover {
    All,
    Ctor(String),
    None,
}

/// 沿 (构造子名, 字段下标) 路径下钻一棵已走查的 PatternDetail 树。
/// 字段下标与 `walk_pat` 的 details 布局同源（望远镜中产槽绑定器的序数）。
pub(crate) fn cover_at(detail: &PatternDetail, path: &[(String, usize)]) -> PosCover {
    let mut cur = detail;
    for (ctor, field) in path {
        match cur {
            PatternDetail::Any(_) | PatternDetail::Bind(_) => return PosCover::All,
            PatternDetail::Con(n, subs) if n.data == *ctor => cur = &subs[*field],
            PatternDetail::Con(..) => return PosCover::None,
        }
    }
    match cur {
        PatternDetail::Any(_) | PatternDetail::Bind(_) => PosCover::All,
        PatternDetail::Con(n, _) => PosCover::Ctor(n.data.clone()),
    }
}

/// 人读路径：`cons#2 → nil#1` 表示 cons 第二字段的 nil 第一字段处。
pub(crate) fn fmt_path(path: &[(String, usize)]) -> String {
    path.iter()
        .map(|(c, f)| format!("{c}#{}", f + 1))
        .collect::<Vec<_>>()
        .join(" → ")
}

type Ty = Tm;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd)]
pub struct Lvl(u32);

impl Add<u32> for Lvl {
    type Output = Lvl;
    fn add(self, rhs: u32) -> Lvl {
        Lvl(self.0 + rhs)
    }
}

impl Sub<u32> for Lvl {
    type Output = Lvl;
    fn sub(self, rhs: u32) -> Lvl {
        Lvl(self.0 - rhs)
    }
}

type Env = List<Rc<Val>>;
type Spine = List<(Rc<Val>, Icit)>;

#[derive(Clone)]
pub struct Closure(Env, Rc<Tm>);

impl std::fmt::Debug for Closure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Closure(.., {:?})", self.1)
    }
}

#[derive(Debug, Clone)]
pub enum Val {
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    Obj(Rc<Val>, Span<String>, Spine),
    Lam(Span<String>, Icit, Closure),
    Pi(Span<String>, Icit, Rc<VTy>, Closure),
    U(u32),
    LiteralType,
    LiteralIntro(Span<String>),
    Prim,
    Sum(
        Span<String>,
        Vec<(Span<String>, Rc<Val>, Rc<VTy>, Icit)>,
        Vec<Span<String>>,
        bool,
    ),
    SumCase {
        is_trait: bool,
        typ: Rc<Val>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Rc<Val>, Icit)>,
    },
    Match(Rc<Val>, Env, Vec<(PatternDetail, Rc<Tm>)>),
    /// 显式替换下的值（模式精化，dpm-nbe `VSub`）：特化解不改写既有值，
    /// 只把解包在外面；`force` 在读点把 σ 推进值的结构（`frcs`，对齐
    /// dpm-nbe 的 `frcS`）。不变式：`force` 的返回值顶层不会是 VSub
    /// （fuel 耗尽时为有界降级的例外，各消费点有防御臂）。
    VSub(Rc<Val>, Rc<Subst>),
}

type VTy = Val;

/// 模式特化的解：层级 → 值 的有限映射（dpm-nbe 的 explicit substitution）。
/// 仅由模式编译器经 `Subst::extend` / 特化合一的 `SpecSolve::acc` 构建；
/// `Rc` 共享让臂边界回滚 = 指针赋值、`Val::VSub` 包裹 = O(1)。
///
/// σ 表示为**持久化单链**（链头 = 最新）：`extend` O(1) cons、`lookup`
/// 沿链首个命中 + 条件包裹（解值浅结构不引用任何已解层级时原样返回，
/// 零分配零 fuel；引用才包 `VSub(·, σ)`，由 force 读点推开）。
///
/// 与旧 `update_cxt` 的对应：旧机制把解**改写进环境槽**并 refresh 全量
/// 重引用（L07 README §6 淘汰的旧架构，值过期/槽位错位 bug 族的载体）；
/// 新机制不动槽位，只把 σ 包在被消费的值外，force 在读点逐层推开。
#[derive(Debug, Clone, Default)]
pub struct Subst {
    head: Option<Rc<SubEntry>>,
}

#[derive(Debug)]
struct SubEntry {
    lvl: Lvl,
    /// 解的原始值。不预先包裹"更新的解"——读取时 `lookup_hit` 把整条 σ
    /// 包在外面（见其文档），由 force 在读点一次性推开。
    val: Val,
    next: Option<Rc<SubEntry>>,
}

impl Subst {
    pub(crate) fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// 命中返回 Some(展开前形态)：解值**不引用**任何已解层级时原样返回
    /// （读点热路径，零分配零 fuel）；引用时把整条 σ 包在解值外（解值不含
    /// x 自身——occurs 守卫；也不含更旧解的 bare 引用——solve 存值已 force、
    /// 头部精化值已 wrap），由 force 在读点推开。未命中 None。
    pub(crate) fn lookup_hit(self: &Rc<Self>, x: Lvl) -> Option<Val> {
        let mut cur = self.head.clone();
        while let Some(e) = cur {
            if e.lvl == x {
                return Some(if !Self::mentions_level(&e.val, self) {
                    e.val.clone()
                } else {
                    Val::VSub(Rc::new(e.val.clone()), self.clone())
                });
            }
            cur = e.next.clone();
        }
        None
    }

    /// 未映射即 fresh rigid（dpm-nbe `lookupSub` 的恒等延拓）。
    pub(crate) fn lookup(self: &Rc<Self>, x: Lvl) -> Val {
        self.lookup_hit(x).unwrap_or_else(|| Val::vvar(x))
    }

    /// 解值的浅结构是否引用 σ 的某个已解层级。含闭包 **env 槽**（它们是
    /// 值，读点会流出）与 Match 的 scrutinee/captured env；不含闭包体 /
    /// Match 分支体（Tm，求值时才经 env 读到槽值）。VSub 保守记为引用。
    /// 误报只多一次包裹，漏报才会丢精化——扫描口径宁宽勿窄。
    fn mentions_level(v: &Val, sub: &Subst) -> bool {
        fn env_slots(env: &Env, sub: &Subst) -> bool {
            env.iter().any(|v| mentions_level(v, sub))
        }
        fn mentions_level(v: &Val, sub: &Subst) -> bool {
            match v {
                Val::Rigid(y, sp) => sub.has(*y) || sp.iter().any(|(u, _)| mentions_level(u, sub)),
                Val::Flex(_, sp) => sp.iter().any(|(u, _)| mentions_level(u, sub)),
                Val::Obj(o, _, sp) => {
                    mentions_level(o, sub) || sp.iter().any(|(u, _)| mentions_level(u, sub))
                }
                Val::Lam(_, _, cl) => env_slots(&cl.0, sub),
                Val::Pi(_, _, a, cl) => mentions_level(a, sub) || env_slots(&cl.0, sub),
                Val::Sum(_, params, _, _) => params
                    .iter()
                    .any(|(_, v, t, _)| mentions_level(v, sub) || mentions_level(t, sub)),
                Val::SumCase { typ, datas, .. } => {
                    mentions_level(typ, sub)
                        || datas.iter().any(|(_, v, _)| mentions_level(v, sub))
                }
                Val::Match(s, env, _) => mentions_level(s, sub) || env_slots(env, sub),
                // 已被包裹的值保守视为引用（内层结构不再探查）
                Val::VSub(..) => true,
                Val::U(_) | Val::LiteralType | Val::LiteralIntro(_) | Val::Prim => false,
            }
        }
        mentions_level(v, sub)
    }

    /// x 是否已有解（旧 `update_cxt` 前 `pm_def` 式的"已解"判定）。
    pub(crate) fn has(&self, x: Lvl) -> bool {
        let mut cur = self.head.clone();
        while let Some(e) = cur {
            if e.lvl == x {
                return true;
            }
            cur = e.next.clone();
        }
        false
    }

    /// 叠加一条解 `x := v`：O(1) cons 到链头（链头 = 最新 ≙ 旧 `update_cxt`
    /// 后写覆盖先写；同键旧条目留在链上但永不命中）。
    pub(crate) fn extend(sub: &Rc<Subst>, x: Lvl, v: Val) -> Rc<Subst> {
        Rc::new(Subst {
            head: Some(Rc::new(SubEntry {
                lvl: x,
                val: v,
                next: sub.head.clone(),
            })),
        })
    }

    /// 组合：内层 `inner` 先应用、外层 `outer` 后应用。外层条目接到链头
    /// （先被查到 = 覆盖同键）——对齐旧 `update_cxt` 的"后写覆盖"语义；
    /// dpm-nbe 的左偏 union 在其无冲突场景下与此等价。
    pub(crate) fn compose(outer: &Rc<Subst>, inner: &Rc<Subst>) -> Rc<Subst> {
        fn cons_all(entry: &Option<Rc<SubEntry>>, onto: Option<Rc<SubEntry>>) -> Option<Rc<SubEntry>> {
            match entry {
                None => onto,
                Some(e) => Some(Rc::new(SubEntry {
                    lvl: e.lvl,
                    val: e.val.clone(),
                    next: cons_all(&e.next, onto),
                })),
            }
        }
        Rc::new(Subst {
            head: cons_all(&outer.head, inner.head.clone()),
        })
    }
}

/// η 展开与 frcs 读点共用的可应用性守卫（L06/L07 同款）：只有 `v_app`
/// 能吃的形态（中性头 / 卡住投影 / VSub）允许应用。字面量 / U / Π /
/// Sum / SumCase 与实参相遇时无从应用——不加守卫会命中 `v_app` 的
/// `impossible apply` panic。
pub(crate) fn v_applicable(v: &Val) -> bool {
    matches!(
        v,
        Val::Flex(..) | Val::Rigid(..) | Val::Obj(..) | Val::VSub(..)
    )
}

/// "解前构建、解后消费"的值的读点纪律：用当前精化替换包裹（O(1) Rc，
/// force 在消费点惰性推开）。σ 为空时零开销直通。
pub(crate) fn wrap_sub(sub: &Rc<Subst>, v: Val) -> Val {
    if sub.is_empty() {
        v
    } else {
        Val::VSub(Rc::new(v), sub.clone())
    }
}

/// 展开燃料：每个展开步骤消耗 1，耗尽即停止（防环）。force 的各展开臂
/// 与 frcs 的 lookup 命中点共用。
fn burn(cell: &std::cell::Cell<u32>) -> bool {
    let f = cell.get();
    if f == 0 {
        return false;
    }
    cell.set(f - 1);
    true
}

/// 值树里是否出现某层级（浅层结构扫描；闭包体 / Match 分支体跳过——那里
/// 的环由 force 的 fuel 兜底）。特化解的環守卫（`unify_pm` 的 occurs）用。
fn val_mentions_lvl(v: &Val, x: Lvl) -> bool {
    fn spine(sp: &Spine, x: Lvl) -> bool {
        sp.iter().any(|(v, _)| val_mentions_lvl(v, x))
    }
    fn env_slots(env: &Env, x: Lvl) -> bool {
        env.iter().any(|v| val_mentions_lvl(v, x))
    }
    match v {
        Val::Rigid(y, sp) => *y == x || spine(sp, x),
        // **不扫 Flex 的 spine**（L10 定制）：L10 的元变量以"全 scope 剪枝
        // spine"登记（fresh_meta 的 AppPruning），spine 里合法地含当前方程
        // 正在解的 rigid（如 `l := succ ?m` 里 ?m 的 spine 含 l）。旧
        // `update_cxt` 没有 occurs 守卫，扫 spine 会把这类合法解误判成环，
        // 使 GADT 嵌套 match 的分支误报不可达（test5/test6/test_index/
        // test0/test7 回归）。元变量是中性头，其 spine 是作用域事实而非解值
        // 结构；真环仍由 force 的 fuel 兜底（与旧机制一致）。
        Val::Flex(..) => false,
        Val::Obj(o, _, sp) => val_mentions_lvl(o, x) || spine(sp, x),
        Val::Lam(_, _, cl) => env_slots(&cl.0, x),
        Val::Pi(_, _, a, cl) => val_mentions_lvl(a, x) || env_slots(&cl.0, x),
        Val::Sum(_, params, _, _) => params
            .iter()
            .any(|(_, v, t, _)| val_mentions_lvl(v, x) || val_mentions_lvl(t, x)),
        Val::SumCase { typ, datas, .. } => {
            val_mentions_lvl(typ, x) || datas.iter().any(|(_, v, _)| val_mentions_lvl(v, x))
        }
        Val::Match(s, env, _) => val_mentions_lvl(s, x) || env_slots(env, x),
        // 只扫解值自身的结构，**不扫 σ 的映射值**：σ 的其它条目（如头部
        // 精化的构造子值）合法引用别的模式变量，扫进来会把无害的解误判
        // 成环。σ 槽位若真引用 x，解包后的 v 结构里自会以 Rigid(x) 出现
        // （对齐旧世界"occurs 只看解的裸值"的语义；更深的间接环仍由
        // force 的 fuel 兜底）。
        Val::VSub(v, _) => val_mentions_lvl(v, x),
        Val::U(_) | Val::LiteralType | Val::LiteralIntro(_) | Val::Prim => false,
    }
}

impl Val {
    fn vvar(x: Lvl) -> Self {
        Val::Rigid(x, List::new())
    }

    fn vmeta(m: MetaVar) -> Self {
        Val::Flex(m, List::new())
    }
}

fn lvl2ix(l: Lvl, x: Lvl) -> Ix {
    // 全局层级哨兵：global_idx 从 0 起（`global_idx + 1919810`），故 0 号
    // 全局恰好等于 1919810——边界必须是 `>=`（eval 的 `x - 1919810` 与快版
    // `*i >= GLOBAL_BASE` 同口径）。用 `>` 会让首个声明的自引用走
    // `l - x - 1` 下溢（debug panic / release 大索引越界）。
    if x.0 >= 1919810 {
        Ix(x.0)
    } else {
        Ix(l.0 - x.0 - 1)
    }
}

use std::{
    collections::HashMap,
    ops::{Add, Sub}, rc::Rc,
};

use rustc_hash::FxHashMap;

#[derive(Debug)]
enum UnifyError {
    Basic,
    Trait(String),
}

fn empty_span<T>(data: T) -> Span<T> {
    Span {
        data,
        start_offset: 0,
        end_offset: 0,
        path_id: 0,
    }
}

#[derive(Debug)]
pub struct Error(pub Span<String>);

/// unify/force 的共享递归 fuel 池容量（L08 护栏前向传播：L09 重写时
/// 丢失，L10 恢复；防 meta 解链环的无限展开与深递归栈溢出）。
const UNIFY_FUEL: u32 = 4096;

#[derive(Clone)]
pub struct Infer {
    meta: Vec<MetaEntry>,
    global: HashMap<Lvl, Rc<VTy>>,
    /// 顶层名字表（名字 → (层级, 类型值)）：**append-only，随 Infer 存续、
    /// 不随 Cxt 克隆**——顶层 def/enum/构造子的真名与 `fake_bind` 的递归
    /// 占位都记在这里（2026-09-20 参考版 O(D²) 修复）。
    ///
    /// 旧设计把顶层名累积进 `Cxt.src_names`（每声明 +1 条），而 `fake_bind`
    /// / `define` 每次克隆整表（表大小 O(D)）⇒ 每声明 2 次全表克隆、总计
    /// O(D²)（L10 strchain k=11 实测 929ms vs 孪生 3.2ms，见
    /// `docs/perf-debt-2026-09-12.md` P2 的孪生侧同款处置）。查找顺序：
    /// `cxt.src_names`（局部，遮蔽）优先，回落本表。
    global_names: FxHashMap<String, (Lvl, Rc<VTy>)>,
    trait_solver: typeclass::Synth,
    trait_definition: HashMap<String, (Vec<(Span<String>, Raw, Icit)>, Vec<bool>, Vec<(Span<String>, Vec<(Span<String>, Raw, Icit)>, Raw)>)>,
    trait_out_param: HashMap<String, Vec<bool>>,
    /// **中性全局视图开关**（孪生 `Machine.neutral` 视图的参考版形态）：
    /// 置位期间 `eval` 的全局回落返回中性 rigid（`Rigid(GLOBAL_BASE + idx)`）
    /// 而非全局值——Match/Match 合一、`rename` 与 `quote` 的分支体重求值要
    /// 的"全局名字不再递归展开"视图（求值函数全为 `&self`，Cell 提供内部
    /// 可变性；可嵌套，存旧值恢复）。
    ///
    /// 旧实现是三处 `self.clone()` 整个 Infer 再就地改写 global 表——L10 的
    /// Infer 还带 trait_solver / trait_definition / trait_out_param 三张表，
    /// 每次克隆都跟着深拷（孪生侧曾以 `neutral_of(&self.globals)` 整拷同病，
    /// perf-debt P2 残余平方项）；开关是 O(1)，语义逐值一致：原先被改写的
    /// 每个条目恰好是"已登记的全局 → 中性 rigid"，未登记的仍 panic（本字段
    /// 只改回落路径的取值，不改可达性）。
    neutral_globals: std::cell::Cell<bool>,
    /// unify/force 共享 fuel 池（L08 同款）：外层入口（`nf`/`unify_catch`）
    /// 充值；`unify` 递归与 `force` 的 meta 展开各烧 1，耗尽时 unify 按
    /// 不可合一失败、force 停止展开按未解处理。
    unify_fuel: std::cell::Cell<u32>,
}

impl Infer {
    pub fn new() -> Self {
        Self {
            meta: vec![],
            global: HashMap::new(),
            global_names: FxHashMap::default(),
            trait_solver: Default::default(),
            trait_definition: Default::default(),
            trait_out_param: Default::default(),
            neutral_globals: std::cell::Cell::new(false),
            unify_fuel: std::cell::Cell::new(UNIFY_FUEL),
        }
    }
    /// 顶层名的局部影子：`Cxt::new` 的两个内建（`String` /
    /// `string_concat`）留在局部表里，而 `Raw::Var` / 构造子探测一律**局部
    /// 优先**；旧单表语义是"后定义覆盖先定义"，两表分离后顶层 def 若与内建
    /// 撞名，必须同步覆写局部条目，否则新 def 反被内建遮蔽（同名递归 def
    /// 的自身引用也会指错）。无同名时是纯读。
    fn shadow_local(cxt: &mut Cxt, x: &Span<String>, lvl: Lvl, ty: &Rc<VTy>) {
        if cxt.src_names.get(&x.data).is_some() {
            cxt.src_names.insert(x.data.clone(), (lvl, ty.clone()));
        }
    }
    /// `Cxt::fake_bind` 的 Infer 侧形态：递归 def/enum 的占位——名字指到
    /// 全局层级（`global_idx + 1919810`），env/lvl/locals/pruning 一概不动，
    /// 返回父上下文的视图。真名随后由 [`Self::define_global`] 覆盖同一条目
    /// （占位只服务本次检查的体）。
    fn fake_bind(&mut self, cxt: &Cxt, x: Span<String>, a: Rc<VTy>, global_idx: Lvl) -> Cxt {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), cxt.lvl.0);
        let lvl = global_idx + 1919810;
        self.global_names.insert(x.data.clone(), (lvl, a.clone()));
        let mut out = cxt.clone();
        Self::shadow_local(&mut out, &x, lvl, &a);
        out
    }
    /// 顶层 define（`Decl::Def` / `Decl::Enum` / 构造子登记）：真名进
    /// [`Self::global_names`]（append-only，不随 Cxt 克隆），槽位照旧——env
    /// 压值、lvl +1、telescope 压 `Define` 槽、pruning 记 `None`。局部表
    /// 不增长，故本次返回的 Cxt 克隆是 O(1)（孪生 `define_name_in` 同款）。
    fn define_global(
        &mut self,
        cxt: &Cxt,
        x: Span<String>,
        t: Rc<Tm>,
        vt: Rc<Val>,
        a: Rc<Ty>,
        va: Rc<VTy>,
    ) -> Cxt {
        //println!("{} {}\n{t:?}\n{vt:?}\n{a:?}\n{va:?}", "define_global".bright_purple(), x.data);
        self.global_names.insert(x.data.clone(), (cxt.lvl, va.clone()));
        let mut out = Cxt {
            env: cxt.env.prepend(vt),
            lvl: cxt.lvl + 1,
            locals: Rc::new(Locals::Define(cxt.locals.clone(), x.clone(), a, t)),
            pruning: cxt.pruning.prepend(None),
            src_names: cxt.src_names.clone(),
        };
        Self::shadow_local(&mut out, &x, cxt.lvl, &va);
        out
    }
    /// 烧 1 格 fuel；池空返回 `false`（调用方按各自失败语义降级）。
    fn burn_fuel(&self) -> bool {
        let f = self.unify_fuel.get();
        if f == 0 {
            return false;
        }
        self.unify_fuel.set(f - 1);
        true
    }
    /// 外层入口充值（L08 `meta_refuel` 同款纪律）。
    fn refuel(&self) {
        self.unify_fuel.set(UNIFY_FUEL);
    }
    /// fuel 是否已耗尽（L07 同款观察口）：可达性探测在合一失败后用它区分
    /// "结构冲突"与"预算耗尽的假 absurd"——后者按可达处理（保守要求覆盖）。
    pub(crate) fn fuel_exhausted(&self) -> bool {
        self.unify_fuel.get() == 0
    }
    fn new_meta(&mut self, a: Rc<VTy>) -> u32 {
        self.meta.push(MetaEntry::Unsolved(a));
        self.meta.len() as u32 - 1
    }
    fn fresh_meta(&mut self, cxt: &Cxt, a: Rc<VTy>) -> Rc<Tm> {
        // 期望类型可能被精化 σ 包裹：先推开，实例合成 / trait 判形才看得到
        // 真实形态（对齐旧 refresh 后槽值已展开的世界）
        let a = self.force(&a);
        if let Ok(Some((a, _))) = self.solve_trait(cxt, &a) {
            a
        } else if let Val::Sum(_, _, _, true) = a.as_ref() {
            let m = self.new_meta(a);
            Tm::Meta(MetaVar(m)).into()
        } else {
            let closed = self.eval(
                &List::new(),
                &close_ty(&cxt.locals, self.quote(cxt.lvl, &a)),
            );
            let m = self.new_meta(closed);
            Tm::AppPruning(Tm::Meta(MetaVar(m)).into(), cxt.pruning.clone()).into()
        }
    }
    fn lookup_meta(&self, m: MetaVar) -> &MetaEntry {
        &self.meta[m.0 as usize]
    }
    fn force(&self, t: &Rc<Val>) -> Rc<Val> {
        //println!("{} {:?}", "force".red(), t);
        match t.as_ref() {
            Val::Flex(m, sp) => match self.lookup_meta(*m) {
                // 展开烧 fuel（L08 前向传播）：solve 无跨 meta occurs check，
                // 解链成环时展开会无限递归；池空停止展开、按未解处理
                MetaEntry::Solved(t_solved, _) if self.burn_fuel() => {
                    self.force(&self.v_app_sp(t_solved.clone(), sp))
                }
                _ => Val::Flex(*m, sp.clone()).into(),
            },
            // 显式替换（dpm-nbe `frc`）：把模式精化的解推进值的结构。入口
            // 不烧 fuel——真正的精化传播只发生在被解变量的读点（frcs 的
            // Rigid 臂 lookup 命中时烧 1），对齐旧 `update_cxt`+`refresh`
            // 时代"读到被解槽才展开"的燃烧剖面；包裹/组合的机械开销免费。
            Val::VSub(v, sub) => self.frcs(sub, v.clone()),
            Val::Obj(x, a, b) => {
                Val::Obj(self.force(x), a.clone(), b.clone()).into()
            }
            _ => t.clone(),
        }
    }

    /// 把替换 `σ` 推进值 `v` 的结构（dpm-nbe `frcS`）。与 `force` 的分工：
    /// σ 是本次精化的局部解，只作用于**被包裹过**的值；推进到中性头为止
    /// ——spine 逐槽推进，闭包 env 逐槽包裹（惰性，不进入闭包体重求值）。
    /// 槽位命中 `Rigid` 且 σ 有解时经 `v_app` 应用（λ ⇒ β；中性头 ⇒ spine
    /// 拼接），对应 dpm-nbe `napp (lookupSub sb v) (frcS sb sp)`。
    fn frcs(&self, sub: &Rc<Subst>, v: Rc<Val>) -> Rc<Val> {
        if sub.is_empty() {
            return self.force(&v);
        }
        match v.as_ref() {
            // 内层先应用、外层后应用：组合后一次推进（frcS (subst sb sb') v）
            Val::VSub(v2, sub2) => {
                let composed = Subst::compose(sub, sub2);
                self.frcs(&composed, v2.clone())
            }
            // 被解变量的读点：lookup 命中（真正的精化传播）烧 1 fuel——
            // 对齐旧 refresh 重求值被解槽的燃烧剖面；fuel 耗尽按未解处理
            // （返回裸 rigid，有界降级，防闭环无限推进）。解值带实参但头
            // 不可应用（对非函数解变量做应用的 ill-typed 形态）时保持卡住。
            Val::Rigid(x, sp) => {
                let mut head = match sub.lookup_hit(*x) {
                    Some(hit) => {
                        if !burn(&self.unify_fuel) {
                            return Rc::new(Val::Rigid(*x, sp.clone()));
                        }
                        self.force(&Rc::new(hit))
                    }
                    None => Rc::new(Val::vvar(*x)),
                };
                if !sp.is_empty() && !v_applicable(&head) {
                    return Rc::new(Val::Rigid(*x, sp.clone()));
                }
                let args: Vec<(Rc<Val>, Icit)> = sp.iter().cloned().collect();
                for (u, i) in args.into_iter().rev() {
                    head = self.v_app(&head, Rc::new(wrap_sub(sub, (*u).clone())), i);
                }
                head
            }
            // 中性头的 spine 槽只**包裹**不推进——槽位引用是作用域事实，
            // 物化会破坏后续 solve 的 invert（与 force_arg 的分工同一理由；
            // 旧 force 也从不触碰 spine 槽）。包裹后交回 force 重走既有臂
            // （meta 解 / 投影），保持"σ 之下的值 force 到同一 WHNF 形态"
            // 的旧语义。
            Val::Flex(m, sp) => {
                self.force(&Rc::new(Val::Flex(*m, self.wrap_sp(sub, sp.clone()))))
            }
            Val::Obj(o, name, sp) => self.force(&Rc::new(Val::Obj(
                self.frcs(sub, o.clone()),
                name.clone(),
                self.wrap_sp(sub, sp.clone()),
            ))),
            // 闭包 env 逐槽包裹（dpm-nbe `subst sb cl` 的惰性形态）
            Val::Lam(x, i, cl) => Rc::new(Val::Lam(
                x.clone(),
                *i,
                Closure(self.frcs_env(sub, &cl.0), cl.1.clone()),
            )),
            Val::Pi(x, i, a, cl) => Rc::new(Val::Pi(
                x.clone(),
                *i,
                self.frcs(sub, a.clone()),
                Closure(self.frcs_env(sub, &cl.0), cl.1.clone()),
            )),
            // Sum/SumCase 的槽位同样只包裹（旧 force 不进入这些结构）
            Val::Sum(name, params, cases, is_trait) => Rc::new(Val::Sum(
                name.clone(),
                params
                    .iter()
                    .map(|(n, v, t, i)| {
                        (
                            n.clone(),
                            Rc::new(wrap_sub(sub, (**v).clone())),
                            Rc::new(wrap_sub(sub, (**t).clone())),
                            *i,
                        )
                    })
                    .collect(),
                cases.clone(),
                *is_trait,
            )),
            Val::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => Rc::new(Val::SumCase {
                is_trait: *is_trait,
                typ: Rc::new(wrap_sub(sub, (**typ).clone())),
                case_name: case_name.clone(),
                datas: datas
                    .iter()
                    .map(|(n, v, i)| (n.clone(), Rc::new(wrap_sub(sub, (**v).clone())), *i))
                    .collect(),
            }),
            // scrutinee **推进**：旧 `refresh` 在槽值重求值时，若被解变量
            // 是卡住 match 的 scrutinee，会连带重选分支——这里等价地在
            // 推进后若已是构造子值就按首匹配重选。捕获 env 只包裹。
            Val::Match(s, env, cases) => {
                let s2 = self.frcs(sub, s.clone());
                let env2 = self.frcs_env(sub, env);
                if matches!(s2.as_ref(), Val::SumCase { .. }) && burn(&self.unify_fuel) {
                    if let Some((tm, env3)) = Compiler::eval_aux(self, &s2, &env2, cases) {
                        return self.force(&self.eval(&env3, &tm));
                    }
                }
                Rc::new(Val::Match(s2, env2, cases.clone()))
            }
            // U / 字面量 / Prim：σ 无从推进
            _ => v.clone(),
        }
    }

    fn wrap_sp(&self, sub: &Rc<Subst>, sp: Spine) -> Spine {
        if sp.is_empty() {
            return sp;
        }
        sp.map(|(v, i)| (Rc::new(wrap_sub(sub, (**v).clone())), *i))
    }

    fn frcs_env(&self, sub: &Rc<Subst>, env: &Env) -> Env {
        if sub.is_empty() {
            return env.clone();
        }
        env.map(|v| Rc::new(Val::VSub(v.clone(), sub.clone())))
    }

    /// `to_typ` 等"结构消费者"的深读点：force 到 WHNF 后，若顶层是
    /// Sum/SumCase，把**槽位值也 force 推开**（旧机制下这些槽位已被
    /// update_cxt/refresh 物化；新机制只包裹，故此处按需展开）。只服务
    /// trait 求解边界（非热路径），不进入 spine/闭包体。
    pub(crate) fn force_deep(&self, v: &Rc<Val>) -> Rc<Val> {
        let v = self.force(v);
        match v.as_ref() {
            Val::Sum(name, params, cases, is_trait) => Rc::new(Val::Sum(
                name.clone(),
                params
                    .iter()
                    .map(|(n, x, t, i)| (n.clone(), self.force_deep(x), self.force_deep(t), *i))
                    .collect(),
                cases.clone(),
                *is_trait,
            )),
            Val::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => Rc::new(Val::SumCase {
                is_trait: *is_trait,
                typ: self.force_deep(typ),
                case_name: case_name.clone(),
                datas: datas
                    .iter()
                    .map(|(n, x, i)| (n.clone(), self.force_deep(x), *i))
                    .collect(),
            }),
            _ => v,
        }
    }

    /// 合一器**参数视角**的 WHNF：与 `force` 相同，但不展开精化、不做
    /// Match 重选。`invert` / `prune_vflex` 关心的是"元变量被应用在
    /// 哪些槽位上"——槽位引用（`Rigid(x)`）本身就是作用域事实，分支内的
    /// 精化等式（x := zero）不改变槽位的存在；在它们身上展开反而会把
    /// 可逆 spine 变成含构造子值的不可逆 spine。
    pub(crate) fn force_arg(&self, t: Rc<Val>) -> Rc<Val> {
        // 精化包裹的槽位：逐层解包看裸形态（subst_cxt 可叠加——嵌套 match
        // 的上下文被外层臂与内层臂各包一次）。解到底仍是 bare rigid ⇒ 槽位
        // 保留；其余形态全量 force 推开。
        {
            let mut cur: &Val = &t;
            while let Val::VSub(v, _) = cur {
                cur = v;
            }
            match cur {
                Val::Rigid(x, sp) if sp.is_empty() => {
                    return Rc::new(Val::Rigid(*x, List::new()));
                }
                Val::Rigid(..) | Val::Match(..) => return t.clone(),
                _ => {}
            }
        }
        self.force(&t)
    }

    fn v_meta(&self, m: MetaVar) -> Rc<Val> {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v, _) => v.clone(),
            MetaEntry::Unsolved(_) => Val::vmeta(m).into(),
        }
    }

    fn closure_apply(&self, closure: &Closure, u: Rc<Val>) -> Rc<Val> {
        //println!("{} {:?} {:?}", "closure apply".yellow(), closure, u);
        self.eval(&closure.0.prepend(u), &closure.1)
    }

    fn v_app(&self, t: &Rc<Val>, u: Rc<Val>, i: Icit) -> Rc<Val> {
        //println!("v_app {t:?} {u:?}");
        match t.as_ref() {
            // 精化包裹的值先推开再分发（eval(App) 等不经 force 的调用点会
            // 把 VSub 头送进来——如臂上下文里 Var 引用了被解槽）
            Val::VSub(..) => {
                let t = self.force(t);
                self.v_app(&t, u, i)
            }
            Val::Lam(_, _, closure) => self.closure_apply(closure, u),
            Val::Flex(m, sp) => Val::Flex(*m, sp.prepend((u, i))).into(),
            Val::Rigid(x, sp) => Val::Rigid(*x, sp.prepend((u, i))).into(),
            Val::Obj(x, name, sp) => Val::Obj(x.clone(), name.clone(), sp.prepend((u, i))).into(),
            x => panic!("impossible apply\n  {:?}\nto\n  {:?}", x, u),
        }
    }

    fn v_app_sp(&self, t: Rc<Val>, spine: &Spine) -> Rc<Val> {
        //spine.iter().rev().fold(t, |acc, (u, i)| self.v_app(acc, u.clone(), *i))
        match spine {
            List { head: None, .. } => t,
            a => {
                let (u, i) = a.head().unwrap();
                self.v_app(&self.v_app_sp(t, &a.tail()), u.clone(), *i)
            }
        }
    }

    fn v_app_pruning(&self, env: &Env, v: Rc<Val>, pr: &Pruning) -> Rc<Val> {
        //println!("{} {:?} {:?}", "v_app_bds".green(), v, bds);
        match (env, pr) {
            (List { head: None, .. }, List { head: None, .. }) => v,
            (a, b) if a.head().is_some() && matches!(b.head(), Some(Some(_))) => self.v_app(
                &self.v_app_pruning(&a.tail(), v, &b.tail()),
                a.head().unwrap().clone(),
                b.head().unwrap().unwrap(),
            ),
            (a, b) if a.head().is_some() && matches!(b.head(), Some(None)) => {
                self.v_app_pruning(&a.tail(), v, &b.tail())
            }
            _ => panic!("impossible {v:?}"),
        }
    }

    fn eval(&self, env: &Env, tm: &Rc<Tm>) -> Rc<Val> {
        //println!("{} {:?}", "eval".yellow(), tm);
        match tm.as_ref() {
            Tm::Var(x) => match env.iter().nth(x.0 as usize) {
                Some(v) => v.clone(),
                None => {
                    let v = self.global.get(&Lvl(x.0 - 1919810)).unwrap();
                    if self.neutral_globals.get() {
                        Val::vvar(Lvl(x.0)).into()
                    } else {
                        v.clone()
                    }
                }
            },
            Tm::Obj(tm, name) => {
                let a = self.eval(env, tm);
                let a = self.force(&a);
                match a.as_ref() {
                    Val::Sum(_, params, _, _) => {
                        params.iter()
                            .find(|(f_name, _, _, _)| f_name == name)
                            .unwrap().1.clone()
                    },
                    Val::SumCase { datas, typ, .. } => {
                        (match typ.as_ref() {
                            Val::Sum(_, params, _, _) => params,
                            _ => panic!("impossible {typ:?}"),
                        }).iter()
                            .map(|x| (x.0.clone(), x.1.clone(), x.3))
                            .chain(datas.iter().cloned())
                        //datas.into_iter()
                            .find(|(f_name, _, _)| f_name == name)
                            .unwrap().1.clone()
                    },
                    _ => {
                        Val::Obj(a, name.clone(), List::new()).into()
                    },
                }
            }
            Tm::App(t, u, i) => self.v_app(&self.eval(env, t), self.eval(env, u), *i),
            Tm::Lam(x, i, t) => Val::Lam(x.clone(), *i, Closure(env.clone(), t.clone())).into(),
            Tm::Pi(x, i, a, b) => {
                Val::Pi(x.clone(), *i, self.eval(env, a), Closure(env.clone(), b.clone())).into()
            }
            Tm::Let(_, _, t, u) => {
                let t_val = self.eval(env, t);
                self.eval(&env.prepend(t_val), u)
            }
            Tm::U(x) => Val::U(*x).into(),
            Tm::Meta(m) => self.v_meta(*m),
            Tm::AppPruning(t, pr) => self.v_app_pruning(env, self.eval(env, t), pr),
            Tm::LiteralIntro(x) => Val::LiteralIntro(x.clone()).into(),
            Tm::LiteralType => Val::LiteralType.into(),
            Tm::Prim => {
                // 槽值可能被精化 σ 包裹（subst_cxt 后的臂上下文）——先推开
                // 再判字面量拼接，对齐旧 refresh 重求值后的槽值形态
                let a = self.force(&env.iter().nth(1).unwrap());
                let b = self.force(&env.iter().nth(0).unwrap());
                match (a.as_ref(), b.as_ref()) {
                    (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
                        Val::LiteralIntro(a.clone().map(|x| format!("{x}{}", b.data))).into()
                    }
                    _ => Val::Prim.into(),
                }
            }
            Tm::Sum(name, params, cases, is_trait) => {
                let new_params = params
                    .iter()
                    .map(|x| (x.0.clone(), self.eval(env, &x.1), self.eval(env, &x.2), x.3))
                    .collect();
                Val::Sum(name.clone(), new_params, cases.clone(), *is_trait).into()
            }
            Tm::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => {
                let datas = datas
                    .iter()
                    .map(|p| (p.0.clone(), self.eval(env, &p.1), p.2))
                    .collect();
                let typ = self.eval(env, typ);
                Val::SumCase {
                    is_trait: *is_trait,
                    typ,
                    case_name: case_name.clone(),
                    datas,
                }.into()
            }
            Tm::Match(tm, cases) => {
                let val = self.eval(env, tm);
                let val = self.force(&val);
                match val.as_ref() {
                    Val::SumCase { .. } => {
                        match Compiler::eval_aux(self, &val, env, cases) {
                            Some((tm, env)) => self.eval(&env, &tm),
                            None => Val::Match(val, env.clone(), cases.clone()).into(),
                        }
                    }
                    _ => {
                        Val::Match(val, env.clone(), cases.clone()).into()
                    }
                }
            }
        }
    }

    /// 中性全局视图下的求值（[`Self::neutral_globals`] 的作用域包装）：
    /// 置位 → eval → 恢复旧值（可嵌套）。三处 Match 分支体重求值点共用
    /// （match 合一的臂体 / `rename` 的 Match 臂 / `quote` 的 Match 臂），
    /// 取代旧实现"`self.clone()` 整机深拷 + 就地改写 global 表"。
    fn eval_neutral(&self, env: &Env, tm: &Rc<Tm>) -> Rc<Val> {
        let prev = self.neutral_globals.replace(true);
        let v = self.eval(env, tm);
        self.neutral_globals.set(prev);
        v
    }

    fn quote_sp(&self, l: Lvl, t: Rc<Tm>, spine: &Spine) -> Rc<Tm> {
        /*spine.iter().fold(t, |acc, u| {
            Tm::App(Box::new(acc), Box::new(self.quote(l, u.0.clone())), u.1)
        })*/
        match spine {
            List { head: None, .. } => t,
            _ => {
                let head = spine.head().unwrap();
                Tm::App(self.quote_sp(l, t, &spine.tail()), self.quote(l, &head.0), head.1).into()
            }
        }
    }

    fn quote(&self, l: Lvl, t: &Rc<Val>) -> Rc<Tm> {
        //println!("{} {:?}", "quote".green(), t);
        let t = self.force(t);
        match t.as_ref() {
            // 不变式：force 的返回值顶层不会是 VSub（防御臂；fuel 耗尽时
            // frcs 的降级会留裸 rigid 而非 VSub，故此臂仅在极端角落可达）
            Val::VSub(..) => {
                debug_assert!(false, "quote: VSub survived force");
                Tm::U(0).into()
            }
            Val::Flex(m, sp) => self.quote_sp(l, Tm::Meta(*m).into(), sp),
            Val::Rigid(x, sp) => self.quote_sp(l, Tm::Var(lvl2ix(l, *x)).into(), sp),
            Val::Obj(x, name, sp) => self.quote_sp(l, Tm::Obj(self.quote(l, x), name.clone()).into(), sp),
            Val::Lam(x, i, closure) => Tm::Lam(
                x.clone(),
                *i,
                self.quote(l + 1, &self.closure_apply(closure, Val::vvar(l).into())),
            ).into(),
            Val::Pi(x, i, a, closure) => Tm::Pi(
                x.clone(),
                *i,
                self.quote(l, a),
                self.quote(l + 1, &self.closure_apply(closure, Val::vvar(l).into())),
            ).into(),
            Val::U(x) => Tm::U(*x).into(),
            Val::LiteralIntro(x) => Tm::LiteralIntro(x.clone()).into(),
            Val::LiteralType => Tm::LiteralType.into(),
            Val::Prim => Tm::Prim.into(),
            Val::Sum(name, params, cases, is_trait) => {
                let new_params = params.iter()
                    .map(|x| {
                        (x.0.clone(), self.quote(l, &x.1), self.quote(l, &x.2), x.3)
                    })
                    .collect();
                Tm::Sum(name.clone(), new_params, cases.clone(), *is_trait).into()
            }
            Val::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => {
                let datas = datas
                    .iter()
                    .map(|p| {
                        (p.0.clone(), self.quote(l, &p.1), p.2)
                    })
                    .collect();
                Tm::SumCase {
                    is_trait: *is_trait,
                    typ: self.quote(l, typ),
                    case_name: case_name.clone(),
                    datas,
                }.into()
            }
            Val::Match(val, env, cases) => {
                /*TODO:let tm_cases = cases
                    .into_iter()
                    .map(|(p, clos)| {
                        let binders_count = p.count_binders();
                        let body_tm = self.quote(l + binders_count, self.closure_apply_pats(&clos, l, &p));
                        (p, body_tm)
                    })
                    .collect();*/
                let tm_cases = cases
                    .iter()
                    .map(|x| (
                        x.0.clone(),
                        {
                            let env = (0..x.0.bind_count())
                                .fold(env.clone(), |env, x| env.prepend(Val::vvar(l + x).into()));
                            // 分支体在中性全局视图下重求值（全局名字不再展开，
                            // 免递归）——`eval_neutral` 取代旧的整机克隆
                            let tm = self.eval_neutral(&env, &x.1);
                            self.quote(l+x.0.bind_count(), &tm)
                        }
                    ))
                    .collect();
                Tm::Match(self.quote(l, val), tm_cases).into()
            }
        }
    }

    pub fn nf(&self, env: &Env, t: &Rc<Tm>) -> Rc<Tm> {
        // quote → eval 会 force；一次 nf 充值 fuel 防循环解（L08 同款）
        self.refuel();
        let l = Lvl(env.iter().count() as u32);
        self.quote(l, &self.eval(env, t))
    }

    fn close_val(&self, cxt: &Cxt, t: &Rc<Val>) -> Closure {
        Closure(cxt.env.clone(), self.quote(cxt.lvl + 1, t))
    }

    fn unify_catch(&mut self, cxt: &Cxt, t: &Rc<Val>, t_prime: &Rc<Val>, span: Span<()>) -> Result<(), Error> {
        self.unify_catch_at(cxt.lvl, cxt, t, t_prime, span)
    }

    /// `unify_catch` 的显式层级版（L07 的显式 lvl 穿参同款）：可达性探测
    /// 的构造子绑定器以**超出上下文的 scratch 层级**实例化（嵌套位置的延迟
    /// 探测还落在臂内全部真槽之外）——η/Π 展开的 binder 层级必须随之抬高，
    /// 否则会与真槽撞号。
    fn unify_catch_at(&mut self, l: Lvl, cxt: &Cxt, t: &Rc<Val>, t_prime: &Rc<Val>, span: Span<()>) -> Result<(), Error> {
        self.refuel();
        self.unify(l, cxt, t, t_prime)
            .map_err(|e| {
                /*Error::CantUnify(
                    cxt.clone(),
                    self.quote(cxt.lvl, t),
                    self.quote(cxt.lvl, t_prime),
                )*/
                //println!("{:?} == {:?}", t, t_prime);
                //println!("{:?}", self.eval(&cxt.env, self.quote(cxt.lvl, t_prime.clone())));
                /*panic!(
                    //"can't unify {:?} == {:?}",
                    "can't unify\n      find: {}\n  expected: {}",
                    pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, t)),
                    pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, t_prime)),
                );*/
                let err = match e {
                    UnifyError::Basic => format!(
                        //"can't unify {:?} == {:?}",
                        "can't unify\n  expected: {}\n      find: {}",
                        pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, t)),
                        pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, t_prime)),
                    ),
                    UnifyError::Trait(e) => e,
                };
                Error(span.map(|_| err.clone()))
                //Error(format!("can't unify {:?} == {:?}", t, t_prime))
            })
    }
}

#[allow(unused)]
pub fn run(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let (ast, parse_errs) = parser::parser(&preprocess(input), path_id).unwrap();
    for e in parse_errs {
        println!("{:?}", e);
    }
    let mut cxt = Cxt::new();
    let mut ret = String::new();
    for tm in ast {
        match &tm {
            parser::syntax::Decl::Def { name, .. }
            | parser::syntax::Decl::Enum { name, .. }
            | parser::syntax::Decl::TraitDecl { name, .. } => {
                println!("> {}", name.data);
                //cxt.print_env(&infer);
            },
            parser::syntax::Decl::Println(raw) => {},
            parser::syntax::Decl::ImplDecl { .. } => {
                println!("> impl");
            }
        }
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(x) = x {
            //ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += &pretty::pretty_tm(0, cxt.names(), &infer.nf(&cxt.env, &x));
            ret += "\n";
        }
    }
    /*cxt.env
        .iter()
        .zip(cxt.names().iter())
        .for_each(|(ty, name)| {
            println!("{}: {}", name, pretty::pretty_tm(0, cxt.names(), &infer.quote(cxt.lvl, ty.clone())));
            //println!("{:?}\n", ty);
        });*/
    Ok(ret)
}

/// 参考版项的节点数（与性能版 `tm_size` 同口径）。
fn tm_size_ref(t: &Tm) -> u64 {
    let mut stack: Vec<&Tm> = vec![t];
    let mut n = 0u64;
    while let Some(x) = stack.pop() {
        n += 1;
        match x {
            Tm::Var(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_)
            | Tm::Prim => {}
            Tm::Obj(h, _) => stack.push(h),
            Tm::Lam(_, _, b) => stack.push(b),
            Tm::App(f, a, _) => {
                stack.push(f);
                stack.push(a);
            }
            Tm::AppPruning(h, pr) => {
                stack.push(h);
                n += pr.len() as u64;
            }
            Tm::Pi(_, _, a, b) => {
                stack.push(a);
                stack.push(b);
            }
            Tm::Let(_, a, t, u) => {
                stack.push(a);
                stack.push(t);
                stack.push(u);
            }
            Tm::Sum(_, params, ..) => {
                for (_, v, ty, _) in params {
                    stack.push(v);
                    stack.push(ty);
                }
            }
            Tm::SumCase { typ, datas, .. } => {
                stack.push(typ);
                for (_, v, _) in datas {
                    stack.push(v);
                }
            }
            Tm::Match(s, cases) => {
                stack.push(s);
                for (p, b) in cases {
                    n += p.bind_count() as u64;
                    stack.push(b);
                }
            }
        }
    }
    n
}

/// 参考版基准口径：elaborate 全部 decl，返回是否通过。
pub(crate) fn bench_check(decls: &[parser::syntax::Decl]) -> bool {
    let mut infer = Infer::new();
    let mut cxt = Cxt::new();
    for d in decls {
        match infer.infer(&cxt, d.clone()) {
            Ok((_, _, nc)) => cxt = nc,
            Err(_) => return false,
        }
    }
    true
}

/// 参考版基准口径：check + nf——取**最后一个 def** 的登记值（define 链的
/// env 槽顶）空层级引读并数节点（深 Box 树的递归析构会爆栈，`mem::forget`）。
pub(crate) fn bench_check_nf(decls: &[parser::syntax::Decl]) -> u64 {
    let mut infer = Infer::new();
    let mut cxt = Cxt::new();
    let mut last: Option<Rc<Val>> = None;
    for d in decls {
        let is_def = matches!(d, parser::syntax::Decl::Def { .. });
        match infer.infer(&cxt, d.clone()) {
            Ok((_, _, nc)) => cxt = nc,
            Err(_) => return 0,
        }
        if is_def {
            last = cxt.env.head().cloned();
        }
    }
    let Some(v) = last else { return 0 };
    let q = infer.quote(Lvl(0), &v);
    let n = tm_size_ref(&q);
    std::mem::forget(q);
    n
}

pub fn preprocess(s: &str) -> String {
    let s = s.split("/*")
        .map(|x| {
            x.split_once("*/")
                .map(|(a, b)| a.replace(|c: char| !c.is_whitespace(), " ") + "  " + b)
                .unwrap_or(x.to_owned())
        })
        .reduce(|a, b| a + "  " + &b)
        .unwrap_or(s.to_owned());
    s.lines()
        .map(|x| {
            x.split_once("//")
                .map(|(a, b)| a.to_owned() + "  " + &b.replace(|c: char| !c.is_whitespace(), " "))
                .unwrap_or(x.to_owned())
        })
        .reduce(|a, b| a + "\n" + &b)
        .unwrap_or(s.to_owned())
}

#[test]
fn test_trait() {
    let input = r#"
def outParam[A](a: A): A = a

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

impl List[Nat] {
    def map1(f: Nat -> Bool): List[Bool] =
        match this {
            case nil => nil
            case cons(head, tail) => cons (f head) (tail.map1 f)
        }
}

def listmap[T, U](xs: List[T], f: T -> U): List[U] =
    match xs {
        case nil => nil
        case cons(head, tail) => cons (f head) (listmap tail f)
    }

impl[T] List[T] {
    def map[U](f: T -> U): List[U] =
        listmap this f
}

def two = succ (succ zero)

def listnat = cons two (cons (succ zero) nil)

def listnat2 = listnat.map (x => succ x)

println listnat2

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println (not true)

trait ToString {
    def to_string: String
}

impl ToString for Bool {
    def to_string: String =
        match this {
            case true => "true"
            case false => "false"
        }
}

def t[T][s: ToString[T]](x: T): String =
    s.to_string x

println (t true)

trait Say {
    def say(x: Nat): String
}

impl[T] Say for T {
    def say(x: Nat): String = "hello"
}

println (zero.say zero)

trait Add[T, O: outParam(Type 0)] {
    def add(that: T): O
}

def nat_add_helper(x: Nat, y: Nat): Nat =
    match y {
        case zero => x
        case succ(n) => succ (nat_add_helper x n)
    }

impl Add[Nat, Nat] for Nat {
    def add(that: Nat): Nat =
        nat_add_helper this that
}

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => y.add (mul n y)
}

def four = two.add two

println four

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]): T = p.x

impl Add[Point[Nat], Point[Nat]] for Point[Nat] {
    def add(that: Point[Nat]): Point[Nat] =
        new Point(this.x.add that.x, this.y.add that.y)
}

impl Add[Nat, Point[Nat]] for Point[Nat] {
    def add(that: Nat): Point[Nat] =
        new Point(this.x.add that, this.y.add that)
}

def start_point = new Point(zero, four)

def end_point = new Point(four, two)

println (get_x start_point)

println (start_point.add end_point)

def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(a: A)
    case2(a: test1)
}

def test2: HighLvl[Nat] = case1 zero

def test3: Type 2 = HighLvl[Nat]

enum HighLvl2[A: Type 2] {
    case2_1(x: A)
    case2_2(x: Nat)
}

def test1_2: HighLvl2[HighLvl[Nat]] = case2_1 test2

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

enum HighLvl3[A: Type 2] {
    case3_1
    case3_2(x: Nat)
}

def test2_2: HighLvl3[HighLvl[Nat]] = case3_1

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]

def Eq[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y

def refl[A, x: A]: Eq[A] x x = _ => px => px

struct Bits {
    name: String
    size: Nat
}

def get_name(x: Bits) = x.name

def assign(a: Bits, b: Bits)(eq: Eq[Nat] a.size b.size): String = a.name

def sigA = new Bits("A", four)

def sigB = new Bits("B", four)

def sigC = new Bits("C", two)

def sigD = new Bits("D", two)

def ab = assign sigA sigB refl

def cd = assign sigC sigD refl

"#;
    println!("{}", run(input, 0).unwrap());
}

#[test]
fn test5() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =
    match x {
        case nil => cons zero nil
        case cons(x, xs) => match y {
            case cons(y, ys) => cons x (t xs ys)
        }
    }
"#;
    println!("{}", run(input, 0).unwrap());
}

#[test]
fn test6() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =
    match x {
        case nil => cons zero nil
        case cons(x, xs) => match y {
            case cons(y, ys) => match t xs ys {
                case cons(z, zs) => cons zero (cons zero zs)
            }
        }
    }
"#;
    println!("{}", run(input, 0).unwrap());
}

#[test]
fn test4() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) =
    match x {
        case zero => zero
        case succ(n) => add y (mul n y)
    }

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def rfl[A][a: A]: Eq a a =
    refl a

def cong[A, B, f: A -> B, x: A, y: A](e: Eq x y): Eq (f x) (f y) =
    match e {
        case refl(a) => refl (f a)
    }

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def add_zero_right(a: Nat): Eq (add a zero) a =
    match a {
        case zero => refl zero
        case succ(t) => cong_succ (add_zero_right t)
    }

def symm[A, x, y: A](e: Eq[A] x y): Eq[A] y x =
    match e {
        case refl(a) => refl[A] a
    }

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }

def add_succ_right (n: Nat, m: Nat): Eq[Nat] (add n (succ m)) (succ (add n m)) =
    match n {
        case zero => refl[Nat] (succ m)
        case succ(k) => cong_succ (add_succ_right k m)
    }

def add_comm (n: Nat, m: Nat): Eq[Nat] (add n m) (add m n) =
    match n {
        case zero => symm (add_zero_right m)
        case succ(k) => trans (cong_succ (add_comm k m)) (symm (add_succ_right m k))
    }

def add_assoc (n: Nat, m: Nat, k: Nat): Eq[Nat] (add (add n m) k) (add n (add m k)) =
    match n {
        case zero => rfl
        case succ(l) => cong_succ (add_assoc l m k)
    }

"#;
    println!("{}", run(input, 0).unwrap());
    println!("success");
}

#[test]
fn test2() {
    let input = r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def listid(x: List[Bool]): List[Bool] = x

def create0: List[Bool] = nil

def create1: List[Bool] = cons true nil

def create2: List[Bool] = cons true (cons false nil)

def two = succ (succ zero)

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println (not true)

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => add y (mul n y)
}

def four = add two two

println four

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]): T = p.x

def point_add(p1: Point[Nat], p2: Point[Nat]): Point[Nat] =
    new Point((add p1.x p2.x), (add p1.y p2.y))

def start_point = new Point(zero, four)

def end_point = new Point(four, two)

println (get_x start_point)

println (point_add start_point end_point)

def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(a: A)
    case2(a: test1)
}

def test2: HighLvl[Nat] = case1 zero

def test3: Type 2 = HighLvl[Nat]

enum HighLvl2[A: Type 2] {
    case2_1(x: A)
    case2_2(x: Nat)
}

def test1_2: HighLvl2[HighLvl[Nat]] = case2_1 test2

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

enum HighLvl3[A: Type 2] {
    case3_1
    case3_2(x: Nat)
}

def test2_2: HighLvl3[HighLvl[Nat]] = case3_1

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]

def Eq[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y

def refl[A, x: A]: Eq[A] x x = _ => px => px

struct Bits {
    name: String
    size: Nat
}

def get_name(x: Bits) = x.name

def assign(a: Bits, b: Bits)(eq: Eq[Nat] a.size b.size): String = a.name

def sigA = new Bits("A", four)

def sigB = new Bits("B", four)

def sigC = new Bits("C", two)

def sigD = new Bits("D", two)

def ab = assign sigA sigB refl

def cd = assign sigC sigD refl

"#;
    println!("{}", run(input, 0).unwrap());
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def test1: Type 2 = Type 1 -> Type 0

struct HighLvl[A] {
    case1: A
    case2: test1
}

def test2_t: Type 1 -> Type 0 = t => Nat

def test2: HighLvl[Nat] = new HighLvl(zero, test2_t)

def test3: Type 2 = HighLvl[Nat]

struct HighLvl2[A: Type 2] {
    case2_1: A
    case2_2: Nat
}

def test1_2: HighLvl2[HighLvl[Nat]] = new HighLvl2(test2, zero)

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

struct HighLvl3[A: Type 2] {
    case3_1: Nat
    case3_2: Nat
}

def test2_2: HighLvl3[HighLvl[Nat]] = new HighLvl3(zero, zero)

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]
"#;
    println!("{}", run(input, 0).unwrap());
    println!("success");
}

#[test]
fn test0() {
    let input = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Product[A, B] {
    product(a: A, b: B)
}

def half_adder(lhs: Bool, rhs: Bool): Product[Bool][Bool] =
    match lhs {
        case false => product false rhs
        case true => match rhs {
            case false => product false true
            case true => product true false
        }
    }

def full_adder(lhs: Bool, rhs: Bool, carrier: Bool): Product[Bool][Bool] =
    match lhs {
        case false => half_adder rhs carrier
        case true => match rhs {
            case false => half_adder true carrier
            case true => product true carrier
        }
    }

def bits_adder_carrier[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len, carrier: Bool): Vec[Bool] (succ len) =
    match lhs {
        case nil => cons carrier nil
        case cons(n, taill) => match rhs {
            case cons(m, tailr) => match bits_adder_carrier taill tailr carrier {
                case cons(c, tail) => match full_adder n m c {
                    case product(a, b) => cons a (cons b tail)
                }
            }
        }
    }

def bits_adder[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len): Vec[Bool] (succ len) =
    bits_adder_carrier lhs rhs false

println bits_adder (cons true nil) (cons false nil)
"#;
    println!("{}", run(input, 0).unwrap());
}

#[test]
pub fn test_index() {
    let input = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

def three = succ (succ (succ zero))

def test: Eq two two = refl

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t = cons zero (cons two (cons three (cons two nil)))

println t.len

def head[T, L: Nat](x: Vec[T] (succ L)): T =
    match x {
        case cons(x, _) => x
    }

println (head (cons zero nil))

def length[T, l: Nat](x: (Vec[T] l)): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (xs.len)
    }

    "#;
    println!("{}", run(input, 0).unwrap());
}

#[test]
fn test7() {
    let input = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Product[A, B] {
    product(a: A, b: B)
}

def half_adder(lhs: Bool, rhs: Bool): Product[Bool][Bool] =
    match lhs {
        case false => product false rhs
        case true => match rhs {
            case false => product false true
            case true => product true false
        }
    }

def full_adder(lhs: Bool, rhs: Bool, carrier: Bool): Product[Bool][Bool] =
    match lhs {
        case false => half_adder rhs carrier
        case true => match rhs {
            case false => half_adder true carrier
            case true => product true carrier
        }
    }

def bits_adder_carrier[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len, carrier: Bool): Vec[Bool] (succ len) =
    match lhs {
        case nil => cons carrier nil
        case cons[_](n, taill) => match rhs {
            case cons[_](m, tailr) => match bits_adder_carrier taill tailr carrier {
                case cons[_](c, tail) => match full_adder n m c {
                    case product(a, b) => cons a (cons b tail)
                }
            }
        }
    }

def bits_adder[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len): Vec[Bool] (succ len) =
    bits_adder_carrier lhs rhs false

println bits_adder (cons true nil) (cons false nil)"#;
    println!("{}", run(input, 0).unwrap());
}

pub fn run1(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let (ast, parse_errs) = parser::parser(input, path_id).unwrap();
    for e in parse_errs {
        println!("{:?}", e);
    }
    let mut cxt = Cxt::new();
    let mut ret = String::new();
    for tm in ast {
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(x) = x {
            ret += &format!("{:?}", infer.nf(&cxt.env, &x));
            ret += "\n";
        }
    }
    println!("{:?}", cxt);
    Ok(ret)
}

#[test]
fn test1() {
    let input = r#"
def str_id(x: String, y: String): String = "builtin"

"#;
    println!("{}", run1(input, 0).unwrap());
    let input = r#"
def str_id(x: String, y: String): String = x

"#;
    println!("{}", run1(input, 0).unwrap());
    let input = r#"
def str_id: String = string_concat "hello " "world"

println str_id

"#;
    println!("{}", run1(input, 0).unwrap());
    println!("success");
}

// --------------------------------------------------------------------------------
// 2026-09-18 评审回归钉（L07 修复轮移植）：嵌套模式覆盖检查 / 构造子良构性。
// 文案与 L07 同款；孪生版同款钉在 tests/l10_fast_parity.rs 的
// parity_review_fixes_2026_09_18 / fast_substv_reclaimed_across_rounds。

fn check_err(input: &str) -> String {
    run(input, 0).unwrap_err().0.data
}

/// P0（嵌套覆盖缺失）：nil 臂 + cons(h, nil) 臂缺 cons(h, cons(..))——
/// 修复前静默接受、运行期在尾部为 cons 的值上卡住；修复后报模式位置缺失。
#[test]
fn test_nested_coverage_gap() {
    let msg = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def f(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => h
    }
"#,
    );
    assert!(msg.contains("缺少构造子 cons"), "{msg}");
}

/// P0（嵌套覆盖缺失，三层）：深度 2 的嵌套位置缺 cons。
#[test]
fn test_nested_coverage_gap3() {
    let msg = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def f(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => h
        case cons(h, cons(h2, nil)) => h2
    }
"#,
    );
    assert!(msg.contains("缺少构造子 cons"), "{msg}");
}

/// P0 正向对照：嵌套覆盖完备的 match 通过并正确求值（防误报钉）。
#[test]
fn test_nested_coverage_complete() {
    let out = run(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def f(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => h
        case cons(h, cons(h2, t)) => h2
    }

println (f (cons zero (cons (succ zero) nil)))
"#,
        0,
    )
    .unwrap();
    assert!(out.contains("succ"), "{out}");
}

/// P0 正向对照（索引精化）：Vec 长度恰 2 上 nil 臂特化失败静默跳过（L10
/// 的荒谬臂收窄语义），尾部（长度 1）上 nil 不可达不触发嵌套误报。
#[test]
fn test_nested_refine_absurd_ok() {
    let out = run(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def f(v: Vec[Nat] (succ (succ zero))): Nat =
    match v {
        case nil => zero
        case cons(h, nil) => h
        case cons(h, cons(h2, t)) => h2
    }

println (f (cons zero (cons zero nil)))
"#,
        0,
    )
    .unwrap();
    assert!(out.contains("zero"), "{out}");
}

/// P1（构造子良构性）：ret 不是本 enum——c -> Nat 向构造子名字空间注入
/// phantom 值（对 Nat 的覆盖完备 match 在该值上卡死），修复后注册期拒绝。
#[test]
fn test_ctor_wf_external_ret() {
    let msg = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Foo {
    c -> Nat
}
"#,
    );
    assert!(msg.contains("不是 Foo"), "{msg}");
}

/// P1（构造子良构性）：参数位特化——隐式参数位是 Bool 而非参数变量，
/// 修复后拒绝（特化请走显式索引）。
#[test]
fn test_ctor_wf_param_specialized() {
    let msg = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Foo[A] {
    c -> Foo[Bool]
}
"#,
    );
    assert!(msg.contains("参数变量"), "{msg}");
}

/// P1 正向对照（构造子重绑定参数惯用法）：`p[A,B](a,b) -> Pack[A][B] a b`
/// 合法——WF 检查不得误伤（v3_multi_index_gadt 同款语义）。
#[test]
fn test_ctor_wf_rebind_params_ok() {
    let out = run(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Pack[A, B](x: A, y: B) {
    p[A, B](a: A, b: B) -> Pack[A][B] a b
}

def sw: Pack[Nat][Bool] zero true = p[Nat][Bool] zero true

println sw.y
"#,
        0,
    )
    .unwrap();
    assert!(out.contains("true"), "{out}");
}

// --------------------------------------------------------------------------------
// 2026-09-20 负例补齐（模式匹配「应当失败」）。
//
// 本层此前只有嵌套位置（test_nested_coverage_gap*）的负例，顶层缺分支与
// 臂不可达两处覆盖义务没有钉子。两者各钉一条，末条是防误报的正向对照。
// 警告经 `elaboration.rs:313` 的 `format!("{error:?}")` 落到 `Error.0.data`，
// 故断言按 Debug 变体名（与 L09/L11/L12 同形）。

/// 负例：顶层缺构造子（Bool 少了 false 臂）必须报错，不得静默接受。
#[test]
fn test_pm_missing_branch_rejected() {
    let msg = check_err(
        r#"
enum Bool {
    true
    false
}

def bad(x: Bool): Bool =
    match x {
        case true => false
    }
"#,
    );
    assert!(
        msg.contains("Unmatched") || msg.contains("not covered") || msg.contains("缺少构造子"),
        "错误文案不含缺分支信息：{msg}"
    );
}

/// 负例：臂不可达（`Vec[Nat] zero` 上 cons 臂的索引方程无解）。
/// 本层是"特化失败 = 臂静默跳过"（与 L11/L12 同款，非 L07 的报"分支
/// 不可达"），故钉的是"整个 match 必须被拒"。
#[test]
fn test_pm_unreachable_arm_rejected() {
    let msg = check_err(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def bad(v: Vec[Nat] zero): Nat =
    match v {
        case cons(x, xs) => x
    }
"#,
    );
    assert!(
        msg.contains("Unmatched") || msg.contains("Unreachable")
            || msg.contains("缺少构造子") || msg.contains("不可达"),
        "错误文案不含拒因信息：{msg}"
    );
}

/// 正向对照（防误报）：通配臂覆盖全部 → 不得报覆盖类错误。
#[test]
fn test_pm_wildcard_covers_ok() {
    let out = run(
        r#"
enum Bool {
    true
    false
}

def ok(x: Bool): Bool =
    match x {
        case true => false
        case _ => true
    }
"#,
        0,
    )
    .unwrap_or_else(|e| panic!("通配臂被误报：{}", e.0.data));
    assert!(!out.contains("非穷尽"), "{out}");
}

// --------------------------------------------------------------------------------
// 2026-09-20 跨层一致性钉子：通配臂之后的臂。
//
// L07 的 README §4（`src/L07_sum_type/README.md:264`）是这条语义的规格：
// 「通配臂之后的臂跳过（运行时永不可达，保持首匹配语义**不报错**）」，
// 且 L07/L08 各有回归钉 `test_catch_all_mixed` 断言这种程序**通过**。
//
// 本层（及 L09/L11/L12）在 `pattern_match.rs` 的臂循环里对被遮蔽的臂推
// `Warning::Unreachable`，而本层把非空 warnings 直接变成 `Err`
// （`elaboration.rs:313`）——于是同一份源在 L07/L08 通过、在本层被拒。
// 该 `Warning::Unreachable` 是决策树时代的残留（老算法里"树从未到达的臂"
// 是另一回事，见 docs/l09l13-match-compiler-analysis-2026-09-17.md §2；
// 改成逐臂下钻后只剩"被 catch-all 遮蔽"这一种情形，而它恰是规格要求不报的）。
/// 2026-09-20 owner 口径更正：**不可达的臂应当报错**（上一轮曾按 L07
/// README:264 对齐成沉默跳过，本轮已还原为报错）。
#[test]
fn test_pm_shadowed_arm_after_catch_all_rejected() {
    match run(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def const_zero(x: Nat): Nat =
    match x {
        case n => zero
        case zero => zero
        case succ(k) => succ k
    }
"#,
        0,
    ) {
        Err(e) => assert!(
            e.0.data.contains("Unreachable") || e.0.data.contains("不可达"),
            "错误文案不含臂不可达信息：{}", e.0.data
        ),
        Ok(out) => panic!("通配臂之后的臂（运行时永不可达）被静默接受：\n{out}"),
    }
}
