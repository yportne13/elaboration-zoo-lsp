//! L06 核心机（eval / quote / unify / force / rename / solve / prune / check /
//! infer / decl 表 / builtin prim）的极致性能版：L05 冠军配方
//! （`bump_spine_iter`）向 string 层的移植。继承 L05 的全部机制（见其模块
//! 注释与 readme）：
//!
//! 1. bump arena；打包值 [`V`]（低 3 位 tag）；扁平中性 + spine 栈；
//! 2. 复合环境（平坦 def 区域 + 持久 binder 链）；
//! 3. 迭代内核：eval 双栈 / quote 任务栈 / unify 工作表 / rename 任务栈 /
//!    force 循环；
//! 5. quote 记忆化（默认口径）+ unify 判等记忆化（`L06_NO_CONV_MEMO=1`
//!    消融）+ O(1) 名字解析（`L06_NO_NAME_MAP=1` 消融）；
//! 6. `Tycker` 稳态复用（跨轮 `Bump::reset`）、热路径草稿常驻、
//!    `Pruning` 跳段（none-run）、`RenBuf` 换代缓冲、fresh meta 免 eval
//!    快捷路径。
//!
//! L06 的增量（string 层语义的落地）：
//!
//! - **值编码**：tag 6 = `LiteralType` 立即数（`V(6)`，同 U）；tag 7 = 指向
//!   [`XCell`]（`Lit(&str)` / `Decl(&str)`）的指针。字面量值惰性无害（quote
//!   /rename 直出）；Decl 既是卡住的按名头（求值 miss decl 表时现造单元），
//!   也是 builtin 的触发载体。
//! - **builtin prim 的增量触发**：参考版 `v_app` 的 Decl 臂——每次对 Decl 头
//!   的应用都把**全条**累积实参交给 prim（自然序），`None`（元数不足 / 实参
//!   非字面量）保持卡住。快版把该臂集中到 [`decl_apply`]，所有应用点
//!   （eval 的 Apply/ChainWrap/AppPrunOne、force 的解值应用、unify 的 η 臂、
//!   prim 的 `change_mutable`）经 [`is_declheaded`] O(1) 判定后走它。判定靠
//!   [`Entry::decl`] 标志（push 时随函数侧传播），不 walks 链。
//! - **decl 表 + 可变全局**：`Machine.decls`（名 → 值/类型/prim）与
//!   `Machine.mutable_map`（RefCell，名 → 值）随轮清空并重新注册（参考版
//!   每次调用新建 `Infer` 的稳态等价）。
//! - **unify 的 L06 臂**：`(6,6)`、`(6,7Decl)`、`(7Decl,6)` 成立；
//!   同名 `(7Decl,7Decl)` 逐实参；`(7Lit,7Lit)` **恒败**（参考版无该臂，
//!   连相同字面量也不可合一——位相等捷径对 tag 7 关闭以复刻之，内联环的
//!   实参位相等跳过与 intersect 回落同理加 tag 7 守卫）。Span 的
//!   PartialEq 只比 data（parser_lib.rs 自定义实现），同名 Decl 头按名
//!   比较、命名 λ 按名匹配 Π——与参考版一致。
//!
//! 与参考版（`super`，分文件：elaboration/cxt/unification/syntax/pretty）
//! 共用 parser / pretty / preprocess，**Ok 输出逐字节一致**（互检测试 +
//! `tests/l06_blackbox.rs`）。已知偏差（仅错误消息内容，不影响判定与
//! Ok 输出）：参考版错误文案 `{:?}` 直接 Debug 打印引读项 / 名字 Span，
//! 携带源码偏移；快版项不存偏移（导出 span 全零），同构但数字不同。判定
//! （Err/Ok）与 println 输出不受影响。

use bumpalo::Bump;
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;
use std::cell::RefCell;

use super::parser::syntax::{Decl, Either, Icit, Raw};
use super::{empty_span, pretty, Error, Ix, Tm as CTm};

// syntax（bump 内的项表示）
// --------------------------------------------------------------------------------

/// bump 内分配的核心项。名字只服务 pretty（`Var` 无名，索引寻址）。
/// `AppPruning` 是洞形态：头（实践中恒为 `Meta`）+ scope 掩码。
/// L06 增量：`LiteralType` / `LiteralIntro` / `Decl`（按名查 decl 表）。
pub(crate) enum Tm<'a> {
    Var(u32),
    Lam(&'a str, Icit, &'a Tm<'a>),
    App(&'a Tm<'a>, &'a Tm<'a>, Icit),
    /// 把头按掩码应用到求值环境：`Some(icit)` 槽位以该 icit 应用实参，
    /// `None` 槽位跳过。
    AppPruning(&'a Tm<'a>, Option<&'a PrCons<'a>>),
    U,
    Pi(&'a str, Icit, &'a Tm<'a>, &'a Tm<'a>),
    Let(&'a str, &'a Tm<'a>, &'a Tm<'a>, &'a Tm<'a>),
    Meta(u32),
    /// String 字面量的类型（`String`）。
    LiteralType,
    /// 字符串字面量（内容即值）。
    LiteralIntro(&'a str),
    /// 按名 decl 表查找：求值命中给登记值，miss 保持卡住的 Decl 头。
    Decl(&'a str),
}

/// `AppPruning` 的掩码链表（bump 持久，头 = 最内层绑定）。
pub(crate) struct PrCons<'a> {
    /// `Some(icit)` = 绑定槽位（应用实参，icit 随槽）；`None` = define 槽
    /// （跳过）。
    slot: Option<Icit>,
    /// 本节点向外（next 方向）连续 `None`（define 槽）的个数；Some 槽为 0。
    none_run: u32,
    /// 本 none-run 之后的第一个槽（Some 槽或链尾）——跳段的落点。
    after_run: Option<&'a PrCons<'a>>,
    next: Option<&'a PrCons<'a>>,
}

impl<'a> PrCons<'a> {
    /// 入链构造（新槽恒为链头，最内层）。run 统计只读既有节点。
    fn new(slot: Option<Icit>, next: Option<&'a PrCons<'a>>) -> Self {
        let (none_run, after_run) = match (slot, next) {
            (Some(_), _) => (0, next),
            (None, Some(n)) if n.slot.is_none() => (n.none_run + 1, n.after_run),
            (None, _) => (1, next),
        };
        PrCons {
            slot,
            none_run,
            after_run,
            next,
        }
    }
}

/// 局部 telescope 节点（`fresh_meta` 闭类型用）：`Bind` 槽存引好的类型项，
/// `Define` 槽再存定义项。
struct LCons<'a> {
    name: &'a str,
    a_t: &'a Tm<'a>,
    /// `Some` = define（闭成 Let），`None` = binder（闭成显式 Π）。
    t_t: Option<&'a Tm<'a>>,
    next: Option<&'a LCons<'a>>,
}

// values（打包值）
// --------------------------------------------------------------------------------

/// 打包值：tag 在低 3 位。`0=Lvl(level<<3)`、`1=Clo(ptr|1)`、
/// `2=Spine(idx<<3|2)`、`3=U`（立即数）、`4=Pi(ptr|4)`、`5=Meta(m<<3|5)`
/// （未解 meta 立即数）、`6=LiteralType`（立即数，L06）、`7=XCell(ptr|7)`
/// （字面量或 Decl 头，L06）。icit 不进打包字——由 Clo/Pi 单元与 spine 槽
/// 携带（打包字是 quote/unify 记忆化的键，icit 随值结构唯一确定）。
#[derive(Clone, Copy)]
pub(crate) struct V(pub(crate) u64);

#[inline]
pub(crate) fn v_lvl(level: u32) -> V {
    V(((level as u64) << 3) | 0)
}
#[inline]
pub(crate) fn v_clo<'a>(p: &'a CloCell<'a>) -> V {
    V((p as *const _ as u64) | 1)
}
#[inline]
pub(crate) fn v_spine(idx: usize) -> V {
    V(((idx as u64) << 3) | 2)
}
#[inline]
pub(crate) fn v_u() -> V {
    V(3)
}
#[inline]
pub(crate) fn v_pi<'a>(p: &'a PiCell<'a>) -> V {
    V((p as *const _ as u64) | 4)
}
#[inline]
pub(crate) fn v_meta(m: u32) -> V {
    V(((m as u64) << 3) | 5)
}
/// `LiteralType` 立即数（同 `U` 的编码方式：tag 本身即值）。
#[inline]
pub(crate) fn v_lit_ty() -> V {
    V(6)
}
#[inline]
pub(crate) fn v_xcell<'a>(p: &'a XCell<'a>) -> V {
    V((p as *const _ as u64) | 7)
}
#[inline]
pub(crate) fn v_tag(v: V) -> u64 {
    v.0 & 7
}
#[inline]
pub(crate) fn v_lvl_of(v: V) -> u32 {
    (v.0 >> 3) as u32
}
#[inline]
pub(crate) fn v_clo_of<'a>(v: V) -> &'a CloCell<'a> {
    unsafe { &*((v.0 & !7) as *const CloCell) }
}
#[inline]
pub(crate) fn v_spine_of(v: V) -> usize {
    (v.0 >> 3) as usize
}
#[inline]
pub(crate) fn v_pi_of<'a>(v: V) -> &'a PiCell<'a> {
    unsafe { &*((v.0 & !7) as *const PiCell) }
}
#[inline]
pub(crate) fn v_meta_of(v: V) -> u32 {
    (v.0 >> 3) as u32
}
/// tag 7 单元解引用（bump 内分配，本轮内有效）。
#[inline]
pub(crate) fn v_xcell_of<'a>(v: V) -> &'a XCell<'a> {
    unsafe { &*((v.0 & !7) as *const XCell) }
}

/// tag 7 的两种载体：字符串字面量（惰性无害值）与卡住的按名 Decl 头。
/// 名字内容只在 pretty / prim 里用；判等按单元指针（同内容不同次求值
/// 各造单元——与参考版每次 `Rc::new` 同构）。
pub(crate) enum XCell<'a> {
    Lit(&'a str),
    Decl(&'a str),
}

/// 复合环境：**平坦 def 区域**（elaborator 的 define 链，指入每轮
/// [`Machine::defs`]；tip 环境原地追加，`nth` O(1)；**非 tip 环境**
/// （λ 体内的 define 先占位后、外层再 define）回落到 binder 链——索引
/// 语义一致，仅查链 O(链深)）+ **持久 binder 链表**。机制与论证同 L03-L05。
#[derive(Clone, Copy)]
pub(crate) struct Env<'a> {
    flat_base: u32,
    flat_len: u32,
    binds: Option<&'a EnvCons<'a>>,
}

const EMPTY_ENV: Env<'static> = Env {
    flat_base: 0,
    flat_len: 0,
    binds: None,
};

/// 环境链表节点（bump 内持久链表，头 = 最内层绑定）。
pub(crate) struct EnvCons<'a> {
    val: V,
    next: Option<&'a EnvCons<'a>>,
}

/// `i < binds 深度` → 走链；否则读平坦 def 区域。
#[inline]
pub(crate) fn env_nth(defs: &[V], env: Env<'_>, i: u32) -> V {
    let mut nb = env.binds;
    let mut j = 0u32;
    while let Some(e) = nb {
        if j == i {
            return e.val;
        }
        j += 1;
        nb = e.next;
    }
    defs[(env.flat_base + env.flat_len - 1 - (i - j)) as usize]
}

/// 环境扩展（**binder 链**：bind / β / 瞬时求值扩展）——O(1)。
#[inline]
pub(crate) fn env_ext<'a>(bump: &'a Bump, env: Env<'a>, v: V) -> Env<'a> {
    Env {
        flat_base: env.flat_base,
        flat_len: env.flat_len,
        binds: Some(bump.alloc(EnvCons { val: v, next: env.binds })),
    }
}

/// 环境扩展（**平坦 def 区域**：elaborator 的 define）。tip 环境原地追加
/// （chain 负载的 O(1) 线性保证）；其余回落 binder 链。tip 判定要求 binds
/// 为空：λ 体内 define 比链上 binder 更新，必须落在链头——追加平坦区会被
/// env_nth/AppPrun 的链优先序排到 binder 之后（de Bruijn 次序互换，错位值
/// 流进 solve 即错解/误报）。
#[inline]
pub(crate) fn env_ext_defs<'a>(
    bump: &'a Bump,
    defs: &mut Vec<V>,
    env: Env<'a>,
    v: V,
) -> Env<'a> {
    if env.binds.is_none() && env.flat_base + env.flat_len == defs.len() as u32 {
        defs.push(v);
        Env {
            flat_base: env.flat_base,
            flat_len: env.flat_len + 1,
            binds: env.binds,
        }
    } else {
        Env {
            flat_base: env.flat_base,
            flat_len: env.flat_len,
            binds: Some(bump.alloc(EnvCons { val: v, next: env.binds })),
        }
    }
}

/// 闭包单元：λ 的名字 + icit（quote 产出带 icit 的 `Lam`）+ env + 体。
pub(crate) struct CloCell<'a> {
    name: &'a str,
    icit: Icit,
    env: Env<'a>,
    body: &'a Tm<'a>,
}

/// Π 值单元：名字 + icit + 定义域值 + 余定义域闭包（内联，一次分配）。
pub(crate) struct PiCell<'a> {
    name: &'a str,
    icit: Icit,
    dom: V,
    env: Env<'a>,
    body: &'a Tm<'a>,
}

/// spine 栈槽：一次中性应用（icit 随槽携带）。`len`/`base` 支撑流式右链
/// quote；`decl` 标志函数侧是否 Decl 头（builtin 的增量触发要 O(1) 判定，
/// 不 walks 链——见 [`is_declheaded`]）。
struct Entry {
    f: V,
    a: V,
    icit: Icit,
    len: u32,
    base: u32,
    decl: bool,
}

/// 求值机持有的扁平中性栈（只增不减，槽位下标即句柄）。
pub(crate) struct Spine {
    stack: Vec<Entry>,
}

impl Spine {
    /// 中性应用 `f a`（icit i）压栈，返回句柄值。`decl` 随函数侧传播：
    /// 裸 Decl 单元或既有 decl 链延伸——后续应用可 O(1) 判定要触发 prim。
    #[inline]
    fn push(&mut self, f: V, a: V, icit: Icit) -> V {
        let idx = self.stack.len();
        let decl = match v_tag(f) {
            7 => matches!(v_xcell_of(f), XCell::Decl(_)),
            2 => self.stack[v_spine_of(f)].decl,
            _ => false,
        };
        let (len, base) = if v_tag(a) == 2 {
            let prev = &self.stack[v_spine_of(a)];
            (prev.len + 1, prev.base)
        } else {
            (1, idx as u32)
        };
        self.stack.push(Entry {
            f,
            a,
            icit,
            len,
            base,
            decl,
        });
        v_spine(idx)
    }

    /// 沿 `f` 指针走到链的最底层头（f 指针严格指向更早的槽位，必终止）。
    #[inline]
    fn spine_head(&self, h: usize) -> V {
        let mut cur = h;
        loop {
            let f = self.stack[cur].f;
            if v_tag(f) == 2 {
                cur = v_spine_of(f);
            } else {
                return f;
            }
        }
    }

    /// 收集链的**引用语义实参**（逆应用序：先 `h.a` 再沿 `f` 下行）。
    #[inline]
    fn collect_args(&self, h: usize, out: &mut Vec<(V, Icit)>) {
        let mut cur = h;
        loop {
            let e = &self.stack[cur];
            out.push((e.a, e.icit));
            if v_tag(e.f) == 2 {
                cur = v_spine_of(e.f);
            } else {
                return;
            }
        }
    }

    /// force 后的未解 flex 探测：`tag 5`（空 spine）或 spine 头是 `Meta`。
    /// 返回 meta 号并把逆应用序实参（带 icit）收进 `out`。要求调用方先 force。
    fn flex_of(&self, v: V, out: &mut Vec<(V, Icit)>) -> Option<u32> {
        match v_tag(v) {
            5 => Some(v_meta_of(v)),
            2 => {
                let h = v_spine_of(v);
                let hd = self.spine_head(h);
                if v_tag(hd) != 5 {
                    return None;
                }
                self.collect_args(h, out);
                Some(v_meta_of(hd))
            }
            _ => None,
        }
    }
}

/// 函数侧是否 Decl 头（builtin 触发判定）：裸单元直查；链查**顶端槽**的
/// `decl` 标志（push 时随函数侧传播，O(1)）。
#[inline]
fn is_declheaded(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        7 => matches!(v_xcell_of(v), XCell::Decl(_)),
        2 => spine.stack[v_spine_of(v)].decl,
        _ => false,
    }
}

/// 取 Decl 头的名（调用方已 `is_declheaded`）。
#[inline]
fn decl_name<'a>(spine: &Spine, v: V) -> &'a str {
    let head = if v_tag(v) == 7 {
        v
    } else {
        spine.spine_head(v_spine_of(v))
    };
    match v_xcell_of(head) {
        XCell::Decl(n) => n,
        XCell::Lit(_) => unreachable!("Lit 头不可触发"),
    }
}

// metacontext
// --------------------------------------------------------------------------------

/// metacontext 条目（与参考版同构）：**类型一律保留**（pruning 检查与
/// `lams` 都要读），解是 bump 内的打包值。
pub(crate) enum MetaEntry {
    Solved(V, V),
    Unsolved(V),
}

/// `vMeta` 的打包版：已解给解值，未解给 Meta 立即数。
#[inline]
fn meta_val_of(metas: &[MetaEntry], m: u32) -> V {
    match &metas[m as usize] {
        MetaEntry::Solved(v, _) => *v,
        MetaEntry::Unsolved(_) => v_meta(m),
    }
}

// builtin prim（L06 增量：decl 表 + 可变全局 + 按名触发）
// --------------------------------------------------------------------------------

/// builtin 的原语实现编号（参考版 `PrimFunc` 的 Rc<dyn Fn> 换成静态分派；
/// 全部实现都是纯函数或只动 `mutable_map` / decl 表 / 文件系统）。
#[derive(Clone, Copy)]
pub(crate) enum Prim {
    StrConcat,
    StrEq,
    StrIndent2,
    ReportCheckIssue,
    StringToGlobalType,
    CreateGlobal,
    ChangeMutable,
    GetGlobal,
    GetGlobalDefault,
    ChangeMutableDefault,
    FileReadAllText,
    FileWriteAllText,
    FileAppendAllText,
    FileExists,
    FileDelete,
}

/// decl 表条目（参考版 `DeclEntry` 的快版）：定义的值与类型，可选 builtin。
pub(crate) struct DeclEntryF {
    pub(crate) vt: V,
    pub(crate) va: V,
    pub(crate) prim: Option<Prim>,
}

/// 可变全局表（参考版 `Infer.mutable_map`；单线程 RefCell）。
pub(crate) type MutableMap = RefCell<FxHashMap<String, V>>;

/// 从实参值取字面量内容（非字面量 → None；参考版同款 match）。内容指向
/// 本轮 bump（调用域内使用）。
#[inline]
fn lit_of<'a>(v: V) -> Option<&'a str> {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => Some(s),
            XCell::Decl(_) => None,
        },
        _ => None,
    }
}

/// prim 的统一执行（参数自然序 = 应用序）。返回 `None` 保持卡住（元数
/// 不足 / 实参非字面量）；`change_mutable` 族要应用函数实参（走
/// [`vapp1`]），文件族失败 panic——均与参考版逐句对应。
#[allow(clippy::too_many_arguments)]
fn prim_fire<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    prim: Prim,
    args: &[V], // 自然序（应用序，最先应用在前）
) -> Option<V> {
    match prim {
        Prim::StrConcat => {
            if args.len() < 2 {
                return None;
            }
            match (lit_of(args[0]), lit_of(args[1])) {
                (Some(a), Some(b)) => {
                    let s = bump.alloc_str(&format!("{a}{b}"));
                    Some(v_xcell(bump.alloc(XCell::Lit(s))))
                }
                _ => None,
            }
        }
        Prim::StrEq => {
            if args.len() < 2 {
                return None;
            }
            match (lit_of(args[0]), lit_of(args[1])) {
                (Some(a), Some(b)) => {
                    let s = if a == b { "true" } else { "false" };
                    Some(v_xcell(bump.alloc(XCell::Lit(s))))
                }
                _ => None,
            }
        }
        Prim::StrIndent2 => {
            if args.is_empty() {
                return None;
            }
            match lit_of(args[0]) {
                Some(s) => {
                    let indented = s.replace('\n', "\n  ");
                    Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&indented)))))
                }
                _ => None,
            }
        }
        Prim::ReportCheckIssue => {
            if args.len() < 4 {
                return None;
            }
            let get = |i: usize| lit_of(args[i]).unwrap_or("").to_string();
            let (code, module, signal, message) = (get(0), get(1), get(2), get(3));
            if code.is_empty() || module.is_empty() {
                return Some(v_u());
            }
            let line = format!("{}|{}|{}|{}", code, module, signal, message);
            let mut map = mmap.borrow_mut();
            let existing = match map.get("CheckIssues") {
                Some(v) => lit_of(*v).unwrap_or("").to_string(),
                None => String::new(),
            };
            if !existing.split('\n').any(|l| l == line) {
                let next = if existing.is_empty() {
                    line
                } else {
                    format!("{}\n{}", existing, line)
                };
                map.insert(
                    "CheckIssues".to_string(),
                    v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&next)))),
                );
            }
            Some(v_u())
        }
        Prim::StringToGlobalType => {
            if args.is_empty() {
                return None;
            }
            match lit_of(args[0]) {
                Some(a) => Some(match decls.get(a) {
                    Some(e) => e.vt,
                    None => v_xcell(bump.alloc(XCell::Decl(bump.alloc_str(a)))),
                }),
                _ => None,
            }
        }
        Prim::CreateGlobal => {
            if args.len() < 2 {
                return None;
            }
            match lit_of(args[0]) {
                Some(a) => {
                    mmap.borrow_mut().insert(a.to_string(), args[1]);
                    Some(v_u())
                }
                _ => None,
            }
        }
        Prim::ChangeMutable => {
            if args.len() < 2 {
                return None;
            }
            match lit_of(args[0]) {
                Some(a) => {
                    if let Some(x) = mmap.borrow_mut().get_mut(a) {
                        let f = args[1];
                        let old = *x;
                        *x = vapp1(bump, spine, work, vals, icits, defs, metas, decls, mmap, f, old, Icit::Expl);
                    };
                    Some(v_u())
                }
                _ => None,
            }
        }
        Prim::GetGlobal => {
            if args.is_empty() {
                return None;
            }
            match lit_of(args[0]) {
                Some(a) => Some(*mmap.borrow().get(a).unwrap()),
                _ => None,
            }
        }
        Prim::GetGlobalDefault => {
            if args.len() < 2 {
                return None;
            }
            match lit_of(args[0]) {
                Some(a) => Some(
                    mmap.borrow()
                        .get(a)
                        .copied()
                        .unwrap_or(args[1]),
                ),
                _ => None,
            }
        }
        Prim::ChangeMutableDefault => {
            if args.len() < 3 {
                return None;
            }
            match lit_of(args[0]) {
                Some(a) => {
                    let mut map = mmap.borrow_mut();
                    if let Some(x) = map.get_mut(a) {
                        let f = args[1];
                        let old = *x;
                        *x = vapp1(bump, spine, work, vals, icits, defs, metas, decls, mmap, f, old, Icit::Expl);
                    } else {
                        map.insert(a.to_string(), args[2]);
                    };
                    Some(v_u())
                }
                _ => None,
            }
        }
        Prim::FileReadAllText => {
            if args.is_empty() {
                return None;
            }
            match lit_of(args[0]) {
                Some(path) => {
                    let content = std::fs::read_to_string(path)
                        .unwrap_or_else(|e| panic!("file_read_all_text: failed to read '{}': {}", path, e));
                    Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&content)))))
                }
                _ => None,
            }
        }
        Prim::FileWriteAllText => {
            if args.len() < 2 {
                return None;
            }
            match (lit_of(args[0]), lit_of(args[1])) {
                (Some(path), Some(content)) => {
                    std::fs::write(path, content)
                        .unwrap_or_else(|e| panic!("file_write_all_text: failed to write '{}': {}", path, e));
                    Some(v_u())
                }
                _ => None,
            }
        }
        Prim::FileAppendAllText => {
            if args.len() < 2 {
                return None;
            }
            match (lit_of(args[0]), lit_of(args[1])) {
                (Some(path), Some(content)) => {
                    use std::io::Write;
                    let mut file = std::fs::OpenOptions::new()
                        .append(true)
                        .create(true)
                        .open(path)
                        .unwrap_or_else(|e| panic!("file_append_all_text: failed to open '{}': {}", path, e));
                    write!(file, "{}", content).unwrap_or_else(|e| {
                        panic!("file_append_all_text: failed to append to '{}': {}", path, e)
                    });
                    Some(v_u())
                }
                _ => None,
            }
        }
        Prim::FileExists => {
            if args.is_empty() {
                return None;
            }
            match lit_of(args[0]) {
                Some(path) => {
                    let exists = std::path::Path::new(path).exists();
                    let s = if exists { "true" } else { "false" };
                    Some(v_xcell(bump.alloc(XCell::Lit(s))))
                }
                _ => None,
            }
        }
        Prim::FileDelete => {
            if args.is_empty() {
                return None;
            }
            match lit_of(args[0]) {
                Some(path) => {
                    std::fs::remove_file(path)
                        .unwrap_or_else(|e| panic!("file_delete: failed to delete '{}': {}", path, e));
                    Some(v_u())
                }
                _ => None,
            }
        }
    }
}

/// 参考版 `v_app` 的 Decl 臂：对 Decl 头应用实参——压栈得到全条累积
/// spine，再把**全部**实参（自然序）交给 prim（元数足够即触发；`None`
/// 保持卡住返回句柄）。无 prim / 未登记的名字同样保持卡住。
#[allow(clippy::too_many_arguments)]
fn decl_apply<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    f: V, // 裸 Decl 单元或 decl 头的链
    a: V,
    i: Icit,
) -> V {
    let acc = spine.push(f, a, i);
    let name = decl_name(spine, f);
    if let Some(entry) = decls.get(name) {
        if let Some(prim) = entry.prim {
            let mut args: Vec<(V, Icit)> = Vec::new();
            spine.collect_args(v_spine_of(acc), &mut args); // 逆应用序
            args.reverse(); // → 自然序
            let arg_vs: Vec<V> = args.iter().map(|&(v, _)| v).collect();
            if let Some(result) =
                prim_fire(bump, spine, work, vals, icits, defs, metas, decls, mmap, prim, &arg_vs)
            {
                return result;
            }
        }
    }
    acc
}

/// 独立应用（eval_iter 之外的 v_app：force 的解值应用、prim 的
/// `change_mutable`、unify 的 η 臂经调用方内联）。闭包 → β；Decl 头 →
/// [`decl_apply`]（可能触发 prim）；其余 → spine 压栈。参考版对 Π/U/Lit
/// 的应用 panic（"impossible"）；快版照 L05 对不可应用值压栈成卡住链
/// （仅良类型不可达的形态，见模块注释）。
#[allow(clippy::too_many_arguments)]
fn vapp1<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    f: V,
    a: V,
    i: Icit,
) -> V {
    if v_tag(f) == 1 {
        let c = v_clo_of(f);
        let env = env_ext(bump, c.env, a);
        eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, c.body)
    } else if is_declheaded(spine, f) {
        decl_apply(bump, spine, work, vals, icits, defs, metas, decls, mmap, f, a, i)
    } else {
        spine.push(f, a, i)
    }
}

// force（迭代）
// --------------------------------------------------------------------------------

/// **force**：把值更新到 metacontext 的当前状态。已解 meta 立即数 → 替换
/// 为解；已解 flex spine → 沿 f 链收集实参（带 icit）、把解按应用序应用到
/// 实参上（应用可触发 β / builtin prim，经 `vapp1`），再继续。
fn force<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    v0: V,
) -> V {
    let mut v = v0;
    // 实参缓冲在本次 force 调用内的已解链轮间复用（clear 保容量）
    let mut args: Vec<(V, Icit)> = Vec::new();
    loop {
        match v_tag(v) {
            5 => match &metas[v_meta_of(v) as usize] {
                MetaEntry::Solved(sol, _) => v = *sol,
                MetaEntry::Unsolved(_) => return v,
            },
            2 => {
                let h = v_spine_of(v);
                let hd = spine.spine_head(h);
                if v_tag(hd) != 5 {
                    return v; // 刚性/Decl 链
                }
                let m = v_meta_of(hd);
                match &metas[m as usize] {
                    MetaEntry::Unsolved(_) => return v,
                    MetaEntry::Solved(sol, _) => {
                        // 把解应用到全部实参（应用序 = 收集序的逆序）；
                        // 每步都可能 β（解是闭包）或触发 builtin（解是
                        // Decl 头的卡住链）——参考版 vAppSp 逐步 vApp 同款
                        args.clear();
                        spine.collect_args(h, &mut args);
                        let mut t = *sol;
                        for &(a, i) in args.iter().rev() {
                            t = vapp1(
                                bump, spine, work, vals, icits, defs, metas, decls, mmap, t, a, i,
                            );
                        }
                        v = t;
                    }
                }
            }
            _ => return v,
        }
    }
}

// eval（双栈迭代 + 右链快速路径 + AppPruning 实参应用 + decl 表）
// --------------------------------------------------------------------------------

/// eval 的 work 栈条目。
enum W<'a> {
    Tm(&'a Tm<'a>, Env<'a>),
    /// 应用（icit 来自 `Tm::App`）：vals 顶两个（先函数后实参）——β、
    /// builtin 触发或入栈。
    Apply(Icit),
    /// vals 顶上是实参；函数值已知是闭包（β 岔路下降时已 `env_nth` 出来），
    /// 直接 β（icit 无关）。
    ApplyKnown(V),
    /// vals 顶上是 base 值，其下 `k` 个是待应用的链头（内层最上；每个链头
    /// 的 icit 在 `icits` 侧栈平行压弹）。
    ChainWrap(u32),
    /// vals 顶是 let 绑定的值：弹出压进环境，继续求值体。
    LetBody(&'a Tm<'a>, Env<'a>),
    /// vals 顶是 Π 定义域值：弹出配余定义域闭包，压 Π 值。
    PiBody(&'a str, Icit, &'a Tm<'a>, Env<'a>),
    /// vals 顶是 `vAppPruning` 的当前值；沿 (env, pr) 平行走完剩余槽位
    /// （外层先应用，icit 取自掩码；`None` 槽跳过）。
    AppPrun(Env<'a>, Option<&'a PrCons<'a>>),
    /// vals 顶是 `vAppPruning` 的当前值；本步把 `arg` 以 `icit` 应用上去
    /// （Clo → β；Decl 头 → prim；其它 → spine.push）。
    AppPrunOne(V, Icit),
}

/// 双栈迭代 eval（L05 版 + L06 增量：decl 表查找、字面量、Decl 头应用的
/// builtin 触发）。
#[allow(clippy::too_many_arguments)]
fn eval_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    env0: Env<'a>,
    tm0: &'a Tm<'a>,
) -> V {
    work.clear();
    vals.clear();
    icits.clear();
    work.push(W::Tm(tm0, env0));
    while let Some(w) = work.pop() {
        match w {
            W::Tm(Tm::Var(i), env) => vals.push(env_nth(defs, env, *i)),
            W::Tm(Tm::Lam(name, icit, body), env) => {
                let c = bump.alloc(CloCell {
                    name,
                    icit: *icit,
                    env,
                    body,
                });
                vals.push(v_clo(c));
            }
            W::Tm(Tm::U, _) => vals.push(v_u()),
            W::Tm(Tm::LiteralType, _) => vals.push(v_lit_ty()),
            W::Tm(Tm::LiteralIntro(s), _) => {
                vals.push(v_xcell(bump.alloc(XCell::Lit(s))))
            }
            // 按名查 decl 表：命中给登记值（builtin 即卡住的头，应用时触发
            // prim）；miss 保持卡住（现造 Decl 单元，参考版同款每次新值）
            W::Tm(Tm::Decl(name), _) => vals.push(match decls.get(*name) {
                Some(e) => e.vt,
                None => v_xcell(bump.alloc(XCell::Decl(name))),
            }),
            W::Tm(Tm::Pi(name, icit, dom, cod), env) => {
                work.push(W::PiBody(name, *icit, cod, env));
                work.push(W::Tm(dom, env));
            }
            W::Tm(Tm::Let(_, _, t, u), env) => {
                work.push(W::LetBody(u, env));
                work.push(W::Tm(t, env));
            }
            W::Tm(Tm::Meta(m), _) => vals.push(meta_val_of(metas, *m)),
            W::Tm(Tm::AppPruning(head, pr), env) => {
                work.push(W::AppPrun(env, *pr));
                work.push(W::Tm(head, env));
            }
            W::Tm(app @ Tm::App(..), env) => {
                // 右链下钻：头为非闭包变量时头值直接进 vals（icit 进侧栈）
                let mut tm = app;
                let mut heads: u32 = 0;
                loop {
                    let (f, a, i) = match tm {
                        Tm::App(f, a, i) => (f, a, i),
                        base => {
                            if heads > 0 {
                                work.push(W::ChainWrap(heads));
                            }
                            work.push(W::Tm(base, env));
                            break;
                        }
                    };
                    let i = *i;
                    match f {
                        Tm::Var(ix) => {
                            let vf = env_nth(defs, env, *ix);
                            if v_tag(vf) == 1 {
                                // β 岔路：函数值已在手上（闭包），ApplyKnown
                                // 直接管 β（icit 无关）；heads>0 时 ChainWrap
                                // 照旧收拢
                                if heads > 0 {
                                    work.push(W::ChainWrap(heads));
                                }
                                work.push(W::ApplyKnown(vf));
                                work.push(W::Tm(a, env));
                                break;
                            }
                            vals.push(vf);
                            icits.push(i);
                            heads += 1;
                            tm = a;
                        }
                        _ => {
                            // 复合函数头：通用三推（同样先收已收的头）
                            if heads > 0 {
                                work.push(W::ChainWrap(heads));
                            }
                            work.push(W::Apply(i));
                            work.push(W::Tm(a, env));
                            work.push(W::Tm(f, env));
                            break;
                        }
                    }
                }
            }
            W::Apply(i) => {
                let va = vals.pop().expect("eval 栈：Apply 缺实参");
                let vf = vals.pop().expect("eval 栈：Apply 缺函数");
                if v_tag(vf) == 1 {
                    // β 归约是尾调用：直接推入体，继续循环
                    let c = v_clo_of(vf);
                    let env = env_ext(bump, c.env, va);
                    work.push(W::Tm(c.body, env));
                } else if is_declheaded(spine, vf) {
                    let r = decl_apply(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, vf, va, i,
                    );
                    vals.push(r);
                } else {
                    vals.push(spine.push(vf, va, i));
                }
            }
            W::ApplyKnown(vf) => {
                let va = vals.pop().expect("eval 栈：ApplyKnown 缺实参");
                let c = v_clo_of(vf);
                let env = env_ext(bump, c.env, va);
                work.push(W::Tm(c.body, env));
            }
            W::ChainWrap(k) => {
                let mut v = vals.pop().expect("eval 栈：ChainWrap 缺 base");
                for _ in 0..k {
                    let vf = vals.pop().expect("eval 栈：ChainWrap 缺链头");
                    let i = icits.pop().expect("eval 栈：ChainWrap 缺 icit");
                    // 链头是 Decl 值（define 的卡住头）：应用即触发尝试
                    // （参考版 vApp 的 Decl 臂；通常 None 保持卡住）
                    v = if is_declheaded(spine, vf) {
                        decl_apply(
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, vf, v, i,
                        )
                    } else {
                        spine.push(vf, v, i)
                    };
                }
                vals.push(v);
            }
            W::LetBody(u, env) => {
                let vt = vals.pop().expect("eval 栈：LetBody 缺绑定值");
                work.push(W::Tm(u, env_ext(bump, env, vt)));
            }
            W::PiBody(name, icit, cod, env) => {
                let dom = vals.pop().expect("eval 栈：PiBody 缺定义域");
                let cell = bump.alloc(PiCell {
                    name,
                    icit,
                    dom,
                    env,
                    body: cod,
                });
                vals.push(v_pi(cell));
            }
            W::AppPrun(env, bds) => match bds {
                None => {
                    // 与 reference 的 (None, None) 对齐：掩码先行耗尽
                    debug_assert!(env.binds.is_none() && env.flat_len == 0);
                }
                Some(b) if env.binds.is_none() && b.slot.is_none() => {
                    // O(1) 跳段：binds 耗尽后剩余链只剩 define 槽。
                    assert!(env.flat_len >= b.none_run);
                    work.push(W::AppPrun(
                        Env {
                            flat_len: env.flat_len - b.none_run,
                            ..env
                        },
                        b.after_run,
                    ));
                }
                Some(b) => {
                    // 内层绑定 = 链头；链耗尽后走平坦 def 区域末端。先跑
                    // 余下槽位（外层），再应用本槽（内层最后应用）
                    let (arg, rest) = if let Some(e) = env.binds {
                        (
                            b.slot.map(|_| e.val),
                            Env {
                                binds: e.next,
                                ..env
                            },
                        )
                    } else if env.flat_len > 0 {
                        let v = defs[(env.flat_base + env.flat_len - 1) as usize];
                        (
                            b.slot.map(|_| v),
                            Env {
                                flat_len: env.flat_len - 1,
                                ..env
                            },
                        )
                    } else {
                        panic!("impossible") // env 与 pr 错位
                    };
                    match (arg, b.slot) {
                        (Some(a), Some(i)) => work.push(W::AppPrunOne(a, i)),
                        (None, Some(_)) => panic!("impossible"), // env 短于 pr
                        _ => {}
                    }
                    work.push(W::AppPrun(rest, b.next));
                }
            },
            W::AppPrunOne(arg, i) => {
                let v = vals.pop().expect("eval 栈：AppPrunOne 缺值");
                if v_tag(v) == 1 {
                    let c = v_clo_of(v);
                    let env = env_ext(bump, c.env, arg);
                    work.push(W::Tm(c.body, env));
                } else if is_declheaded(spine, v) {
                    let r = decl_apply(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, v, arg, i,
                    );
                    vals.push(r);
                } else {
                    vals.push(spine.push(v, arg, i));
                }
            }
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}

// quote（任务栈迭代 + 流式右链；flex/Decl 头共享节点）
// --------------------------------------------------------------------------------

/// quote 任务。`ChainRun` 的「断点续跑」语义见 L01/L04/L05；quote 不产
/// `AppPruning`（项层洞形态，值层不存在）；L06 增量：Decl 头的链同样走
/// 流式右链（共享单一 `Tm::Decl` 节点）。
enum QJob<'a> {
    /// 引一个值（先 force）。
    Q(V, u32),
    /// done 栈顶是体，包一层 Lam（名字与 icit 随闭包携带）。
    Lam1(&'a str, Icit),
    /// done 栈顶两个（先 cod 后 dom），合一个 Pi（icit 在 PiCell 里）。
    Pi1(&'a PiCell<'a>),
    /// 先 eval（引出闭包/余定义域的体）再引。
    EvalQ(&'a Tm<'a>, Env<'a>, u32),
    /// done 栈顶两个（先 f 后 a），合一个 App（icit 随任务携带）——
    /// 二叉 fallback 用。
    App1(Icit),
    /// 记忆化屏障：done 栈顶是刚完成的 `Q(key, level)` 结果，入表后放回。
    MemoStore(u64, u32),
    /// 流式右链：next..=end 逐层 App 自底向上；f 与 f0 同一变量 / 同一未解
    /// meta / 同一 Decl 名时用共享节点，否则挂起（Q 引 f）后续跑。
    ChainRun {
        level: u32,
        next: usize,
        end: usize,
        f0: V,
        idx_node: Option<&'a Tm<'a>>,
        prev: Option<&'a Tm<'a>>,
    },
}

/// (值打包字, quote level) → 已引结果子树。icit 不进键：它随 `V` 指向的
/// 单元/槽位携带，同一打包字在同一 level 的 quote 产出（含 icit）唯一。
type QuoteMemo<'a> = FxHashMap<(u64, u32), &'a Tm<'a>>;

/// 任务栈 quote（L05 版 + LiteralType/LiteralIntro/Decl 臂）。
#[allow(clippy::too_many_arguments)]
fn quote_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    tasks: &mut Vec<QJob<'a>>,
    done: &mut Vec<&'a Tm<'a>>,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    level0: u32,
    v0: V,
    mut memo: Option<&mut QuoteMemo<'a>>,
) -> &'a Tm<'a> {
    tasks.clear();
    done.clear();
    tasks.push(QJob::Q(v0, level0));
    while let Some(job) = tasks.pop() {
        match job {
            QJob::Q(v0, level) => {
                // 先 force（metacontext 在 quote 期间冻结，同键同结果）
                let v = force(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, v0,
                );
                match v_tag(v) {
                    0 => done.push(bump.alloc(Tm::Var(level - v_lvl_of(v) - 1))),
                    1 => {
                        if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                            done.push(*t);
                            continue;
                        }
                        let c = v_clo_of(v);
                        if memo.is_some() {
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        let env = env_ext(bump, c.env, v_lvl(level));
                        tasks.push(QJob::Lam1(c.name, c.icit));
                        tasks.push(QJob::EvalQ(c.body, env, level + 1));
                    }
                    5 => done.push(bump.alloc(Tm::Meta(v_meta_of(v)))),
                    3 => done.push(bump.alloc(Tm::U)),
                    // L06：字面量类型与字面量值（叶子，无 memo 收益）
                    6 => done.push(bump.alloc(Tm::LiteralType)),
                    7 => done.push(bump.alloc(match v_xcell_of(v) {
                        XCell::Lit(s) => Tm::LiteralIntro(s),
                        XCell::Decl(s) => Tm::Decl(s),
                    })),
                    4 => {
                        if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                            done.push(*t);
                            continue;
                        }
                        let cell = v_pi_of(v);
                        if memo.is_some() {
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        let env = env_ext(bump, cell.env, v_lvl(level));
                        tasks.push(QJob::Pi1(cell));
                        tasks.push(QJob::EvalQ(cell.body, env, level + 1));
                        tasks.push(QJob::Q(cell.dom, level));
                    }
                    _ => {
                        if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                            done.push(*t);
                            continue;
                        }
                        if memo.is_some() {
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        // 先拷出标量再继续（后续任务会 push spine，Vec 可能扩容）
                        let h = v_spine_of(v);
                        let (ea, len, base, top_icit) = {
                            let e = &spine.stack[h];
                            (e.a, e.len, e.base, e.icit)
                        };
                        if len > 1 && base as usize + len as usize - 1 == h {
                            // 连续右链：先引 base，再 ChainRun 自底向上扫
                            let f0 = spine.stack[base as usize].f;
                            let idx_node = match v_tag(f0) {
                                0 => Some(
                                    &*bump.alloc(Tm::Var(level - v_lvl_of(f0) - 1))
                                        as &Tm<'a>,
                                ),
                                // flex 链头：未解 meta 立即数（已解的在
                                // force 里早已展开），共享单一 ?m 节点
                                5 => Some(&*bump.alloc(Tm::Meta(v_meta_of(f0))) as &Tm<'a>),
                                // Decl 链头：共享单一名字节点（Lit 头挂起
                                // 走 Q，良类型不可达）
                                7 => match v_xcell_of(f0) {
                                    XCell::Decl(s) => {
                                        Some(&*bump.alloc(Tm::Decl(s)) as &Tm<'a>)
                                    }
                                    XCell::Lit(_) => None,
                                },
                                _ => None,
                            };
                            let base_v = spine.stack[base as usize].a;
                            tasks.push(QJob::ChainRun {
                                level,
                                next: base as usize,
                                end: h,
                                f0,
                                idx_node,
                                prev: None,
                            });
                            tasks.push(QJob::Q(base_v, level));
                        } else {
                            tasks.push(QJob::App1(top_icit));
                            tasks.push(QJob::Q(ea, level));
                            tasks.push(QJob::Q(spine.stack[h].f, level));
                        }
                    }
                }
            }
            QJob::Lam1(name, icit) => {
                let body = done.pop().expect("quote 栈：Lam 缺体");
                done.push(bump.alloc(Tm::Lam(name, icit, body)));
            }
            QJob::Pi1(cell) => {
                let cod = done.pop().expect("quote 栈：Pi 缺余定义域");
                let dom = done.pop().expect("quote 栈：Pi 缺定义域");
                done.push(bump.alloc(Tm::Pi(cell.name, cell.icit, dom, cod)));
            }
            QJob::EvalQ(body, env, level) => {
                let v = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, env, body,
                );
                tasks.push(QJob::Q(v, level));
            }
            QJob::App1(icit) => {
                let a = done.pop().expect("quote 栈：App 缺实参");
                let f = done.pop().expect("quote 栈：App 缺函数");
                done.push(bump.alloc(Tm::App(f, a, icit)));
            }
            QJob::MemoStore(key, level) => {
                let m = memo
                    .as_deref_mut()
                    .expect("quote 栈：MemoStore 缺 memo 表");
                let t = done.pop().expect("quote 栈：MemoStore 缺结果");
                m.insert((key, level), t);
                done.push(t);
            }
            QJob::ChainRun {
                level,
                next,
                end,
                f0,
                idx_node,
                prev,
            } => {
                let mut prev = match prev {
                    Some(p) => {
                        // 恢复点：非平凡 f 刚引完在 done 栈顶，合掉一层
                        // （悬挂槽位 = next-1，其 icit 即本层应用的 icit）
                        let f_node = done.pop().expect("quote 栈：链缺函数头");
                        let icit = spine.stack[next - 1].icit;
                        bump.alloc(Tm::App(f_node, p, icit))
                    }
                    None => done.pop().expect("quote 栈：链缺 base"),
                };
                let mut i = next;
                loop {
                    if i > end {
                        done.push(prev);
                        break;
                    }
                    let fi = spine.stack[i].f;
                    match idx_node {
                        Some(n) if fi.0 == f0.0 => {
                            prev = bump.alloc(Tm::App(n, prev, spine.stack[i].icit));
                            i += 1;
                        }
                        _ => {
                            // 非平凡链头：挂起引 f，ChainRun 续跑
                            tasks.push(QJob::ChainRun {
                                level,
                                next: i + 1,
                                end,
                                f0,
                                idx_node,
                                prev: Some(prev),
                            });
                            tasks.push(QJob::Q(fi, level));
                            break;
                        }
                    }
                }
            }
        }
    }
    done.pop().expect("quote 必须恰有一个根")
}

// unify（工作表迭代 + force 前置 + 模式求解 + intersect/flex-flex + L06 字面量/Decl 臂）
// --------------------------------------------------------------------------------

/// A/B 实验开关（unify 工作表的判等记忆化消融）：置 `L06_NO_CONV_MEMO=1`
/// 关闭（`=0` 不关闭）。
static NO_CONV_MEMO: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L06_NO_CONV_MEMO").is_ok_and(|v| v != "0"))
    });

/// unify 工作表条目：待比较子对，或 Π 余定义域的惰性比较屏障，或判等
/// 记忆化屏障。
enum UItem<'a> {
    /// 待比较子对（level 相同的一对值；弹出时先 force 双方再分派）。
    Pair(u32, V, V),
    /// Π 余定义域的惰性比较（排在 dom 对之下——dom 不等即失败，cod 的
    /// eval 整个省掉）。
    EvalCod2(&'a Tm<'a>, Env<'a>, &'a Tm<'a>, Env<'a>, u32),
    /// 判等记忆化屏障（LIFO；健壮性论证同 L03——solve 写一次、成功单调）。
    Store((u64, u64)),
}

/// `?m args ≡ ?m args'`（同头 flex）：上游 `intersect`。逐槽（内→外）
/// 都取到裸变量则产出掩码（槽位相等 → 其 icit、不等 → None）；有 None 即
/// 剪枝（`pruneMeta`），全相等即成立。长度不等直接失败（参考版
/// intersect_go 的 `_ => None` → unify_sp 长度失配分支：失配即败、零比较）。
/// 任一对含非变量 → 回落 `unify_sp` 逐实参比较。
#[allow(clippy::too_many_arguments)]
fn intersect_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    stack: &mut Vec<UItem<'a>>,
    l: u32,
    m: u32,
    args1: &[(V, Icit)], // 内先（collect_args 的产出序）
    args2: &[(V, Icit)],
) -> bool {
    let n1 = args1.len();
    let n2 = args2.len();
    if n1 != n2 {
        return false; // 长度失配：直败零比较（连 force/压栈都省）
    }
    let common = n1;
    let mut pr: Vec<Option<Icit>> = Vec::with_capacity(common);
    let mut fallback = false;
    for k in 0..common {
        let f1 = force(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, args1[k].0,
        );
        let f2 = force(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, args2[k].0,
        );
        if v_tag(f1) == 0 && v_tag(f2) == 0 {
            pr.push(if v_lvl_of(f1) == v_lvl_of(f2) {
                Some(args1[k].1)
            } else {
                None
            });
        } else {
            fallback = true; // 上游 go 的 None：回落 unify_sp
            break;
        }
    }
    if !fallback {
        if pr.iter().any(|x| x.is_none()) {
            return prune_meta_bump(bump, spine, work, vals, icits, defs, metas, decls, mmap, &pr, m)
                .is_some();
        }
        return true; // 两 spine 逐槽相等
    }
    // unify_sp 回落：前缀对压栈（内先压 → 弹出外先，对齐 unify_sp 的递归序）。
    // tag 7 不跳过：参考版对字面量实参照走 unify（恒败）、对 Decl 实参照
    // 走同名逐参——位相等的同单元也须分派（见 unify 的 (7,7) 臂）。
    for k in 0..common {
        let (a1, _) = args1[k];
        let (a2, _) = args2[k];
        if a1.0 != a2.0 || v_tag(a1) == 7 {
            stack.push(UItem::Pair(l, a1, a2));
        }
    }
    true
}

/// 异头 flex-flex（上游 `flexFlex`）：较长 spine 一侧优先反演求解；反演
/// 失败则用另一侧求解（rhs 是整条 flex 值）。
#[allow(clippy::too_many_arguments)]
fn flex_flex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    ren: &mut RenBuf,
    gamma: u32,
    m1: u32,
    args1: &[(V, Icit)],
    v1: V,
    m2: u32,
    args2: &[(V, Icit)],
    v2: V,
) -> bool {
    let (ma, argsa, vrhs, mb, argsb, vlhs) = if args1.len() < args2.len() {
        (m2, args2, v2, m1, args1, v1)
    } else {
        (m1, args1, v1, m2, args2, v2)
    };
    match invert_bump(bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, gamma, argsa) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, gamma, ma,
            argsa.len() as u32, mask, vrhs,
        ),
        None => {
            // 一侧非模式：落另一侧（solve = invert + solve_with_pren）
            match invert_bump(bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, gamma, argsb) {
                Some(mask) => solve_with_pren_bump(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, gamma, mb,
                    argsb.len() as u32, mask, vlhs,
                ),
                None => false,
            }
        }
    }
}

/// unification：结构比较 + 模式求解（含 intersect / flex-flex / 剪枝），
/// 工作表迭代。分派与参考版逐项对应（顺序按 tag 互斥重排）：λ/η → U →
/// Π（icit 相等）→ 同头 rigid 逐实参 → 同头 flex = intersect → 异头
/// flex = flex_flex → 单侧 flex 求解 → L06 的 LiteralType/Decl 臂 →
/// 其余刚性失配。**位相等捷径与实参跳过对 tag 7 关闭**：参考版 unify
/// 无 `(Lit, Lit)` 臂——同字面量也 Err，同单元 Decl 需走同名逐参分派，
/// 位相等直接放行会错 Accept。
#[allow(clippy::too_many_arguments)]
fn unify_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    ren: &mut RenBuf,
    conv: &mut ConvScratch,
    l0: u32,
    t0: V,
    u0: V,
) -> bool {
    let memo_on = !NO_CONV_MEMO.load(std::sync::atomic::Ordering::Relaxed);
    // 草稿复用（Machine 常驻）：清空保容量，热路径零分配
    conv.memo.clear();
    conv.scratch1.clear();
    conv.scratch2.clear();
    let memo = &mut conv.memo;
    let mut stack: Vec<UItem<'a>> = Vec::new();
    stack.push(UItem::Pair(l0, t0, u0));
    while let Some(item) = stack.pop() {
        let (l, t, u) = match item {
            UItem::Store(key) => {
                memo.insert(key);
                continue;
            }
            UItem::EvalCod2(b1, e1, b2, e2, l) => {
                let vt = {
                    let env = env_ext(bump, e1, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, b1)
                };
                let vu = {
                    let env = env_ext(bump, e2, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, b2)
                };
                stack.push(UItem::Pair(l + 1, vt, vu));
                continue;
            }
            UItem::Pair(l, t, u) => (l, t, u),
        };
        // 位相等：同一值。tag 7 例外（见函数注释——参考版 unify 对字面量
        // 无自反性，Decl 需同名分派）
        if t.0 == u.0 && v_tag(t) != 7 {
            continue;
        }
        if memo_on && memo.contains(&(t.0, u.0)) {
            continue; // 本轮已判等过的子对（命中连 force 都省——成功单调）
        }
        let t = force(bump, spine, work, vals, icits, defs, metas, decls, mmap, t);
        let u = force(bump, spine, work, vals, icits, defs, metas, decls, mmap, u);
        if t.0 == u.0 && v_tag(t) != 7 {
            continue; // force 展开后同值（同一解的两处引用）
        }
        match (v_tag(t), v_tag(u)) {
            // λ 情形（eta 含）：两边都应用到同一个新变量
            (1, 1) => {
                let c1 = v_clo_of(t);
                let c2 = v_clo_of(u);
                let vt = {
                    let env = env_ext(bump, c1.env, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, c1.body)
                };
                let vu = {
                    let env = env_ext(bump, c2.env, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, c2.body)
                };
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l + 1, vt, vu));
            }
            // η：中性一侧按 λ 一侧的 icit 应用（Decl 头的应用可能触发
            // builtin——走 decl_apply）
            (_, 1) => {
                let c = v_clo_of(u);
                let vu = {
                    let env = env_ext(bump, c.env, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, c.body)
                };
                let vt = if is_declheaded(spine, t) {
                    decl_apply(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, t, v_lvl(l),
                        c.icit,
                    )
                } else {
                    spine.push(t, v_lvl(l), c.icit)
                };
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l + 1, vt, vu));
            }
            (1, _) => {
                let c = v_clo_of(t);
                let vt = {
                    let env = env_ext(bump, c.env, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, env, c.body)
                };
                let vu = if is_declheaded(spine, u) {
                    decl_apply(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, u, v_lvl(l),
                        c.icit,
                    )
                } else {
                    spine.push(u, v_lvl(l), c.icit)
                };
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l + 1, vt, vu));
            }

            // 宇宙
            (3, 3) => {}

            // Π：icit 相等才比；先比定义域，再惰性 eval 两侧余定义域
            (4, 4) => {
                let p = v_pi_of(t);
                let q = v_pi_of(u);
                if p.icit != q.icit {
                    return false;
                }
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::EvalCod2(p.body, p.env, q.body, q.env, l));
                stack.push(UItem::Pair(l, p.dom, q.dom));
            }

            // 变量
            (0, 0) => return false, // 位相等已剪同 level；异 level 必不等

            // 中性链 vs 中性链
            (2, 2) => {
                let h1 = v_spine_of(t);
                let h2 = v_spine_of(u);
                let hd1 = spine.spine_head(h1);
                let hd2 = spine.spine_head(h2);
                let f1 = v_tag(hd1) == 5;
                let f2 = v_tag(hd2) == 5;
                if f1 && f2 {
                    // 双 flex：同头 intersect、异头 flex_flex
                    let mut a1 = std::mem::take(&mut conv.scratch1);
                    a1.clear();
                    spine.collect_args(h1, &mut a1);
                    let mut a2 = std::mem::take(&mut conv.scratch2);
                    a2.clear();
                    spine.collect_args(h2, &mut a2);
                    let m1 = v_meta_of(hd1);
                    let m2 = v_meta_of(hd2);
                    let ok = if m1 == m2 {
                        intersect_bump(
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, &mut stack,
                            l, m1, &a1, &a2,
                        )
                    } else {
                        flex_flex_bump(
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, l, m1,
                            &a1, u, m2, &a2, t,
                        )
                    };
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                // 同头判定：位相等（同变量 / 同 meta / 同单元）或**同名
                // Decl 头**（参考版 `x == x_prime` 比较 Span——decl 值的名
                // 全部来自 empty_span 构造，等价于名内容相等）
                let same_head = hd1.0 == hd2.0
                    || (v_tag(hd1) == 7
                        && v_tag(hd2) == 7
                        && matches!(
                            (v_xcell_of(hd1), v_xcell_of(hd2)),
                            (XCell::Decl(n1), XCell::Decl(n2)) if n1 == n2
                        ));
                if same_head {
                    // 同头刚性/Decl：逐实参比较（应用序；收集是逆序，压栈
                    // 倒回）。实参 icit 不比（类型已定，上游同款）。
                    if memo_on {
                        stack.push(UItem::Store((t.0, u.0)));
                    }
                    // 受控内联环（L03-L05 同款门控）：沿 `.a` 同步下走，仅在
                    // 纯 ChainWrap 同头延续处（实参链顶层 `f` 与本层 `f`
                    // 同字）；实参若是另一条中性链（Apply 惯例：`f` =
                    // partial 句柄 ≠ 头字；`?6 a b` vs `?0 a a` 的实参正是
                    // 此类）则停下，把子对交回完整分派（异头 flex 走
                    // flex_flex、同头 flex 走 intersect）——盲下钻会跳过内层
                    // 头分派、误比其内层变量。派发序与参考版 unify_sp 同序：
                    // 停钻时先压实参对、后压函数部分对（函数部分在栈顶先
                    // 弹出）。
                    let mut i1 = h1;
                    let mut i2 = h2;
                    loop {
                        let (f1, a1) = {
                            let e = &spine.stack[i1];
                            (e.f, e.a)
                        };
                        let (f2, a2) = {
                            let e = &spine.stack[i2];
                            (e.f, e.a)
                        };
                        // 位相等后缀：实参对免比（tag 7 除外——字面量恒
                        // 败、Decl 走同名分派），函数部分对仍须入栈
                        if a1.0 == a2.0 && v_tag(a1) != 7 {
                            if f1.0 != f2.0 {
                                stack.push(UItem::Pair(l, f1, f2));
                            }
                            break;
                        }
                        if v_tag(a1) == 2 && v_tag(a2) == 2 {
                            // 下钻门控：两侧的实参链顶层 f 与本层 f 同字
                            let cont = spine.stack[v_spine_of(a1)].f.0 == f1.0
                                && spine.stack[v_spine_of(a2)].f.0 == f2.0;
                            if cont {
                                if f1.0 != f2.0 {
                                    stack.push(UItem::Pair(l, f1, f2));
                                }
                                i1 = v_spine_of(a1);
                                i2 = v_spine_of(a2);
                                continue;
                            }
                        }
                        stack.push(UItem::Pair(l, a1, a2));
                        if f1.0 != f2.0 {
                            stack.push(UItem::Pair(l, f1, f2));
                        }
                        break;
                    }
                    continue;
                }
                // 异头：一侧 flex 头（f1/f2 已排除双 flex）→ 该侧 solve；
                // 双刚性异头 → 刚性失配。
                let (mv, h, rhs) = if f1 {
                    (v_meta_of(hd1), h1, u)
                } else if f2 {
                    (v_meta_of(hd2), h2, t)
                } else {
                    return false;
                };
                let mut args = std::mem::take(&mut conv.scratch1);
                args.clear();
                spine.collect_args(h, &mut args);
                let solved = solve_bump(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, l, mv, &args,
                    rhs,
                );
                conv.scratch1 = args;
                if solved {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                return false;
            }

            // 其余形态：一侧（或两侧）是裸/带链 flex → 求解；L06 的
            // LiteralType / LiteralIntro / Decl 组合在此分派
            _ => {
                // L06 臂（参考版 unify 的末段）：String 类型自反；String
                // 类型与卡住 Decl 互通（decl 仍表示 String/U 型值）；同名
                // Decl 逐实参（空 spine 自反成立）；(Lit, Lit) 恒败（含
                // 同单元——参考版无该臂）。
                match (v_tag(t), v_tag(u)) {
                    (6, 6) => continue,
                    (6, 7) | (7, 6) => {
                        let other = if v_tag(t) == 7 { t } else { u };
                        if matches!(v_xcell_of(other), XCell::Decl(_)) {
                            continue;
                        }
                        return false; // LiteralType vs 字面量：刚性失配
                    }
                    // 裸单元对（带实参的 Decl 是 tag 2 链，在 (2,2) 的同名
                    // 分支走 lockstep 逐实参）：同名 Decl 空 spine 自反成立
                    (7, 7) => match (v_xcell_of(t), v_xcell_of(u)) {
                        (XCell::Lit(_), XCell::Lit(_)) => return false, // 参考版无该臂
                        (XCell::Decl(n1), XCell::Decl(n2)) => {
                            if n1 == n2 {
                                continue;
                            }
                            return false; // 异名 Decl
                        }
                        _ => return false, // Lit vs Decl
                    },
                    _ => {}
                }
                let mut a1 = std::mem::take(&mut conv.scratch1);
                a1.clear();
                let ft = spine.flex_of(t, &mut a1);
                let mut a2 = std::mem::take(&mut conv.scratch2);
                a2.clear();
                let fu = spine.flex_of(u, &mut a2);
                let ok = match (ft, fu) {
                    (Some(m1), Some(m2)) => {
                        if m1 == m2 {
                            intersect_bump(
                                bump, spine, work, vals, icits, defs, metas, decls, mmap,
                                &mut stack, l, m1, &a1, &a2,
                            )
                        } else {
                            flex_flex_bump(
                                bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, l,
                                m1, &a1, u, m2, &a2, t,
                            )
                        }
                    }
                    (Some(m), None) => solve_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, l, m, &a1,
                        u,
                    ),
                    (None, Some(m)) => solve_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, l, m, &a2,
                        t,
                    ),
                    (None, None) => false, // 刚性失配 / 病态混杂
                };
                conv.scratch1 = a1;
                conv.scratch2 = a2;
                if ok {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                return false;
            }
        }
    }
    true
}

// solve（invert + prune 验证 + rename + lams，全迭代）
// --------------------------------------------------------------------------------

/// solve 的偏置换缓冲（generational）：`val[x]` 在第 `epoch` 代里给出
/// level x → 新下标；`stamp[x] == epoch` 表示条目有效。`reset` 只推进
/// epoch（O(1) 换代）。`NONE_MARK` 哨兵标记**非线性（重复）变量**——
/// `get` 视其为缺项。
#[derive(Default)]
struct RenBuf {
    val: Vec<u32>,
    /// 各 level 槽位的生效代数（与 `val` 平行）；`== epoch` 才有效。
    stamp: Vec<u64>,
    epoch: u64,
}

/// 非线性（重复）变量的哨兵值。
const NONE_MARK: u32 = u32::MAX;

impl RenBuf {
    /// 换代即「清空」：旧条目的 gen 不等于新 epoch，全部失效。
    #[inline]
    fn reset(&mut self) {
        self.epoch += 1;
    }
    /// `NONE_MARK` 视同缺项（非线性变量不在 renaming 里）。
    #[inline]
    fn get(&self, x: usize) -> Option<u32> {
        match self.stamp.get(x).copied() {
            Some(g) if g == self.epoch => {
                let v = self.val[x];
                if v == NONE_MARK {
                    None
                } else {
                    Some(v)
                }
            }
            _ => None,
        }
    }
    /// 本代里 `x` 是否已标非线性哨兵。
    #[inline]
    fn has_mark(&self, x: usize) -> bool {
        self.stamp.get(x).copied() == Some(self.epoch) && self.val[x] == NONE_MARK
    }
    #[inline]
    fn set(&mut self, x: usize, v: u32) {
        if x >= self.val.len() {
            self.val.resize(x + 1, 0);
            self.stamp.resize(x + 1, 0); // 0 != epoch（epoch 从 1 起）
        }
        self.val[x] = v;
        self.stamp[x] = self.epoch;
    }
}

/// 上游 `invert`：实参（应用序）逐个 force 成**裸刚性变量**。非线性
/// （重复变量）移出 renaming、记 `NONE_MARK`，产出把重复变量的全部出现
/// 记为 `None` 的掩码（内先序 = args 序）；线性时返回空 vec。非变量实参
/// （字面量 / Decl / 带链变量）即失败（`None`）。
#[allow(clippy::too_many_arguments)]
fn invert_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    ren: &mut RenBuf,
    gamma: u32,
    args: &[(V, Icit)], // 内先序（spine 收集器的输出）
) -> Option<Vec<Option<Icit>>> {
    ren.reset(); // 换代：本反演的映射从空开始
    let mut lvs: Vec<u32> = Vec::with_capacity(args.len());
    let mut nonlinear = false;
    for &(a, _) in args.iter().rev() {
        // 应用序（外先）
        let f = force(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, a,
        );
        if v_tag(f) != 0 {
            return None;
        }
        let x = v_lvl_of(f);
        if x >= gamma {
            return None;
        }
        let i = lvs.len() as u32;
        lvs.push(x);
        match ren.get(x as usize) {
            // 已标非线性哨兵：保持 NONE_MARK 不动（第 3+ 次出现不覆盖）
            None if ren.has_mark(x as usize) => {}
            None => ren.set(x as usize, i),
            Some(_) => {
                ren.set(x as usize, NONE_MARK);
                nonlinear = true;
            }
        }
    }
    if !nonlinear {
        return Some(Vec::new());
    }
    // 掩码（内先序 = args 原序；重复变量整级剪除）
    let mut mask: Vec<Option<Icit>> = Vec::with_capacity(args.len());
    for k in (0..args.len()).rev() {
        // lvs 按应用序填：lvs[0] = 最先应用（外）；args[k] 内先 ↔ 应用序 n-1-k
        let x = lvs[args.len() - 1 - k] as usize;
        mask.push(match ren.get(x) {
            Some(_) => Some(args[k].1),
            None => None, // 非线性或从未映射 → 剪
        });
    }
    Some(mask)
}

/// `Γ ⊢ ?m args ≡ rhs` 的求解（invert 已做）：非线性掩码先验证剪枝可行性，
/// 再 rename（occurs/scope check 在内），λ 包裹取自 **meta 类型**，空环境
/// 求值写表。失败即不改 metacontext。
#[allow(clippy::too_many_arguments)]
fn solve_with_pren_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    ren: &mut RenBuf,
    gamma: u32,
    m: u32,
    dom: u32,
    mask: Vec<Option<Icit>>, // invert 的非线性掩码（空 vec = 线性）
    rhs: V,
) -> bool {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(a) => *a,
        _ => unreachable!(), // 只对未解 meta 求解
    };
    // 非线性 spine：检查非线性的变量槽位可以从 meta 类型里剪掉
    if !mask.is_empty()
        && prune_ty_bump(bump, spine, work, vals, icits, defs, metas, decls, mmap, &mask, mty)
            .is_none()
    {
        return false;
    }
    let Some(tm) =
        rename_iter(bump, spine, work, vals, icits, defs, ren, metas, decls, mmap, Some(m), dom, gamma, rhs)
    else {
        return false;
    };
    let lam_tm = lams_from_ty(bump, spine, work, vals, icits, defs, metas, decls, mmap, dom, mty, tm);
    let sol = eval_iter(
        bump, spine, work, vals, icits, defs, metas, decls, mmap, EMPTY_ENV, lam_tm,
    );
    metas[m as usize] = MetaEntry::Solved(sol, mty);
    true
}

/// solve = invert + solve_with_pren。
#[allow(clippy::too_many_arguments)]
fn solve_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    ren: &mut RenBuf,
    gamma: u32,
    m: u32,
    args: &[(V, Icit)],
    rhs: V,
) -> bool {
    match invert_bump(bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, gamma, args) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, ren, gamma, m,
            args.len() as u32, mask, rhs,
        ),
        None => false,
    }
}

/// rename 任务。icit 记账同 L04/L05：**只有刚性 `spine_case` 预装载**
/// `done_icits`（按收集序入栈）；flex 链走 `prune_vflex`（自持 fold，
/// 不碰 icit 栈）。
enum RJob<'a> {
    /// 引一个值到解域（产生一个 Tm 到 done）。
    Ren { dom: u32, cod: u32, v: V },
    /// 实参（逆应用序）已由其上任务引完，头是 head_tm，折叠 App
    /// （每个 App 的 icit 从平行 done_icits 栈取）。
    SpineFold {
        head_tm: &'a Tm<'a>,
        n: u32,
    },
    /// done 栈顶是体，包 Lam（icit 随闭包携带）。
    Lam1(&'a str, Icit),
    /// done 栈顶两个（先 cod 后 dom），合 Pi（icit 随 PiCell 携带）。
    Pi2(&'a PiCell<'a>),
}

/// partial renaming 的迭代版（L05 版 + L06 增量：LiteralType/LiteralIntro/
/// Decl 的 rename 臂与 Decl/Lit 头的 spine 重建）。
#[allow(clippy::too_many_arguments)]
fn rename_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    ren: &mut RenBuf,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    occ: Option<u32>,
    dom0: u32,
    cod0: u32,
    v0: V,
) -> Option<&'a Tm<'a>> {
    let mut tasks: Vec<RJob<'a>> = vec![RJob::Ren {
        dom: dom0,
        cod: cod0,
        v: v0,
    }];
    let mut done: Vec<&'a Tm<'a>> = Vec::new();
    // SpineFold 的实参 icit 预装载栈
    let mut done_icits: Vec<Icit> = Vec::new();
    // 实参收集 / 折叠草稿：跨任务复用（clear 保容量）
    let mut args: Vec<(V, Icit)> = Vec::new();
    let mut popped: Vec<&'a Tm<'a>> = Vec::new();
    macro_rules! spine_case {
        ($dom:expr, $cod:expr, $h:expr, $head_tm:expr, $tasks:expr) => {{
            args.clear();
            spine.collect_args($h, &mut args);
            $tasks.push(RJob::SpineFold {
                head_tm: $head_tm,
                n: args.len() as u32,
            });
            for &(_, i) in args.iter() {
                done_icits.push(i);
            }
            for &(a, _) in args.iter() {
                $tasks.push(RJob::Ren {
                    dom: $dom,
                    cod: $cod,
                    v: a,
                });
            }
        }};
    }
    while let Some(job) = tasks.pop() {
        match job {
            RJob::Ren { dom, cod, v } => {
                let v = force(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, v,
                );
                match v_tag(v) {
                    5 => {
                        let m = v_meta_of(v);
                        if occ == Some(m) {
                            return None; // occurs check
                        }
                        done.push(bump.alloc(Tm::Meta(m)));
                    }
                    0 => {
                        let x = v_lvl_of(v) as usize;
                        // scope check（x 不在 spine 映射里；非线性哨兵也算缺项）
                        let Some(xp) = ren.get(x) else {
                            return None;
                        };
                        done.push(bump.alloc(Tm::Var(dom - xp - 1)));
                    }
                    2 => {
                        let h = v_spine_of(v);
                        let hd = spine.spine_head(h);
                        match v_tag(hd) {
                            5 => {
                                // flex 链：pruneVFlex（occ 检查在内部先行）
                                let m = v_meta_of(hd);
                                if occ == Some(m) {
                                    return None; // occurs check
                                }
                                let t = prune_vflex_bump(
                                    bump, spine, work, vals, icits, defs, ren, metas, decls,
                                    mmap, occ, dom, cod, m, h,
                                )?;
                                done.push(t);
                            }
                            // L06：Decl / Lit 头的链照参考版 rename_sp 重建
                            // App 链（头名直出，实参逐个 rename）
                            7 => {
                                let head_tm: &'a Tm<'a> =
                                    bump.alloc(match v_xcell_of(hd) {
                                        XCell::Decl(s) => Tm::Decl(s),
                                        XCell::Lit(s) => Tm::LiteralIntro(s),
                                    });
                                spine_case!(dom, cod, h, head_tm, tasks);
                            }
                            _ => {
                                let x = v_lvl_of(hd) as usize;
                                let Some(xp) = ren.get(x) else {
                                    return None; // scope check
                                };
                                let head_tm = bump.alloc(Tm::Var(dom - xp - 1));
                                spine_case!(dom, cod, h, head_tm, tasks);
                            }
                        }
                    }
                    1 => {
                        let c = v_clo_of(v);
                        let bv = {
                            let env = env_ext(bump, c.env, v_lvl(cod));
                            eval_iter(
                                bump, spine, work, vals, icits, defs, metas, decls, mmap, env,
                                c.body,
                            )
                        };
                        // lift：binder 槽 (cod → dom)
                        ren.set(cod as usize, dom);
                        tasks.push(RJob::Lam1(c.name, c.icit));
                        tasks.push(RJob::Ren {
                            dom: dom + 1,
                            cod: cod + 1,
                            v: bv,
                        });
                    }
                    4 => {
                        let cell = v_pi_of(v);
                        let bv = {
                            let env = env_ext(bump, cell.env, v_lvl(cod));
                            eval_iter(
                                bump, spine, work, vals, icits, defs, metas, decls, mmap, env,
                                cell.body,
                            )
                        };
                        // lift（同 Lam）
                        ren.set(cod as usize, dom);
                        tasks.push(RJob::Pi2(cell));
                        tasks.push(RJob::Ren {
                            dom: dom + 1,
                            cod: cod + 1,
                            v: bv,
                        });
                        tasks.push(RJob::Ren {
                            dom,
                            cod,
                            v: cell.dom,
                        });
                    }
                    3 => done.push(bump.alloc(Tm::U)),
                    // L06：字面量类型与裸单元（Lit / Decl 空链）直出
                    6 => done.push(bump.alloc(Tm::LiteralType)),
                    7 => done.push(bump.alloc(match v_xcell_of(v) {
                        XCell::Lit(s) => Tm::LiteralIntro(s),
                        XCell::Decl(s) => Tm::Decl(s),
                    })),
                    _ => return None, // 病态（Π/U/字面量被应用等）
                }
            }
            RJob::SpineFold { head_tm, n } => {
                popped.clear();
                for _ in 0..n {
                    let t = done.pop()?;
                    popped.push(t);
                }
                let mut t = head_tm;
                for k in 0..n as usize {
                    let i = done_icits.pop()?;
                    let a = popped[n as usize - 1 - k];
                    t = bump.alloc(Tm::App(t, a, i));
                }
                done.push(t);
            }
            RJob::Lam1(name, icit) => {
                let body = done.pop()?; // 栈约定：子任务必已完成
                done.push(bump.alloc(Tm::Lam(name, icit, body)));
            }
            RJob::Pi2(cell) => {
                let cod = done.pop()?;
                let dom = done.pop()?;
                done.push(bump.alloc(Tm::Pi(cell.name, cell.icit, dom, cod)));
            }
        }
    }
    debug_assert_eq!(
        done_icits.len(),
        0,
        "icit 预装载必须全部配对弹出"
    );
    done.pop()
}

/// `pruneVFlex`：meta + 纯变量 renaming 判定与剪枝（L05 版原样；非变量
/// 实参——含字面量/Decl——嵌套 rename，与参考版 prune_vflex_go 的非
/// Rigid 臂一致）。
#[allow(clippy::too_many_arguments)]
fn prune_vflex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    ren: &mut RenBuf,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    occ: Option<u32>,
    dom: u32,
    cod: u32,
    m: u32,
    h: usize,
) -> Option<&'a Tm<'a>> {
    let mut args: Vec<(V, Icit)> = Vec::new();
    spine.collect_args(h, &mut args); // 内先序
    let mut slots: Vec<(Option<&'a Tm<'a>>, Icit)> = Vec::with_capacity(args.len());
    let mut status = SpinePruneStatus::OKRenaming;
    for &(a, i) in args.iter().rev() {
        // 应用序（外先）
        let f = force(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, a,
        );
        if v_tag(f) == 0 {
            match ren.get(v_lvl_of(f) as usize) {
                Some(xp) => slots.push((Some(bump.alloc(Tm::Var(dom - xp - 1))), i)),
                None if status == SpinePruneStatus::OKNonRenaming => return None,
                None => {
                    slots.push((None, i));
                    status = SpinePruneStatus::NeedsPruning;
                }
            }
        } else {
            if status == SpinePruneStatus::NeedsPruning {
                return None; // 上游：剪枝后 spine 必须全变量
            }
            let t = rename_iter(
                bump, spine, work, vals, icits, defs, ren, metas, decls, mmap, occ, dom, cod, f,
            )?;
            slots.push((Some(t), i));
            status = SpinePruneStatus::OKNonRenaming;
        }
    }
    let m_prime = if status == SpinePruneStatus::NeedsPruning {
        // 掩码内先序 = slots 反序
        let mut mask: Vec<Option<Icit>> = Vec::with_capacity(slots.len());
        for (st, i) in slots.iter().rev() {
            mask.push(if st.is_some() { Some(*i) } else { None });
        }
        prune_meta_bump(bump, spine, work, vals, icits, defs, metas, decls, mmap, &mask, m)?
    } else {
        m
    };
    // 折叠：上游 foldr = 最外层实参先应用（外先迭代，内层包在最外）
    let mut t: &'a Tm<'a> = bump.alloc(Tm::Meta(m_prime));
    for (st, i) in slots {
        if let Some(u) = st {
            t = bump.alloc(Tm::App(t, u, i));
        }
    }
    Some(t)
}

/// `pruneMeta`：检查剪后类型良型、造新 meta（类型 = 剪后值），旧 meta 解为
/// `λ telescope. AppPruning ?m' pruned`。掩码内先序（同 cxt 惯例）。
#[allow(clippy::too_many_arguments)]
fn prune_meta_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    mask: &[Option<Icit>], // 内先序
    m: u32,
) -> Option<u32> {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(a) => *a,
        _ => unreachable!(), // 只对未解 meta 剪枝
    };
    let pruned_tm = prune_ty_bump(bump, spine, work, vals, icits, defs, metas, decls, mmap, mask, mty)?;
    let prunedty = eval_iter(
        bump, spine, work, vals, icits, defs, metas, decls, mmap, EMPTY_ENV, pruned_tm,
    );
    let mp = metas.len() as u32;
    metas.push(MetaEntry::Unsolved(prunedty));
    // AppPruning 项：掩码外先入链（新槽恒链头 → 最终头 = 最内层）
    let mut pr: Option<&'a PrCons<'a>> = None;
    for slot in mask.iter().rev() {
        pr = Some(bump.alloc(PrCons::new(*slot, pr)));
    }
    let ap = bump.alloc(Tm::AppPruning(bump.alloc(Tm::Meta(mp)), pr));
    let lam_tm = lams_from_ty(
        bump, spine, work, vals, icits, defs, metas, decls, mmap, mask.len() as u32, mty, ap,
    );
    let sol = eval_iter(
        bump, spine, work, vals, icits, defs, metas, decls, mmap, EMPTY_ENV, lam_tm,
    );
    metas[m as usize] = MetaEntry::Solved(sol, mty);
    Some(mp)
}

/// `pruneTy (revPruning pr) a`：掩码**外→内**配对 Π 层。自带换代缓冲。
#[allow(clippy::too_many_arguments)]
fn prune_ty_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    mask_inner_first: &[Option<Icit>],
    mty: V,
) -> Option<&'a Tm<'a>> {
    let mut ren2 = RenBuf::default();
    ren2.reset(); // epoch 从 1 起（新槽 stamp 0 无效）
    let mut dom: u32 = 0;
    let mut cod: u32 = 0;
    let mut layers: Vec<(&'a str, Icit, &'a Tm<'a>)> = Vec::new();
    let mut cur = force(
        bump, spine, work, vals, icits, defs, metas, decls, mmap, mty,
    );
    for entry in mask_inner_first.iter().rev() {
        // 外→内
        if v_tag(cur) != 4 {
            return None; // 上游 impossible：掩码与类型层不匹配
        }
        let p = v_pi_of(cur);
        let (name, icit, pdom, env, body) = (p.name, p.icit, p.dom, p.env, p.body);
        if entry.is_some() {
            let dtm = rename_iter(
                bump, spine, work, vals, icits, defs, &mut ren2, metas, decls, mmap, None, dom, cod,
                pdom,
            )?;
            // lift：binder 进映射
            ren2.set(cod as usize, dom);
            layers.push((name, icit, dtm));
            dom += 1;
        }
        let next = eval_iter(
            bump,
            spine,
            work,
            vals,
            icits,
            defs,
            metas,
            decls,
            mmap,
            env_ext(bump, env, v_lvl(cod)),
            body,
        );
        cod += 1;
        cur = force(bump, spine, work, vals, icits, defs, metas, decls, mmap, next);
    }
    let mut t = rename_iter(
        bump, spine, work, vals, icits, defs, &mut ren2, metas, decls, mmap, None, dom, cod, cur,
    )?;
    // 保留层由内向外回包（layers 序 = 外→内，rev = 内→外 ✓）
    for (name, icit, dtm) in layers.iter().rev() {
        t = bump.alloc(Tm::Pi(name, *icit, dtm, t));
    }
    Some(t)
}

/// `lams l a t`：沿 **meta 类型**的 Π 层包 λ（名字与 icit 随 Π，`"_"` 改名
/// `x{l'}`；逐层用 `VVar l'` 剥闭包）。
#[allow(clippy::too_many_arguments)]
fn lams_from_ty<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    l: u32,
    ty: V,
    body: &'a Tm<'a>,
) -> &'a Tm<'a> {
    let mut names: Vec<(&'a str, Icit)> = Vec::with_capacity(l as usize);
    let mut cur = force(bump, spine, work, vals, icits, defs, metas, decls, mmap, ty);
    for lp in 0..l {
        if v_tag(cur) != 4 {
            unreachable!(); // 类型 Π 层数不足（上游同款不可能）
        }
        let p = v_pi_of(cur);
        let (name, icit, env, body_tm) = (p.name, p.icit, p.env, p.body);
        let name = if name == "_" {
            bump.alloc_str(&format!("x{}", lp))
        } else {
            name
        };
        names.push((name, icit));
        let next = eval_iter(
            bump,
            spine,
            work,
            vals,
            icits,
            defs,
            metas,
            decls,
            mmap,
            env_ext(bump, env, v_lvl(lp)),
            body_tm,
        );
        cur = force(bump, spine, work, vals, icits, defs, metas, decls, mmap, next);
    }
    let mut t = body;
    for (name, icit) in names.iter().rev() {
        t = bump.alloc(Tm::Lam(name, *icit, t));
    }
    t
}

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

/// `pruneVFlex` 的 spine 状态（参考版 `SpinePruneStatus` 同构）。
#[derive(Debug, Clone, Copy, PartialEq)]
enum SpinePruneStatus {
    OKRenaming,
    OKNonRenaming,
    NeedsPruning,
}

/// 稳态复用机（L05 版 + L06 增量：decl 表与可变全局挂在机上——求值 /
/// 引读 / unify 都要按名查；随轮清空并重新注册 builtin）。
pub(crate) struct Machine {
    spine: Spine,
    vals: Vec<V>,
    /// icit 侧栈（eval 右链下降用；跨调用复用容量，进核前 clear）。
    icits: Vec<Icit>,
    /// unify 的判等记忆化 + 实参收集草稿（跨调用复用容量，进核前 clear）。
    conv: ConvScratch,
    /// 平坦环境区域（每轮 append-only，只增不减）。
    defs: Vec<V>,
    pub(crate) metas: Vec<MetaEntry>,
    /// solve 的偏置换换代缓冲（跨求解持久，epoch 换代免逐槽清零）。
    ren: RenBuf,
    /// 名字 → (绑定 lvl, 类型值)：`Raw::Var` 的 O(1) 解析。**只收源码
    /// binder**（bind/define）——inserted binder 不入表。
    name_map: FxHashMap<SmolStr, (u32, V)>,
    /// bind/define 的撤销轨迹：(名字, 旧值)。
    name_trail: Vec<(SmolStr, Option<(u32, V)>)>,
    /// decl 表（L06）：名 → (值, 类型, 可选 builtin prim)。
    decls: FxHashMap<String, DeclEntryF>,
    /// 可变全局（L06）：builtin `create_global` / `change_mutable` 族的
    /// 存取目标。值指向本轮 bump——每轮清空（参考版每次调用新建 Infer）。
    mutable_map: MutableMap,
}

/// unify 的跨调用草稿。
#[derive(Default)]
struct ConvScratch {
    memo: FxHashSet<(u64, u64)>,
    scratch1: Vec<(V, Icit)>,
    scratch2: Vec<(V, Icit)>,
}

const PI_NAME: &str = "x"; // infer App 非 Π 分支合成的闭包名（只服务 pretty）

impl Machine {
    pub(crate) fn new() -> Self {
        Machine {
            spine: Spine {
                stack: Vec::with_capacity(4096),
            },
            vals: Vec::with_capacity(4096),
            icits: Vec::new(),
            conv: ConvScratch::default(),
            defs: Vec::with_capacity(4096),
            metas: Vec::new(),
            ren: RenBuf::default(),
            name_map: FxHashMap::default(),
            name_trail: Vec::new(),
            decls: FxHashMap::default(),
            mutable_map: RefCell::new(FxHashMap::default()),
        }
    }

    /// 每轮 reset：metacontext + 名字表/轨迹/环境区域 + decl 表/可变全局
    /// 全部清空（builtin 的重注册在 [`Machine::prime_round`]）。
    fn clear_round(&mut self) {
        self.metas.clear();
        self.name_map.clear();
        self.name_trail.clear();
        self.defs.clear();
        self.decls.clear();
        self.mutable_map.borrow_mut().clear();
    }

    /// Extend Cxt with a bound variable（源码 binder）。
    #[allow(clippy::too_many_arguments)]
    fn bind_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let key = SmolStr::new(x);
        let prev = self.name_map.insert(key.clone(), (cxt.lvl, ty));
        self.name_trail.push((key, prev));
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: true,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: None,
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
            binds: cxt.binds + 1,
            lvl: cxt.lvl + 1,
            mark: cxt.mark + 1,
        }
    }

    /// Extend Cxt with an inserted implicit binder：**不入名字表**、trail
    /// 不动、mark 不变——但 telescope/pruning 照常扩展。
    fn new_binder<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: false,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: None,
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
            binds: cxt.binds + 1,
            lvl: cxt.lvl + 1,
            mark: cxt.mark,
        }
    }

    /// Extend Cxt with a definition（pruning 记 `None`、telescope 记 Define
    /// 槽）。
    #[allow(clippy::too_many_arguments)]
    fn define_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        t_t: &'a Tm<'a>,
        val: V,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let key = SmolStr::new(x);
        let prev = self.name_map.insert(key.clone(), (cxt.lvl, ty));
        self.name_trail.push((key, prev));
        let env = env_ext_defs(bump, &mut self.defs, cxt.env, val);
        Cxt {
            env,
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: true,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: Some(t_t),
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(None, cxt.pruning))),
            binds: cxt.binds, // define 槽不产生 Π 层
            lvl: cxt.lvl + 1,
            mark: cxt.mark + 1,
        }
    }

    /// 截断撤销轨迹到 `mark`（binder 作用域退出）。
    fn unwind_names(&mut self, mark: u32) {
        while self.name_trail.len() > mark as usize {
            let (key, prev) = self.name_trail.pop().expect("unwind_names: 轨迹为空");
            match prev {
                Some(entry) => {
                    self.name_map.insert(key, entry);
                }
                None => {
                    self.name_map.remove(&key);
                }
            }
        }
    }

    /// 挂新洞（上游 `freshMeta`）：物化闭类型、追加未解条目，产出
    /// `AppPruning ?m (cxt.pruning)`。快捷（L05 三级 + tag 6）：
    /// **`binds == 0`** 时常值类型（U / 裸未解 meta / LiteralType，tag
    /// 3/5/6）闭类型恒等（telescope 只剩 Define 的 Let 层——eval 只往 env
    /// 塞值不添 Π 层）；`quote` 无自由变量则跳过 Let 链直接空环境求值；
    /// 否则全构造（与参考版同形）。
    fn fresh_meta<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, a: V) -> &'a Tm<'a> {
        let mty = if cxt.binds == 0 && matches!(v_tag(a), 3 | 5 | 6) {
            a
        } else {
            let q = self.quote(bump, cxt.lvl, a);
            if cxt.binds == 0 && !has_free_var(q) {
                self.eval(bump, EMPTY_ENV, q)
            } else {
                let closed = self.close_tm(bump, cxt.locals, q);
                self.eval(bump, EMPTY_ENV, closed)
            }
        };
        let m = self.metas.len() as u32;
        self.metas.push(MetaEntry::Unsolved(mty));
        bump.alloc(Tm::AppPruning(bump.alloc(Tm::Meta(m)), cxt.pruning))
    }

    /// 沿 telescope 链闭包（Bind → 显式 Π、Define → Let）。
    fn close_tm<'a>(
        &self,
        bump: &'a Bump,
        mut ls: Option<&'a LCons<'a>>,
        q: &'a Tm<'a>,
    ) -> &'a Tm<'a> {
        let mut b = q;
        while let Some(n) = ls {
            b = match n.t_t {
                None => bump.alloc(Tm::Pi(n.name, Icit::Expl, n.a_t, b)),
                Some(t) => bump.alloc(Tm::Let(n.name, n.a_t, t, b)),
            };
            ls = n.next;
        }
        b
    }

    /// fresh meta 的求值快捷路径：掩码全为 define 槽（或空）时 AppPrun
    /// 走空转，结果恒为裸 meta 立即数——免一次 eval。
    fn eval_fresh(&mut self, bump: &Bump, env: Env, m: &Tm<'_>) -> V {
        if let Tm::AppPruning(CTm_head, pr) = m {
            // 头必须是裸 Meta 才有短路意义
            if let Tm::Meta(mm) = CTm_head {
                if pr.map_or(true, |p| p.slot.is_none() && p.after_run.is_none()) {
                    return v_meta(*mm);
                }
            }
        }
        self.eval(bump, env, m)
    }

    fn eval<'a>(&mut self, bump: &'a Bump, env: Env, tm: &'a Tm<'a>) -> V {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            ..
        } = self;
        eval_iter(
            bump,
            spine,
            &mut Vec::new(),
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            env,
            tm,
        )
    }

    fn quote<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            ..
        } = self;
        quote_iter(
            bump,
            spine,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            level,
            v,
            None,
        )
    }

    /// quote 的记忆化口径（表随本次调用新建，绝不跨 reset 持有）。
    fn quote_memo<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            ..
        } = self;
        let mut memo: QuoteMemo<'a> = FxHashMap::default();
        quote_iter(
            bump,
            spine,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            level,
            v,
            Some(&mut memo),
        )
    }

    fn unify(&mut self, bump: &Bump, l: u32, t: V, u: V) -> bool {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            ren,
            conv,
            ..
        } = self;
        unify_iter(
            bump,
            spine,
            &mut Vec::new(),
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            ren,
            conv,
            l,
            t,
            u,
        )
    }

    /// 错误消息（参考版 `unify_catch` 的 `{:?}` Debug 口径；快版项不含
    /// 源码偏移，span 全零——判定一致，文案数字与参考版有已知偏差）。
    fn unify_catch(&mut self, bump: &Bump, lvl: u32, t: V, t_prime: V) -> Result<(), Error> {
        if self.unify(bump, lvl, t, t_prime) {
            Ok(())
        } else {
            let tq = export(self.quote(bump, lvl, t));
            let uq = export(self.quote(bump, lvl, t_prime));
            Err(Error(format!("can't unify {:?} == {:?}", tq, uq)))
        }
    }

    // 隐式插入（上游 Elaboration.hs 的 insert 族）
    // --------------------------------------------------------------------------------

    /// `insert'`：类型的隐式 Pi 前缀逐个补 fresh meta 实参。
    fn insert_go<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> (&'a Tm<'a>, V) {
        let va = self.force_v(bump, va);
        if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
            let p = v_pi_of(va);
            let m = self.fresh_meta(bump, cxt, p.dom);
            let mv = self.eval_fresh(bump, cxt.env, m);
            let b = {
                let env = env_ext(bump, p.env, mv);
                self.eval(bump, env, p.body)
            };
            let t2 = bump.alloc(Tm::App(t, m, Icit::Impl));
            self.insert_go(bump, cxt, t2, b)
        } else {
            (t, va)
        }
    }

    /// infer 后无条件插入。
    fn insert_t<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        Ok(self.insert_go(bump, cxt, t, va))
    }

    /// infer 后插入，但隐式 lambda 本身免插。
    fn insert<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        if let Tm::Lam(_, Icit::Impl, _) = t {
            Ok((t, va))
        } else {
            self.insert_t(bump, cxt, t, va)
        }
    }

    /// `insertUntilName`：插入到名字匹配的隐式 Pi binder 为止。
    fn insert_until_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        name: &str,
        t: &'a Tm<'a>,
        mut va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        let mut t = t;
        loop {
            let forced = self.force_v(bump, va);
            va = forced;
            if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
                let p = v_pi_of(va);
                if p.name == name {
                    return Ok((t, va));
                }
                let m = self.fresh_meta(bump, cxt, p.dom);
                let mv = self.eval_fresh(bump, cxt.env, m);
                let b = {
                    let env = env_ext(bump, p.env, mv);
                    self.eval(bump, env, p.body)
                };
                t = bump.alloc(Tm::App(t, m, Icit::Impl));
                va = b;
            } else {
                return Err(Error(format!(
                    "no named implicit arg {:?}",
                    empty_span(name.to_owned())
                )));
            }
        }
    }

    /// force 的方法包装（Machine 内 elaboration 侧的散装调用点用；解值
    /// 应用可能 β / 触发 prim——分配一律落本轮 bump）。
    fn force_v(&mut self, bump: &Bump, v: V) -> V {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            ..
        } = self;
        force(
            bump,
            spine,
            &mut Vec::new(),
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            v,
        )
    }

    // 主 check / infer（与参考版 elaboration.rs 逐臂对应）
    // --------------------------------------------------------------------------------

    fn check<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &Raw,
        a: V,
    ) -> Result<&'a Tm<'a>, Error> {
        // force 期望类型后分派（已解 meta 可能展开成 Pi）
        let a = self.force_v(bump, a);
        if let Raw::Lam(x, larg, tbody) = t {
            if v_tag(a) == 4 {
                let p = v_pi_of(a);
                // 参考版首臂的守卫 `(i, i_t) == (Either::Name(x_t), Impl)
                // || i == Either::Icit(i_t)`——Span 的 PartialEq 是**只比
                // data** 的自定义实现（parser_lib.rs），故命名 binder 按
                // 名字匹配（L05 同款语义）
                let matched = match larg {
                    Either::Name(n) => n.data == p.name && p.icit == Icit::Impl,
                    &Either::Icit(j) => j == p.icit,
                };
                if matched {
                    // 命中：按 λ 的 binder 名绑定（源码名，入名字表）
                    let name: &'a str = bump.alloc_str(&x.data);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, env, p.body)
                    };
                    let mark = cxt.mark;
                    let a_t = self.quote(bump, cxt.lvl, p.dom);
                    let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, p.dom);
                    let body = self.check(bump, cxt2, tbody, body_a)?;
                    self.unwind_names(mark);
                    Ok(bump.alloc(Tm::Lam(name, p.icit, body)))
                } else if p.icit == Icit::Impl {
                    // 检查到隐式 Π：补 inserted binder（Pi 侧名字，源码
                    // 不可见），整个项对余定义域重检
                    let name: &'a str = bump.alloc_str(p.name);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, env, p.body)
                    };
                    let mark = cxt.mark;
                    let a_t = self.quote(bump, cxt.lvl, p.dom);
                    let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
                    let body = self.check(bump, cxt2, t, body_a)?;
                    self.unwind_names(mark);
                    Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
                } else {
                    // 显式 Π 上的 icit 失配：回落 general
                    let (t2, tty) = self.infer(bump, cxt, t)?;
                    let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                    self.unify_catch(bump, cxt.lvl, a, tty)?;
                    Ok(t2)
                }
            } else {
                let (t2, tty) = self.infer(bump, cxt, t)?;
                let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                self.unify_catch(bump, cxt.lvl, a, tty)?;
                Ok(t2)
            }
        } else if v_tag(a) == 4 && v_pi_of(a).icit == Icit::Impl {
            // 非 lambda 项检查到隐式 Π：插入隐式 binder
            let p = v_pi_of(a);
            let name: &'a str = bump.alloc_str(p.name);
            let body_a = {
                let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                self.eval(bump, env, p.body)
            };
            let mark = cxt.mark;
            let a_t = self.quote(bump, cxt.lvl, p.dom);
            let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
            let body = self.check(bump, cxt2, t, body_a)?;
            self.unwind_names(mark);
            Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
        } else if let Raw::Let(x, a_ty, t, u) = t {
            let a_tm = self.check(bump, cxt, a_ty, v_u())?;
            let va = self.eval(bump, cxt.env, a_tm);
            let t_tm = self.check(bump, cxt, t, va)?;
            let vt = self.eval(bump, cxt.env, t_tm);
            let name: &'a str = bump.alloc_str(&x.data);
            let mark = cxt.mark;
            let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
            let u_tm = self.check(bump, cxt2, u, a)?;
            self.unwind_names(mark);
            Ok(bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)))
        } else if let Raw::Hole = t {
            // hole：以 fresh meta 填充（类型 = 期望类型）
            Ok(self.fresh_meta(bump, cxt, a))
        } else {
            let (t2, tty) = self.infer(bump, cxt, t)?;
            let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
            self.unify_catch(bump, cxt.lvl, a, tty)?;
            Ok(t2)
        }
    }

    /// 主 `infer`（表达式层；参考版 `infer_expr` 逐臂对应，L06 无 SrcPos）。
    fn infer<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, t: &Raw) -> Result<(&'a Tm<'a>, V), Error> {
        match t {
            Raw::Var(x) => {
                if !NO_NAME_MAP.load(std::sync::atomic::Ordering::Relaxed) {
                    // O(1)：表与 types 链由 bind/define + trail 同步维护
                    if let Some(&(blvl, ty)) = self.name_map.get(x.data.as_str()) {
                        return Ok((bump.alloc(Tm::Var(cxt.lvl - blvl - 1)), ty));
                    }
                } else {
                    // 消融口径：沿 types 链线性找名（跳过 inserted binder）
                    let mut i = 0u32;
                    let mut tys = cxt.types;
                    while let Some(tc) = tys {
                        if tc.source && tc.name == x.data {
                            return Ok((bump.alloc(Tm::Var(i)), tc.ty));
                        }
                        i += 1;
                        tys = tc.next;
                    }
                }
                Err(Error(format!(
                    "error name not in scope: {:?}",
                    empty_span(x.data.clone())
                )))
            }

            Raw::U => Ok((bump.alloc(Tm::U), v_u())),

            Raw::LiteralIntro(l) => Ok((
                bump.alloc(Tm::LiteralIntro(bump.alloc_str(&l.data))),
                v_lit_ty(),
            )),

            // 定义域挂洞；余定义域闭包住当前环境；体推断后在扩展后的
            // 上下文里 insert
            Raw::Lam(x, Either::Icit(i), tbody) => {
                let name: &'a str = bump.alloc_str(&x.data);
                let new_meta = self.fresh_meta(bump, cxt, v_u());
                let a = self.eval_fresh(bump, cxt.env, new_meta);
                let mark = cxt.mark;
                let a_t = self.quote(bump, cxt.lvl, a);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, a);
                let (t, b) = self.infer(bump, cxt2, tbody)?;
                let (t, b) = self.insert(bump, cxt2, t, b)?;
                self.unwind_names(mark);
                // closeVal：quote 在 lvl+1——给即将到来的 binder 留第 0 槽
                let body = self.quote(bump, cxt.lvl + 1, b);
                let cell = bump.alloc(PiCell {
                    name,
                    icit: *i,
                    dom: a,
                    env: cxt.env,
                    body,
                });
                Ok((bump.alloc(Tm::Lam(name, *i, t)), v_pi(cell)))
            }

            Raw::Lam(_, Either::Name(_), _) => Err(Error("infer named lambda".to_owned())),

            Raw::App(t, u, arg) => {
                // 实参分派：命名 → insertUntilName 后按 Impl 应用；
                // 位置 Impl → 直接应用；位置 Expl → 先 insert_t
                let (i, t, tty) = match arg {
                    Either::Name(name) => {
                        let (t, tty) = self.infer(bump, cxt, t)?;
                        let (t, tty) =
                            self.insert_until_name(bump, cxt, &name.data, t, tty)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer(bump, cxt, t)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Expl) => {
                        let (t, tty) = self.infer(bump, cxt, t)?;
                        let (t, tty) = self.insert_t(bump, cxt, t, tty)?;
                        (Icit::Expl, t, tty)
                    }
                };
                let tty = self.force_v(bump, tty);
                let (a, bcell) = if v_tag(tty) == 4 {
                    let p = v_pi_of(tty);
                    if p.icit != i {
                        return Err(Error(format!(
                            "icit mismatch {:?} {:?}",
                            i, p.icit
                        )));
                    }
                    (p.dom, p)
                } else {
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    // 合成 binder（PI_NAME）不进名字表：只延伸 env/telescope/
                    // pruning。注意参数序：期望 = 合成 Π（L06 参考版把合成
                    // Π 放在 unify_catch 的**首位**，与 L05 相反——忠实复刻，
                    // 只影响报错文案方向）。
                    let new_meta = self.fresh_meta(bump, cxt, v_u());
                    let a = self.eval_fresh(bump, cxt.env, new_meta);
                    let a_t = self.quote(bump, cxt.lvl, a);
                    let cxt2 = Cxt {
                        env: env_ext(bump, cxt.env, v_lvl(cxt.lvl)),
                        types: cxt.types,
                        locals: Some(bump.alloc(LCons {
                            name: PI_NAME,
                            a_t,
                            t_t: None,
                            next: cxt.locals,
                        })),
                        pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
                        binds: cxt.binds + 1, // 合成 binder 也是绑定槽
                        lvl: cxt.lvl + 1,
                        mark: cxt.mark,
                    };
                    let cod_meta = self.fresh_meta(bump, cxt2, v_u());
                    let cell = bump.alloc(PiCell {
                        name: PI_NAME,
                        icit: i,
                        dom: a,
                        env: cxt.env,
                        body: cod_meta,
                    });
                    self.unify_catch(bump, cxt.lvl, v_pi(cell), tty)?;
                    (a, &*cell)
                };
                let u = self.check(bump, cxt, u, a)?;
                let arg = self.eval(bump, cxt.env, u);
                // t u : B[x |-> u]
                let ty = {
                    let env = env_ext(bump, bcell.env, arg);
                    self.eval(bump, env, bcell.body)
                };
                Ok((bump.alloc(Tm::App(t, u, i)), ty))
            }

            Raw::Pi(x, i, a, b) => {
                let a_tm = self.check(bump, cxt, a, v_u())?;
                let va = self.eval(bump, cxt.env, a_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let mark = cxt.mark;
                let a_t = self.quote(bump, cxt.lvl, va);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, va);
                let b_tm = self.check(bump, cxt2, b, v_u())?;
                self.unwind_names(mark);
                Ok((bump.alloc(Tm::Pi(name, *i, a_tm, b_tm)), v_u()))
            }

            Raw::Let(x, a_ty, t, u) => {
                let a_tm = self.check(bump, cxt, a_ty, v_u())?;
                let va = self.eval(bump, cxt.env, a_tm);
                let t_tm = self.check(bump, cxt, t, va)?;
                let vt = self.eval(bump, cxt.env, t_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let mark = cxt.mark;
                let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
                let (u_tm, uty) = self.infer(bump, cxt2, u)?;
                self.unwind_names(mark);
                Ok((bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)), uty))
            }

            Raw::Hole => {
                let new_meta = self.fresh_meta(bump, cxt, v_u());
                let a = self.eval_fresh(bump, cxt.env, new_meta);
                let t = self.fresh_meta(bump, cxt, a);
                Ok((t, a))
            }
        }
    }

    /// decl 层的 `infer`（参考版 `Infer::infer(Decl)`）：Def 把参数折叠成
    /// Pi/Lam 后检查，登记 decl 表并 define；Println 推断体（返回引读用）。
    fn infer_decl<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        d: &Decl,
    ) -> Result<(DeclOut<'a>, Cxt<'a>), Error> {
        match d {
            Decl::Def {
                name,
                params,
                ret_type,
                body,
            } => {
                // 参数折叠：typ = Π 参数. 返回类型；bod = λ 参数. 体
                // （与参考版同款在 Raw 层做，一次成本）
                let mut typ = ret_type.clone();
                for (n, a, i) in params.iter().rev() {
                    typ = Raw::Pi(n.clone(), *i, Box::new(a.clone()), Box::new(typ));
                }
                let mut bod = body.clone();
                for (n, _, i) in params.iter().rev() {
                    bod = Raw::Lam(n.clone(), Either::Icit(*i), Box::new(bod));
                }
                let typ_tm = self.check(bump, cxt, &typ, v_u())?;
                let vtyp = self.eval(bump, cxt.env, typ_tm);
                let t_tm = self.check(bump, cxt, &bod, vtyp)?;
                let vt = self.eval(bump, cxt.env, t_tm);
                // decl 表登记（运行期按名取值：string_to_global_type 等）
                self.decls.insert(
                    name.data.clone(),
                    DeclEntryF {
                        vt,
                        va: vtyp,
                        prim: None,
                    },
                );
                let cxt2 = self.define_name(bump, cxt, &name.data, typ_tm, t_tm, vt, vtyp);
                Ok((
                    DeclOut::Def {
                        name: bump.alloc_str(&name.data),
                        vt,
                    },
                    cxt2,
                ))
            }
            Decl::Println(t) => {
                let (tm, _) = self.infer(bump, cxt, t)?;
                Ok((DeclOut::Println(tm), cxt))
            }
        }
    }
}

/// decl 层推断的产出：Def 带名与值（bench 的 nf 口径用），Println 带
/// elaborated 体（run 的 nf 输出用）。
enum DeclOut<'a> {
    Def { name: &'a str, vt: V },
    Println(&'a Tm<'a>),
}

/// 项里是否含自由 `Var`（按 binder 深度算）。`fresh_meta` 快捷路径 2 的
/// 判据（保守：自由 ⇒ 走全构造）。L06 新叶（字面量/类型/名字）无变量。
fn has_free_var(t: &Tm<'_>) -> bool {
    let mut stack: Vec<(&Tm<'_>, u32)> = vec![(t, 0)];
    while let Some((x, d)) = stack.pop() {
        match x {
            Tm::Var(i) => {
                if *i >= d {
                    return true;
                }
            }
            Tm::Lam(_, _, b) => stack.push((b, d + 1)),
            Tm::App(f, a, _) => {
                stack.push((f, d));
                stack.push((a, d));
            }
            Tm::AppPruning(h, _) => stack.push((h, d)),
            Tm::U | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) | Tm::Decl(_) => {}
            Tm::Pi(_, _, a, b) => {
                stack.push((a, d));
                stack.push((b, d + 1));
            }
            Tm::Let(_, a, t, u) => {
                stack.push((a, d));
                stack.push((t, d));
                stack.push((u, d + 1));
            }
        }
    }
    false
}

/// Elaboration 上下文（全 Copy，绑定量在 bump 里）。L06 无位置跟踪
/// （错误不带 span 位置，`Error(String)`）。
#[derive(Clone, Copy)]
struct Cxt<'a> {
    env: Env<'a>,
    /// type of every variable in scope（头 = 最内层；`source` 标记源码
    /// binder——消融口径的线性找名跳过非源码条目；println 的 pretty 名
    /// 单也走这里，与参考版 `Cxt::names()` 的 locals 序一致）。
    types: Option<&'a TCons<'a>>,
    /// telescope（上游 `cxtLocals`）：fresh_meta 闭类型用。
    locals: Option<&'a LCons<'a>>,
    /// fresh meta 的 scope 掩码（与 env 平行；头 = 最内层）。
    pruning: Option<&'a PrCons<'a>>,
    /// 绑定层数（bind/new_binder/synth +1，define 不动）。
    binds: u32,
    lvl: u32,
    /// 名字撤销轨迹的本上下文基线（inserted binder 不留轨迹、不动 mark）。
    mark: u32,
}

/// scope 里的一项：名字 + 类型值 + 来源（源码 binder / inserted binder）。
struct TCons<'a> {
    name: &'a str,
    ty: V,
    source: bool,
    next: Option<&'a TCons<'a>>,
}

impl<'a> Cxt<'a> {
    fn empty() -> Self {
        Cxt {
            env: EMPTY_ENV,
            types: None,
            locals: None,
            pruning: None,
            binds: 0,
            lvl: 0,
            mark: 0,
        }
    }
}

/// types 链 → 参考版 pretty 的名字 List（头 = 最内层；List::prepend 从尾
/// 起构回，序不变）。
fn types_names_list(tys: Option<&TCons<'_>>) -> crate::list::List<String> {
    let mut ns: Vec<String> = Vec::new();
    let mut cur = tys;
    while let Some(tc) = cur {
        ns.push(tc.name.to_owned());
        cur = tc.next;
    }
    let mut list = crate::list::List::new();
    for n in ns.into_iter().rev() {
        list = list.prepend(n);
    }
    list
}

// builtin 注册（每轮 prime；参考版 `Cxt::new` + `add_builtin` 逐条对应）
// --------------------------------------------------------------------------------

impl Machine {
    /// `(String ->)^n ret` —— L06 builtin 的参数类型全为 String。
    fn str_pi<'a>(bump: &'a Bump, params: &[&str], ret: &'a Tm<'a>) -> &'a Tm<'a> {
        let mut t = ret;
        for name in params.iter().rev() {
            t = bump.alloc(Tm::Pi(
                bump.alloc_str(name),
                Icit::Expl,
                bump.alloc(Tm::LiteralType),
                t,
            ));
        }
        t
    }

    /// `(name : dom) -> cod`。
    fn tm_pi<'a>(bump: &'a Bump, name: &str, dom: &'a Tm<'a>, cod: &'a Tm<'a>) -> &'a Tm<'a> {
        bump.alloc(Tm::Pi(bump.alloc_str(name), Icit::Expl, dom, cod))
    }

    /// `string_to_global_type Var(ix)`（de Bruijn 引用前序参数）。
    fn st2g_app<'a>(bump: &'a Bump, ix: u32) -> &'a Tm<'a> {
        bump.alloc(Tm::App(
            bump.alloc(Tm::Decl(bump.alloc_str("string_to_global_type"))),
            bump.alloc(Tm::Var(ix)),
            Icit::Expl,
        ))
    }

    /// 每轮注册（参考版 `Cxt::new(&mut infer)`）：String 类型进 decl 表并
    /// define；全组 builtin 登记（值 = 卡住 Decl 头，应用时触发 prim）+
    /// 位置 define（源码可用名）。**注册顺序与参考版一致**——
    /// create_global 等的类型引用 `string_to_global_type`，须先登记。
    fn prime_round<'a>(&mut self, bump: &'a Bump) -> Cxt<'a> {
        let mut cxt = Cxt::empty();
        // String
        self.decls.insert(
            "String".to_owned(),
            DeclEntryF {
                vt: v_lit_ty(),
                va: v_u(),
                prim: None,
            },
        );
        let u_tm: &'a Tm<'a> = bump.alloc(Tm::U);
        let lit_ty_tm: &'a Tm<'a> = bump.alloc(Tm::LiteralType);
        cxt = self.define_name(
            bump,
            cxt,
            "String",
            u_tm,
            lit_ty_tm,
            v_lit_ty(),
            v_u(),
        );
        // builtin 组（名, 类型项, prim）——与参考版 Cxt::new 同序
        let lit_ty = bump.alloc(Tm::LiteralType);
        let u_t = bump.alloc(Tm::U);
        let builtins: Vec<(&str, &'a Tm<'a>, Prim)> = vec![
            ("string_concat", Self::str_pi(bump, &["x", "y"], lit_ty), Prim::StrConcat),
            ("str_eq", Self::str_pi(bump, &["x", "y"], lit_ty), Prim::StrEq),
            ("str_indent2", Self::str_pi(bump, &["x"], lit_ty), Prim::StrIndent2),
            (
                "report_check_issue",
                Self::str_pi(bump, &["code", "module", "signal", "message"], u_t),
                Prim::ReportCheckIssue,
            ),
            (
                "string_to_global_type",
                Self::str_pi(bump, &["x"], u_t),
                Prim::StringToGlobalType,
            ),
            (
                "create_global",
                Self::tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    Self::tm_pi(bump, "y", Self::st2g_app(bump, 0), u_t),
                ),
                Prim::CreateGlobal,
            ),
            (
                "change_mutable",
                Self::tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    Self::tm_pi(
                        bump,
                        "f",
                        Self::tm_pi(bump, "_", Self::st2g_app(bump, 0), Self::st2g_app(bump, 1)),
                        u_t,
                    ),
                ),
                Prim::ChangeMutable,
            ),
            (
                "get_global",
                Self::tm_pi(bump, "x", lit_ty, Self::st2g_app(bump, 0)),
                Prim::GetGlobal,
            ),
            (
                "get_global_default",
                Self::tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    Self::tm_pi(bump, "z", Self::st2g_app(bump, 0), Self::st2g_app(bump, 1)),
                ),
                Prim::GetGlobalDefault,
            ),
            (
                "change_mutable_default",
                Self::tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    Self::tm_pi(
                        bump,
                        "f",
                        Self::tm_pi(bump, "_", Self::st2g_app(bump, 0), Self::st2g_app(bump, 1)),
                        Self::tm_pi(bump, "z", Self::st2g_app(bump, 1), u_t),
                    ),
                ),
                Prim::ChangeMutableDefault,
            ),
            (
                "file_read_all_text",
                Self::str_pi(bump, &["path"], lit_ty),
                Prim::FileReadAllText,
            ),
            (
                "file_write_all_text",
                Self::str_pi(bump, &["path", "content"], u_t),
                Prim::FileWriteAllText,
            ),
            (
                "file_append_all_text",
                Self::str_pi(bump, &["path", "content"], u_t),
                Prim::FileAppendAllText,
            ),
            (
                "file_exists",
                Self::str_pi(bump, &["path"], lit_ty),
                Prim::FileExists,
            ),
            (
                "file_delete",
                Self::str_pi(bump, &["path"], u_t),
                Prim::FileDelete,
            ),
        ];
        for (name, ty, prim) in builtins {
            let va = self.eval(bump, EMPTY_ENV, ty);
            let head = v_xcell(bump.alloc(XCell::Decl(bump.alloc_str(name))));
            self.decls.insert(
                name.to_owned(),
                DeclEntryF {
                    vt: head,
                    va,
                    prim: Some(prim),
                },
            );
            let name_tm: &'a Tm<'a> = bump.alloc(Tm::Decl(bump.alloc_str(name)));
            cxt = self.define_name(bump, cxt, name, ty, name_tm, head, va);
        }
        cxt
    }

    /// 参考版 `run` 的主循环（无输出变体，bench 用）：返回 (是否通过，
    /// 最后一个 def 的名与值)。
    fn elab_all<'a>(
        &mut self,
        bump: &'a Bump,
        ast: &[Decl],
    ) -> (Result<(), Error>, Option<(&'a str, V)>) {
        let mut cxt = self.prime_round(bump);
        let mut last = None;
        for d in ast {
            match self.infer_decl(bump, cxt, d) {
                Ok((out, nc)) => {
                    if let DeclOut::Def { name, vt } = out {
                        last = Some((name, vt));
                    }
                    cxt = nc;
                }
                Err(e) => return (Err(e), last),
            }
        }
        (Ok(()), last)
    }
}

// export 与对外入口
// --------------------------------------------------------------------------------

/// 把 bump 结果项转回参考版的 `Box` 树（迭代任务栈；icit/掩码随任务
/// 携带），复用参考版的 pretty。L06 新叶的 span 全零（内容即输出）。
fn export(t: &Tm<'_>) -> CTm {
    use crate::list::List as CList;
    use super::parser::syntax::Icit as PIcit;
    use CTm as B;
    enum J<'a> {
        Do(&'a Tm<'a>),
        Lam2(&'a str, PIcit),
        Pi2(&'a str, PIcit),
        Let2(&'a str),
        App2(PIcit),
        AppPrun2(CList<Option<PIcit>>),
    }
    fn name(x: &str) -> crate::parser_lib::Span<String> {
        empty_span(x.to_owned())
    }
    let mut tasks: Vec<J<'_>> = vec![J::Do(t)];
    let mut done: Vec<CTm> = Vec::new();
    while let Some(j) = tasks.pop() {
        match j {
            J::Do(Tm::Var(i)) => done.push(B::Var(Ix(*i))),
            J::Do(Tm::Lam(x, i, b)) => {
                tasks.push(J::Lam2(x, *i));
                tasks.push(J::Do(b));
            }
            J::Do(Tm::App(f, a, i)) => {
                tasks.push(J::App2(*i));
                tasks.push(J::Do(a));
                tasks.push(J::Do(f));
            }
            J::Do(Tm::AppPruning(h, pr)) => {
                // bds 持久链表（头 = 最内层）→ 参考版 List<Option<Icit>>（同序）
                let mut vec: Vec<Option<PIcit>> = Vec::new();
                let mut cur = *pr;
                while let Some(b) = cur {
                    vec.push(b.slot);
                    cur = b.next;
                }
                let mut list: CList<Option<PIcit>> = CList::new();
                for s in vec.into_iter().rev() {
                    list = list.prepend(s);
                }
                tasks.push(J::AppPrun2(list));
                tasks.push(J::Do(h));
            }
            J::Do(Tm::U) => done.push(B::U),
            J::Do(Tm::Pi(x, i, a, b)) => {
                tasks.push(J::Pi2(x, *i));
                tasks.push(J::Do(b));
                tasks.push(J::Do(a));
            }
            J::Do(Tm::Let(x, a, t, u)) => {
                tasks.push(J::Let2(x));
                tasks.push(J::Do(u));
                tasks.push(J::Do(t));
                tasks.push(J::Do(a));
            }
            J::Do(Tm::Meta(m)) => done.push(B::Meta(super::MetaVar(*m))),
            J::Do(Tm::LiteralType) => done.push(B::LiteralType),
            J::Do(Tm::LiteralIntro(s)) => done.push(B::LiteralIntro(name(s))),
            J::Do(Tm::Decl(s)) => done.push(B::Decl(name(s))),
            J::Lam2(x, i) => {
                let b = done.pop().expect("export 栈：Lam 缺体");
                done.push(B::Lam(name(x), i, Box::new(b)));
            }
            J::Pi2(x, i) => {
                let cod = done.pop().expect("export 栈：Pi 缺余定义域");
                let dom = done.pop().expect("export 栈：Pi 缺定义域");
                done.push(B::Pi(name(x), i, Box::new(dom), Box::new(cod)));
            }
            J::Let2(x) => {
                let u = done.pop().expect("export 栈：Let 缺体");
                let t = done.pop().expect("export 栈：Let 缺值");
                let a = done.pop().expect("export 栈：Let 缺类型");
                done.push(B::Let(name(x), Box::new(a), Box::new(t), Box::new(u)));
            }
            J::App2(i) => {
                let a = done.pop().expect("export 栈：App 缺实参");
                let f = done.pop().expect("export 栈：App 缺函数");
                done.push(B::App(Box::new(f), Box::new(a), i));
            }
            J::AppPrun2(pr) => {
                let h = done.pop().expect("export 栈：AppPruning 缺头");
                done.push(B::AppPruning(Box::new(h), pr));
            }
        }
    }
    done.pop().expect("export 必须恰有一个根")
}

fn tm_size(t: &Tm<'_>) -> u64 {
    let mut stack: Vec<&Tm<'_>> = vec![t];
    let mut n = 0u64;
    while let Some(x) = stack.pop() {
        n += 1;
        match x {
            Tm::Var(_) | Tm::U | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_)
            | Tm::Decl(_) => {}
            Tm::Lam(_, _, b) => stack.push(b),
            Tm::App(f, a, _) => {
                stack.push(f);
                stack.push(a);
            }
            Tm::AppPruning(h, pr) => {
                stack.push(h);
                let mut cur = *pr;
                while let Some(b) = cur {
                    n += 1;
                    cur = b.next;
                }
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
        }
    }
    n
}

/// A/B 实验开关（Raw::Var 名字解析消融）：置 `L06_NO_NAME_MAP=1` 回落为
/// 沿 `types` 链的线性找名（`=0` 不关闭）。
static NO_NAME_MAP: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L06_NO_NAME_MAP").is_ok_and(|v| v != "0"))
    });

/// 稳态类型检查器（同 L03-L05：owns 反复 `reset` 的 `Bump` 与跨调用复用
/// 的 [`Machine`]）。
pub(crate) struct Tycker {
    bump: Bump,
    machine: Machine,
}

impl Tycker {
    pub(crate) fn new() -> Self {
        Tycker {
            bump: Bump::with_capacity(1 << 20),
            machine: Machine::new(),
        }
    }

    /// 参考版 `run` 的等价物：preprocess + parse 由调用方完成（与参考版
    /// 共用 parser），本方法做轮重置 + builtin 重注册 + 逐 decl 推断，
    /// println 的 nf 经 pretty 输出（quote 走记忆化口径——与无记忆化
    /// 输出逐字节一致，L03-L05 已证）。
    pub(crate) fn run_decls(&mut self, ast: &[Decl]) -> Result<String, Error> {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut ret = String::new();
        for d in ast {
            let (out, nc) = self.machine.infer_decl(bump, cxt, d)?;
            cxt = nc;
            if let DeclOut::Println(t) = out {
                let v = self.machine.eval(bump, cxt.env, t);
                let q = self.machine.quote_memo(bump, cxt.lvl, v);
                let names = types_names_list(cxt.types);
                ret += &pretty::pretty_tm(0, names, &export(q));
                ret += "\n";
            }
        }
        Ok(ret)
    }

    /// 参考版 `run` 的全流程等价物（含 preprocess/parse）。
    pub(crate) fn run_input(&mut self, input: &str, path_id: u32) -> Result<String, Error> {
        let ast = super::parser::parser(&super::preprocess(input), path_id).unwrap();
        self.run_decls(&ast)
    }

    /// 基准口径（bench 用）：仅 elaborate。
    pub(crate) fn bench_check(&mut self, ast: &[Decl]) -> bool {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        self.machine.elab_all(bump, ast).0.is_ok()
    }

    /// 基准口径：check + nf（最后一个 def 的登记值空层级引读），返回
    /// 结果树节点数。
    pub(crate) fn bench_check_nf(&mut self, ast: &[Decl]) -> u64 {
        self.bench_nf_impl(ast, false)
    }

    /// [`Tycker::bench_check_nf`] 的 quote 记忆化口径。
    pub(crate) fn bench_check_nf_memo(&mut self, ast: &[Decl]) -> u64 {
        self.bench_nf_impl(ast, true)
    }

    fn bench_nf_impl(&mut self, ast: &[Decl], use_memo: bool) -> u64 {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        let (r, last) = self.machine.elab_all(bump, ast);
        if r.is_err() {
            return 0;
        }
        let Some((_, vt)) = last else {
            return 0;
        };
        let q = if use_memo {
            self.machine.quote_memo(bump, 0, vt)
        } else {
            self.machine.quote(bump, 0, vt)
        };
        tm_size(q)
    }
}

/// 一次性口径入口（与参考版 `run` 同签名同 Ok 输出）。
pub(crate) fn run_fast(input: &str, path_id: u32) -> Result<String, Error> {
    let mut tycker = Tycker::new();
    tycker.run_input(input, path_id)
}

// 基准负载生成器（l06bench 共用；L05 全家桶的 L06 语法版 + string 特色负载）
// --------------------------------------------------------------------------------

/// church 2^(k+1)：k 次 ×2 翻倍（`add p p`）的 def 链，末位 def 为 `p_k`
/// （L06 顶层是 decl 序列：**无尾表达式行、def 无分号**——parser 只取
/// decl 前缀，多余 token 会把后续 println 截掉；nf 节点数 = 2n + 4）。
pub(crate) fn church_src(k: u32) -> String {
    let mut s = String::from(
        "def Nat : U = (N : U) -> (N -> N) -> N -> N\n\
         def add : Nat -> Nat -> Nat = a => b => N => s => z => a N s (b N s z)\n\
         def p0 : Nat = N => s => z => s (s z)\n",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}\n", i - 1, i - 1);
    }
    s
}

/// implicit 2^(k+1)（L04/L05 同款链的 L06 版）：每层 `id p_{i-1}` 触发一次
/// 隐式插入 + 一次求解——插入口的 fresh meta 类型恒为 `U`（tag 3 快捷
/// 全命中），掩码全 define 槽（eval_fresh 跳段）。
pub(crate) fn implicit_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "def Nat : U = (N : U) -> (N -> N) -> N -> N\n\
         def id [A : U] : A -> A = x => x\n\
         def p0 : Nat = N => s => z => s (s z)\n",
    );
    for i in 1..n {
        s += &format!("def p{i} : Nat = id p{}\n", i - 1);
    }
    s
}

/// prune 2^(k+1)（L05 特色负载的 L06 版）：每层 `m_i`（洞类型
/// `(A : U)(B : U) -> U -> U -> U`）+ `t_i` 的 `m_i a a` 非线性 spine——
/// invert 的重复变量掩码 + prune_ty 验证 + solve。
pub(crate) fn prune_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "def Eq [A : U] (x : A, y : A) : U = (P : A -> U) -> P x -> P y\n\
         def refl [A : U, x : A] : Eq[A] x x = P => px => px\n\
         def the (A : U)(x : A) : A = x\n",
    );
    for i in 0..n {
        s += &format!(
            "def m{i} : (A : U)(B : U) -> U -> U -> U = _\n\
             def t{i} = a => b => the (Eq (m{i} a a) (x => y => y)) refl\n"
        );
    }
    s
}

/// solve 2^(k+1)：`Eq _ p_k p_k = refl _ _`——rename 沿 church 展开的整条
/// neutral 链走的主展示负载。
pub(crate) fn solve_src(k: u32) -> String {
    let mut s = String::from(
        // Eq/refl 都用**显式**参数（L05 solve 负载同款）：`Eq _ p_k p_k` 与
        // `refl _ _` 的显式实参恰好填满，洞走 unify 求解（隐式版会先走
        // insert 造出头是 meta 的应用，invert 非模式而失败）
        "def Nat : U = (N : U) -> (N -> N) -> N -> N\n\
         def add : Nat -> Nat -> Nat = a => b => N => s => z => a N s (b N s z)\n\
         def Eq (A : U)(x : A, y : A) : U = (P : A -> U) -> P x -> P y\n\
         def refl (A : U)(x : A) : Eq A x x = P => px => px\n\
         def p0 : Nat = N => s => z => s (s z)\n",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}\n", i - 1, i - 1);
    }
    s += &format!("def eqTest : Eq _ p{k} p{k} = refl _ _\n");
    s
}

/// strchain 2^(k+1)（**L06 特色负载**）：每层 `string_concat s_{i-1} "x"`
/// ——define 链 + decl 表增长 + 每层一次 builtin prim 触发（字面量拼接），
/// 末值是长度 n 的字面量（nf 节点数 = 1）。
pub(crate) fn strchain_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from("def s0 : String = \"x\"\n");
    for i in 1..n {
        s += &format!("def s{i} : String = string_concat s{} \"x\"\n", i - 1);
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::FILE_IO_LOCK;

    /// Ok 输出逐字节互检；Err 判定互检（错误文案的 Debug-span 偏移是已知
    /// 偏差，不比内容）。
    fn assert_parity(src: &str) {
        let basic = super::super::run(src, 0);
        let fast = run_fast(src, 0);
        match (&basic, &fast) {
            (Ok(b), Ok(f)) => assert_eq!(
                b, f,
                "Ok 输出不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
            ),
            (Err(_), Err(_)) => {}
            _ => panic!(
                "判定不一致（basic={:?}, fast={:?}），src:\n{src}",
                basic.map(|_| ".."),
                fast.map(|_| "..")
            ),
        }
    }

    /// DEMO_SRC 全量互检（pruning + 字面量 + builtin 注册表 + decl 表 +
    /// 可变全局 + 文件 IO——两个实现先后跑，各自写删同一文件，幂等）。
    /// 文件 IO 用固定文件名，相关测试经 `FILE_IO_LOCK` 串行（并行线程下
    /// Windows 的文件句柄竞争会让删除报 os error 5）。
    #[test]
    fn parity_on_demo_src() {
        let _guard = FILE_IO_LOCK.lock().unwrap();
        assert_parity(super::super::DEMO_SRC);
    }

    /// 剪枝样例束（L05 EX1 的 L06 语法版）。
    #[test]
    fn parity_on_pruning_examples() {
        for src in [
            "def pr1 = f => x => f x;\nprintln pr1\n",
            "def pr2 = f => x => y => f x y;\nprintln pr2\n",
            "def pr3 = f => f U;\nprintln pr3\n",
            "def m : (A : U)(B : U) -> U -> U -> U = _;\n\
             def the (A : U)(x : A) : A = x;\n\
             def test = a => b => the (Eq (m a a) (x => y => y)) refl;\n\
             println test\n",
            "def m : U -> U -> U -> U = _;\n\
             def the (A : U)(x : A) : A = x;\n\
             def test = a => b => c => the (Eq (m a b c) (m c b a)) refl;\n\
             println test\n",
        ] {
            assert_parity(src);
        }
    }

    /// 字面量 + builtin 全组（部分应用卡住、同名 stuck decl 的 unify、
    /// str_eq 的真假、indent）。
    #[test]
    fn parity_on_string_builtins() {
        for src in [
            "def s : String = string_concat \"hello \" \"world\"\nprintln s\n",
            // 部分应用：卡住的 Decl 头（quote 成 `string_concat x` 形态）
            "def f = s => string_concat s\nprintln f\n",
            // 卡住 decl 与 String 类型的 unify（get_global 的返回类型）
            "def st : U = string_to_global_type \"String\"\nprintln st\n",
            "def st : U = string_to_global_type \"Missing\"\nprintln st\n",
            "def eq1 = str_eq \"foo\" \"foo\"\nprintln eq1\n",
            "def eq2 = str_eq \"foo\" \"bar\"\nprintln eq2\n",
            "def ind = str_indent2 \"line1\nline2\"\nprintln ind\n",
        ] {
            assert_parity(src);
        }
    }

    /// 命名 λ：按名字匹配 Π binder（Span 的 PartialEq 只比 data——与参考
    /// 版/L05 同款语义）。L06 λ 语法无反斜杠：binder 组 + `=>`。
    #[test]
    fn named_lambda_matches_by_name() {
        // 名字命中：elaborated binder 用 λ 侧的 binder 名（a）
        assert_parity(
            "def f : [A : U] -> A -> A = [A = a] x => x\n\
             println f\n",
        );
        // 名字未命中：按 Π 名补 inserted binder（A）
        assert_parity(
            "def g : [A : U] -> A -> A = [B = b] y => y\n\
             println g\n",
        );
    }

    /// 报错路径：判定一致（文案含 span 偏移为已知偏差）。
    #[test]
    fn error_parity() {
        for src in [
            "println nope\n",
            "def g : U -> U -> U = x => y => x\nprintln (g U)\n", // icit 失配
            "def h = [B = x] y => y\nprintln h\n",                // 命名 λ 不可推断
            "def bad : U = \"not a type\"\nprintln bad\n",        // Lit vs U
        ] {
            assert_parity(src);
        }
    }

    /// 深负载：church k=12 的 elaborate 判定一致（8192 层），strchain 512。
    #[test]
    fn deep_workloads() {
        let src = church_src(12);
        let Some(raw) = super::super::parser::parser(&super::super::preprocess(&src), 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert!(t.bench_check(&raw), "church k=12 未通过");
        assert_eq!(t.bench_check_nf_memo(&raw), 2 * (1u64 << 13) + 4, "nf 节点数");

        let src = strchain_src(9);
        let Some(raw) = super::super::parser::parser(&super::super::preprocess(&src), 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert!(t.bench_check(&raw), "strchain 未通过");
        assert_eq!(t.bench_check_nf_memo(&raw), 1, "strchain nf 节点数");
        // 与参考版逐字节（含 println 输出）
        let src_print = strchain_src(5) + "println s0\n";
        let basic = super::super::run(&src_print, 0).unwrap();
        assert_eq!(run_fast(&src_print, 0).unwrap(), basic);
    }

    /// 稳态复用正确性：同一 Tycker 连续多轮（含 mutable_map / decl 表的
    /// 轮清空），输出与每轮新建的一致。
    #[test]
    fn steady_state_reuse() {
        let _guard = FILE_IO_LOCK.lock().unwrap();
        let src = super::super::DEMO_SRC;
        let mut steady = Tycker::new();
        let r1 = steady.run_input(src, 0).unwrap();
        let r2 = steady.run_input(src, 0).unwrap();
        let fresh = run_fast(src, 0).unwrap();
        assert_eq!(r1, r2, "稳态两轮不一致");
        assert_eq!(r1, fresh, "稳态与一次性不一致");
    }

    /// 判等记忆化消融口径输出一致。
    #[test]
    fn ablation_env_off_by_default() {
        assert!(!NO_CONV_MEMO.load(std::sync::atomic::Ordering::Relaxed));
        assert!(!NO_NAME_MAP.load(std::sync::atomic::Ordering::Relaxed));
    }
}
