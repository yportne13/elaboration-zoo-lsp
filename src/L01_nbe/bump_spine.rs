//! `bump_tree` 的值表示 + quote 改造（`bump_spine`）：沿两条轴再压常数因子。
//!
//! 1. **打包值**：`Bv`（24B 枚举）换成 64 位字 [`V`]，tag 塞在低位
//!    （bump 分配天然 8 字节对齐，level/spine 下标走立即数编码）。
//!    值拷贝、env 节点、中性节点全部减半以上。
//! 2. **扁平中性 + 流式 quote**：中性的 `App` 不再逐节点 bump 分配二叉
//!    单元，而是压进一条 spine 栈（[`Entry`]，顺序内存）；quote 检测
//!    **右嵌套链**（`f (f (f x))`，church 数正态形的形状）后**从内向外
//!    顺序扫描**：自底向上分配结果树，消除树式 quote 的指针追逐
//!    （依赖式 load 链在 n ≥ 8000、中性树超出 L2 时是主要延迟来源）。
//!
//! 项表示复用 [`super::bump_arena::Bt`]（指针树；`compiled` 已实测数组式
//! 项访问更慢）。eval/quote 保持递归（与 `bump_tree` 同深度级别）。
//!
//! ```text
//! V(u64)   00=Level(level<<2)  01=Clo(ptr)  10=Spine(idx<<2)
//! CloCell  { env: Option<&EnvCons>, body: &Bt }   // 16B
//! EnvCons  { val: V, next: Option<&EnvCons> }     // 16B（持久链表）
//! Entry    { f: V, a: V, len: u32, base: u32 }     // 24B，spine 栈槽
//!          len  = 以本条目为链尾的右嵌套链长度
//!          base = 链最内层条目的下标（连续性校验）
//! ```
//!
//! 连续性引理（quote 流式路径的正确性依据）：`Entry.len` 按构造继承
//! （延续链则 `prev.len + 1`），故 `base + len - 1 == idx` 当且仅当链上
//! 各条目下标恰为 `base..=idx` 连续——此时可按下标顺序自底向上重建。

use bumpalo::Bump;

use super::bump_arena::{self, Bt};
use super::term::Term;

/// 打包值：tag 在低 2 位（bump 指针 8 字节对齐，低位空闲）。
#[derive(Clone, Copy)]
pub(crate) struct V(pub(crate) u64);

#[inline]
pub(crate) fn v_lvl(level: usize) -> V {
    V(((level as u64) << 2) | 0)
}
#[inline]
pub(crate) fn v_clo<'a>(p: &'a CloCell<'a>) -> V {
    V((p as *const _ as u64) | 1)
}
#[inline]
pub(crate) fn v_spine(idx: usize) -> V {
    V(((idx as u64) << 2) | 2)
}
#[inline]
pub(crate) fn v_tag(v: V) -> u64 {
    v.0 & 3
}
#[inline]
pub(crate) fn v_lvl_of(v: V) -> usize {
    (v.0 >> 2) as usize
}
#[inline]
pub(crate) fn v_clo_of<'a>(v: V) -> &'a CloCell<'a> {
    unsafe { &*((v.0 & !3) as *const CloCell) }
}
#[inline]
pub(crate) fn v_spine_of(v: V) -> usize {
    (v.0 >> 2) as usize
}

/// 闭包单元：env + 体。
pub(crate) struct CloCell<'a> {
    pub(crate) env: Option<&'a EnvCons<'a>>,
    pub(crate) body: &'a Bt<'a>,
}

/// 环境节点（持久链表）。
pub(crate) struct EnvCons<'a> {
    pub(crate) val: V,
    pub(crate) next: Option<&'a EnvCons<'a>>,
}

/// spine 栈槽：一次中性应用。`len`/`base` 支撑流式右链 quote。
pub(crate) struct Entry {
    pub(crate) f: V,
    pub(crate) a: V,
    pub(crate) len: u32,
    pub(crate) base: u32,
}

/// 求值机持有的扁平中性栈（只增不减，槽位下标即句柄）。
pub(crate) struct Spine {
    pub(crate) stack: Vec<Entry>,
}

impl Spine {
    /// 中性应用 `f a` 压栈，返回句柄值。
    #[inline]
    pub(crate) fn push(&mut self, f: V, a: V) -> V {
        let idx = self.stack.len();
        // a 若是 spine 句柄，则本条目延续它的右链（len+1、base 继承）；
        // 否则自成新链（len=1、base=自己）。
        let (len, base) = if v_tag(a) == 2 {
            let prev = &self.stack[v_spine_of(a)];
            (prev.len + 1, prev.base)
        } else {
            (1, idx as u32)
        };
        self.stack.push(Entry { f, a, len, base });
        v_spine(idx)
    }
}

#[inline]
pub(crate) fn nth<'a>(mut env: Option<&'a EnvCons<'a>>, idx: usize) -> V {
    for _ in 0..idx {
        env = env.expect("de Bruijn 越界：闭项不应查空环境").next;
    }
    env.expect("de Bruijn 越界：闭项不应查越深").val
}

/// eval（与 `bump_arena::eval` 同语义：先函数后实参）。
pub(crate) fn eval<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    env: Option<&'a EnvCons<'a>>,
    tm: &'a Bt<'a>,
) -> V {
    match tm {
        Bt::Idx(i) => nth(env, *i),
        Bt::Lam(body) => {
            let c = bump.alloc(CloCell { env, body });
            v_clo(c)
        },
        Bt::App(f, a) => {
            let vf = eval(bump, spine, env, f);
            let va = eval(bump, spine, env, a);
            if v_tag(vf) == 1 {
                let c = v_clo_of(vf);
                let node = bump.alloc(EnvCons { val: va, next: c.env });
                eval(bump, spine, Some(node), c.body)
            } else {
                spine.push(vf, va)
            }
        },
    }
}

/// quote level value（与 `bump_tree::quote_bump` 同语义）。
/// Spine 分支：`base + len - 1 == idx`（链连续）时流式自底向上；
/// 否则按二叉节点递归（链被其他求值穿插时的等价慢路径）。
fn quote<'a>(bump: &'a Bump, spine: &mut Spine, level: usize, v: V) -> &'a Bt<'a> {
    match v_tag(v) {
        0 => bump.alloc(Bt::Idx(level - v_lvl_of(v) - 1)),
        1 => {
            let c = v_clo_of(v);
            let node = bump.alloc(EnvCons { val: v_lvl(level), next: c.env });
            let body = eval(bump, spine, Some(node), c.body);
            let t = quote(bump, spine, level + 1, body);
            bump.alloc(Bt::Lam(t))
        },
        _ => {
            // 先拷出标量再递归：quote 的重入会 push spine（Vec 可能扩容）
            let (ef, ea, len, base) = {
                let e = &spine.stack[v_spine_of(v)];
                (e.f, e.a, e.len, e.base)
            };
            let h = v_spine_of(v);
            if len > 1 && base as usize + len as usize - 1 == h {
                // 连续右链：base 起按下标顺序扫到 h，自底向上搭结果树。
                // 链头全是同一个变量（church 链的形状）时 Idx 节点只分配一次。
                let mut prev = quote(bump, spine, level, spine.stack[base as usize].a);
                let f0 = spine.stack[base as usize].f;
                let idx_node = if v_tag(f0) == 0 {
                    Some(&*bump.alloc(Bt::Idx(level - v_lvl_of(f0) - 1)))
                } else {
                    None
                };
                for i in base as usize..=h {
                    let fi = spine.stack[i].f;
                    let f_node = match idx_node {
                        Some(n) if fi.0 == f0.0 => n,
                        _ => quote(bump, spine, level, fi),
                    };
                    prev = bump.alloc(Bt::App(f_node, prev));
                }
                prev
            } else {
                let f = quote(bump, spine, level, ef);
                let a = quote(bump, spine, level, ea);
                bump.alloc(Bt::App(f, a))
            }
        },
    }
}

/// 对已导入 bump 的项做 NBE（基准计时对象；import 在计时外）。
pub(crate) fn normalize_imported<'a>(bump: &'a Bump, tm: &'a Bt<'a>) -> &'a Bt<'a> {
    // 预保留：中性应用数与项的 App 节点数同阶，避免长链下 Vec 倍增拷贝
    let mut spine = Spine { stack: Vec::with_capacity(4096) };
    let v = eval(bump, &mut spine, None, tm);
    quote(bump, &mut spine, 0, v)
}

/// 便捷入口：import + normalize 一步完成（计时含转换成本）。
pub(crate) fn normalize(t: Term) -> Term {
    let bump = Bump::new();
    let tm = bump_arena::import(&bump, &t);
    bump_arena::export(normalize_imported(&bump, tm))
}

#[cfg(test)]
mod tests {
    use super::super::term::{self, Term};
    use super::normalize;

    #[test]
    fn church_pair_ok() {
        assert_eq!(normalize(term::church_pair(5)), term::church(10));
    }

    #[test]
    fn already_normal_right_chain() {
        // λf.λx. f (f x)：已正态，走流式右链路径，结果须逐字还原
        let input = {
            let mut t = Term::Idx(0);
            for _ in 0..4 {
                t = Term::App(Box::new(Term::Idx(1)), Box::new(t));
            }
            Term::Lam(Box::new(Term::Lam(Box::new(t))))
        };
        assert_eq!(normalize(input.clone()), input);
    }

    #[test]
    fn beta_under_binder() {
        // λg. (λx. x) g  →  λx. x 的体归约后应得 λg. g
        let inner = Term::App(Box::new(Term::Lam(Box::new(Term::Idx(0)))), Box::new(Term::Idx(0)));
        let input = Term::Lam(Box::new(inner));
        assert_eq!(
            normalize(input),
            Term::Lam(Box::new(Term::Idx(0)))
        );
    }

    #[test]
    fn interleaved_chains_fallback() {
        // λf.λg.λx. (λy. (f y) (g y)) (f x) → λf.λg.λx. (f (f x)) (g (f x))
        // 中性链 (f x) 被两条不同链穿插：quote 须走非连续 fallback 路径
        let idx = |i: usize| Term::Idx(i);
        let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
        let lam = |b: Term| Term::Lam(Box::new(b));
        // λy 内：y=0 x=1 g=2 f=3；λfλgλx 层：f=2 g=1 x=0
        let inner = app(app(idx(3), idx(0)), app(idx(2), idx(0))); // (f y) (g y)
        let input = lam(lam(lam(app(lam(inner), app(idx(2), idx(0))))));
        let expect = lam(lam(lam(app(
            app(idx(2), app(idx(2), idx(0))), // f (f x)
            app(idx(1), app(idx(2), idx(0))), // g (f x)
        ))));
        assert_eq!(normalize(input), expect);
    }
}
