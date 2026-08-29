//! spine 系的输出编码变体（`bump_spine_rpn`）：quote 不再构建结果树，
//! 而是直接把正态形写成**后缀（RPN）字节流**（`Term::to_vec` 编码，
//! `Term::from_vec` 可解回）。
//!
//! 流式右链的字节序：`App(f, a)` 编码为 `enc(f)·enc(a)·[2]`（函数侧在
//! 前），故 `f (f (f x))` 的编码是 `enc(f)³·enc(x)·[2]³`——链头块先出
//! （外层到内层）、base 随后、App tag 批量殿后，全部顺序追加。链头共享
//! （church 链的形状）时 `enc(f)` 的 9 字节模式只算一次、重复输出。
//! Lam 的长度字段在体写完后就地可得，无需回填。
//!
//! 与 `bump_spine` 的差异只在 quote 一侧的**输出物**：`&Bt` 树
//! （每 App 节点 24B bump 分配）→ `Vec<u8>`（每层约 10B 顺序追加）。
//! eval/值/spine 机制完全复用 [`super::bump_spine`]。递归深度同
//! `bump_spine`（右链走流式循环，深的是罕见形态）。

use bumpalo::Bump;

use super::bump_arena::Bt;
use super::bump_spine::{
    eval, v_clo_of, v_lvl, v_lvl_of, v_spine_of, v_tag, EnvCons, Spine, V,
};
use super::term::Term;

/// RPN 编码的 Idx 片段（9B：8B 索引 + 1B tag，tag 在末尾）。
#[inline]
fn idx_bytes(level: usize, lvl: usize) -> [u8; 9] {
    let mut b = [0u8; 9];
    b[..8].copy_from_slice(&(level - lvl - 1).to_le_bytes());
    b[8] = 0; // Idx tag
    b
}

/// quote level value -> RPN 字节流（追加到 out）。
fn quote_rpn<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    level: usize,
    v: V,
    out: &mut Vec<u8>,
) {
    match v_tag(v) {
        0 => out.extend_from_slice(&idx_bytes(level, v_lvl_of(v))),
        1 => {
            let c = v_clo_of(v);
            let node = bump.alloc(EnvCons { val: v_lvl(level), next: c.env });
            let body = eval(bump, spine, Some(node), c.body);
            let mark = out.len();
            quote_rpn(bump, spine, level + 1, body, out);
            let len = (out.len() - mark) as u64;
            out.extend_from_slice(&len.to_le_bytes());
            out.push(1); // Lam tag
        },
        _ => {
            // 先拷出标量再递归（重入会 push spine，Vec 可能扩容）
            let h = v_spine_of(v);
            let (ef, ea, len, base) = {
                let e = &spine.stack[h];
                (e.f, e.a, e.len, e.base)
            };
            if len > 1 && base as usize + len as usize - 1 == h {
                // 连续右链：enc(v_h) = enc(f_h)···enc(f_b0)·enc(base)·[2]×len
                // 链头从最外层（h）到最内层（base）顺序输出。
                // 输出规模此刻已知（每层 ≤10B），按链预留避免 Vec 中途扩容。
                let n_app = len as usize;
                out.reserve(n_app * 10 + 16);
                let base_v = spine.stack[base as usize].a;
                let f0 = spine.stack[base as usize].f;
                if v_tag(f0) == 0 {
                    // 链头全是同一变量时才打模式摞（32 层/摞一次 memcpy）。
                    // 链头各异（如 f (g x)）必须逐层引——与 bump_spine 树版
                    // 的 per-entry `fi.0 == f0.0` 对照一致；曾漏掉此检查，
                    // 把 f (g x) 错编码成 g (g x)（外层头丢失、内层头重复）。
                    let all_same = (base as usize..=h).all(|i| spine.stack[i].f.0 == f0.0);
                    if all_same {
                        let enc = idx_bytes(level, v_lvl_of(f0));
                        let mut block = [0u8; 9 * 32];
                        for k in 0..32 {
                            block[k * 9..k * 9 + 9].copy_from_slice(&enc);
                        }
                        let mut left = n_app;
                        while left >= 32 {
                            out.extend_from_slice(&block);
                            left -= 32;
                        }
                        for _ in 0..left {
                            out.extend_from_slice(&enc);
                        }
                    } else {
                        for i in (base as usize..=h).rev() {
                            let fi = spine.stack[i].f;
                            quote_rpn(bump, spine, level, fi, out);
                        }
                    }
                } else {
                    for i in (base as usize..=h).rev() {
                        let fi = spine.stack[i].f;
                        quote_rpn(bump, spine, level, fi, out);
                    }
                }
                quote_rpn(bump, spine, level, base_v, out);
                let at = out.len();
                out.resize(at + n_app, 2); // App tag 批量殿后
            } else {
                // 二叉 fallback：后缀序 = enc(f) enc(a) [2]
                quote_rpn(bump, spine, level, ef, out);
                quote_rpn(bump, spine, level, ea, out);
                out.push(2);
            }
        },
    }
}

/// 对已导入 bump 的项做 NBE，返回 RPN 字节流（基准计时对象；import 在计时外）。
pub(crate) fn normalize_imported_rpn<'a>(bump: &'a Bump, tm: &'a Bt<'a>) -> Vec<u8> {
    let mut spine = Spine { stack: Vec::with_capacity(4096) };
    let v = eval(bump, &mut spine, None, tm);
    let mut out = Vec::with_capacity(1 << 16);
    quote_rpn(bump, &mut spine, 0, v, &mut out);
    out
}

/// 便捷入口：import + normalize + 解码（计时含转换成本，供测试）。
pub(crate) fn normalize(t: Term) -> Term {
    let bump = Bump::new();
    let tm = super::bump_arena::import(&bump, &t);
    Term::from_vec(normalize_imported_rpn(&bump, tm)).0
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
        // λf.λx. f (f x)：已正态，走流式右链路径，编码须逐字还原
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
    fn chain_mixed_heads() {
        // λf.λg.λx. f (g x)：连续右链但链头各异（f、g 都是 level 且不同）——
        // 曾误走全同头模式摞，把外层 f 丢掉、内层 g 重复（g (g x)）
        let idx = |i: usize| Term::Idx(i);
        let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
        let lam = |b: Term| Term::Lam(Box::new(b));
        let input = lam(lam(lam(app(idx(2), app(idx(1), idx(0))))));
        assert_eq!(normalize(input.clone()), input);
    }

    #[test]
    fn interleaved_chains_fallback() {
        // λf.λg.λx. (λy. (f y) (g y)) (f x) → λf.λg.λx. (f (f x)) (g (f x))
        let idx = |i: usize| Term::Idx(i);
        let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
        let lam = |b: Term| Term::Lam(Box::new(b));
        let inner = app(app(idx(3), idx(0)), app(idx(2), idx(0)));
        let input = lam(lam(lam(app(lam(inner), app(idx(2), idx(0))))));
        let expect = lam(lam(lam(app(
            app(idx(2), app(idx(2), idx(0))),
            app(idx(1), app(idx(2), idx(0))),
        ))));
        assert_eq!(normalize(input), expect);
    }
}
