//! prim：decl 表基础设施（`DeclEntryF`/`MutableMap`/`Fuel`/`UNIFY_FUEL`/
//! `burn`）与卡住 builtin 的归约体（`lit_of`/`is_selfref_val`/
//! `prim_reduce`）。原 bump_spine_iter.rs 的 "decl 表与 builtin prim"
//! 节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;
use std::cell::{Cell, RefCell};

use super::parser::syntax::Icit;

use super::eval::W;
use super::force::vapp1;
use super::spine::{MetaEntry, Spine};
use super::syntax::{V, v_tag, v_u, v_xcell, v_xcell_of, XCell};

// decl 表与 builtin prim（L07：值 = λ 链 → Prim 标记；归约在 force）
// --------------------------------------------------------------------------------

/// decl 表条目（参考版 `DeclEntry` 的快版）：定义的类型值与 WHNF 值。
/// builtin 无需 prim 标志——其值就是 λ 链求值出的闭包，应用满元数后环境里
/// 出现 `Tm::Prim` 体，force 时按名触发 [`prim_reduce`]。
#[derive(Clone, Copy)]
pub(crate) struct DeclEntryF {
    pub(crate) ty: V,
    pub(crate) val: V,
}

/// 可变全局表（参考版 `Infer.mutable_map`；单线程 RefCell）。
pub(crate) type MutableMap = RefCell<FxHashMap<SmolStr, V>>;

/// force 的展开燃料池（与 unify 递归共享；参考版 `Infer.unify_fuel`）。
pub(crate) type Fuel = Cell<u32>;

pub(super) const UNIFY_FUEL: u32 = 4096;

/// 消耗 1 燃料；耗尽即 false（调用方把值当未解处理 / Err）。
#[inline]
pub(super) fn burn(fuel: &Fuel) -> bool {
    let f = fuel.get();
    if f == 0 {
        return false;
    }
    fuel.set(f - 1);
    true
}

/// 从实参值取字面量内容（非字面量 → None）。返回值的 `'a` 与入参无
/// link——健全性依赖全局不变式：所有 `V` 的 XCell 都指向**当前轮的
/// bump**或 `'static` 钉串（builtin 的 "true"/"false" 等），跨轮
/// `bump.reset()` 前一切句柄已消亡（`clear_round` 清空 mutable_map，
/// decl 表的 Rc 随 Cxt 消亡）。
#[inline]
fn lit_of<'a>(v: V) -> Option<&'a str> {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => Some(s),
            _ => None,
        },
        _ => None
    }
}

/// 递归 def 的自引用占位守卫：`Decl(自身名, 空)`（占位值与 simpl_decl 的
/// 中性条目）——unfold 永无进展只会自旋烧光 fuel 池，直接按中性返回
/// （参考版 force 的 Decl 臂同款守卫）。
#[inline]
pub(super) fn is_selfref_val(v: V, name: &str) -> bool {
    v_tag(v) == 7 && matches!(v_xcell_of(v), XCell::Decl(n) if *n == name)
}

/// 卡住内建的归约体（参考版 `Infer::prim_reduce` 的逐句移植；L06 的
/// builtin 注册表全部函数体）。`args` 是 [`Spine::collect_args`] 的产出
/// （**逆应用序**，内层在前），`arg` 闭包按自然序（应用序）取第 k 个。
/// 元数 / 字面量检查不满足即 None 保持卡住；文件族失败 panic（两版一致）。
#[allow(clippy::too_many_arguments)]
pub(super) fn prim_reduce<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    name: &str,
    args: &[(V, Icit)], // collect_args 产出（逆应用序）
) -> Option<V> {
    let n = args.len();
    let arg = |k: usize| args[n - 1 - k].0; // 自然序（应用序）第 k 个
    match name {
        "string_concat" => {
            if n < 2 {
                return None;
            }
            match (lit_of(arg(0)), lit_of(arg(1))) {
                (Some(a), Some(b)) => {
                    // 一次 bump 分配 + 两段 memcpy（format! 走 fmt 机器且
                    // String → alloc_str 双份拷贝）
                    let len = a.len() + b.len();
                    let ptr = bump
                        .alloc_layout(std::alloc::Layout::from_size_align(len, 1).unwrap())
                        .as_ptr();
                    // SAFETY: a/b 都是 &str（合法 UTF-8）；两段完整序列按
                    // 字节拼接仍是合法 UTF-8，不会引入跨边界截断的码点
                    let s = unsafe {
                        std::ptr::copy_nonoverlapping(a.as_ptr(), ptr, a.len());
                        std::ptr::copy_nonoverlapping(b.as_ptr(), ptr.add(a.len()), b.len());
                        std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr, len))
                    };
                    Some(v_xcell(bump.alloc(XCell::Lit(s))))
                }
                _ => None,
            }
        }
        "str_eq" => {
            if n < 2 {
                return None;
            }
            match (lit_of(arg(0)), lit_of(arg(1))) {
                (Some(a), Some(b)) => {
                    let s = if a == b { "true" } else { "false" };
                    Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(s)))))
                }
                _ => None,
            }
        }
        "str_indent2" => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(s) => {
                    let indented = s.replace('\n', "\n  ");
                    Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&indented)))))
                }
                _ => None,
            }
        }
        "report_check_issue" => {
            if n < 4 {
                return None;
            }
            let get = |i: usize| lit_of(arg(i)).unwrap_or("").to_string();
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
                    "CheckIssues".into(),
                    v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&next)))),
                );
            }
            Some(v_u())
        }
        "string_to_global_type" => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                // 登记名给登记**类型**；未登记名返回以其自身名字的卡住
                // Decl——动态类型的逃逸舱口（后续 unify 的宽松臂处理）
                Some(a) => Some(match decls.get(a) {
                    Some(e) => e.ty,
                    None => v_xcell(bump.alloc(XCell::Decl(bump.alloc_str(a)))),
                }),
                _ => None,
            }
        }
        "create_global" => {
            if n < 2 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(a) => {
                    mmap.borrow_mut().insert(SmolStr::new(a), arg(1));
                    Some(v_u())
                }
                _ => None,
            }
        }
        "change_mutable" => {
            if n < 2 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(a) => {
                    // 同参考版:先取旧值并结束借用,再求值 f——f 的求值可能
                    // 再触发任何 prim,持有 borrow_mut 会 BorrowError panic
                    let old = mmap.borrow().get(a).copied();
                    if let Some(old) = old {
                        let new = vapp1(
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                            arg(1), old, Icit::Expl,
                        );
                        mmap.borrow_mut().insert(SmolStr::new(a), new);
                    }
                    Some(v_u())
                }
                _ => None,
            }
        }
        "get_global" => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                // 缺名不再 panic:None 保持卡住的 Prim 头(参考版同款修改)
                Some(a) => mmap.borrow().get(a).copied(),
                _ => None,
            }
        }
        "get_global_default" => {
            if n < 2 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(a) => Some(mmap.borrow().get(a).copied().unwrap_or(arg(1))),
                _ => None,
            }
        }
        "change_mutable_default" => {
            if n < 3 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(a) => {
                    // 同 change_mutable:先取旧值并结束借用,再求值 f(重入安全)
                    let existing = mmap.borrow().get(a).copied();
                    match existing {
                        Some(old) => {
                            let new = vapp1(
                                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                                arg(1), old, Icit::Expl,
                            );
                            mmap.borrow_mut().insert(SmolStr::new(a), new);
                        }
                        None => {
                            mmap.borrow_mut().insert(SmolStr::new(a), arg(2));
                        }
                    }
                    Some(v_u())
                }
                _ => None,
            }
        }
        "file_read_all_text" => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(path) => {
                    let content = std::fs::read_to_string(path).unwrap_or_else(|e| {
                        panic!("file_read_all_text: failed to read '{}': {}", path, e)
                    });
                    Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&content)))))
                }
                _ => None,
            }
        }
        "file_write_all_text" => {
            if n < 2 {
                return None;
            }
            match (lit_of(arg(0)), lit_of(arg(1))) {
                (Some(path), Some(content)) => {
                    std::fs::write(path, content).unwrap_or_else(|e| {
                        panic!("file_write_all_text: failed to write '{}': {}", path, e)
                    });
                    Some(v_u())
                }
                _ => None,
            }
        }
        "file_append_all_text" => {
            if n < 2 {
                return None;
            }
            match (lit_of(arg(0)), lit_of(arg(1))) {
                (Some(path), Some(content)) => {
                    use std::io::Write;
                    let mut file = std::fs::OpenOptions::new()
                        .append(true)
                        .create(true)
                        .open(path)
                        .unwrap_or_else(|e| {
                            panic!("file_append_all_text: failed to open '{}': {}", path, e)
                        });
                    write!(file, "{}", content).unwrap_or_else(|e| {
                        panic!("file_append_all_text: failed to append to '{}': {}", path, e)
                    });
                    Some(v_u())
                }
                _ => None,
            }
        }
        "file_exists" => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(path) => {
                    let exists = std::path::Path::new(path).exists();
                    let s = if exists { "true" } else { "false" };
                    Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(s)))))
                }
                _ => None,
            }
        }
        "file_delete" => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(path) => {
                    std::fs::remove_file(path).unwrap_or_else(|e| {
                        panic!("file_delete: failed to delete '{}': {}", path, e)
                    });
                    Some(v_u())
                }
                _ => None,
            }
        }
        _ => None,
    }
}
