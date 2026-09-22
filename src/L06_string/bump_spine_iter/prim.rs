//! prim：builtin prim（decl 表 + 可变全局 + 按名触发）——`Prim` 编号、
//! `DeclEntryF`/`MutableMap`、统一执行 `prim_fire` 与增量触发
//! `decl_apply`/`vapp1`。原 bump_spine_iter.rs 的 "builtin prim…" 一节，
//! 逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;
use std::cell::RefCell;

use super::parser::syntax::Icit;

use super::env::env_ext;
use super::eval::{eval_iter, W};
use super::spine::{decl_name, is_declheaded, MetaEntry, Spine};
use super::syntax::{V, XCell, v_clo_of, v_spine_of, v_tag, v_u, v_xcell, v_xcell_of};

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

/// prim 的最小元数（decl_apply 的元数预检：不足即保持卡住，零收集）。
#[inline]
fn prim_arity(p: Prim) -> usize {
    match p {
        Prim::ReportCheckIssue => 4,
        Prim::ChangeMutableDefault => 3,
        Prim::StrConcat
        | Prim::StrEq
        | Prim::CreateGlobal
        | Prim::ChangeMutable
        | Prim::GetGlobalDefault
        | Prim::FileWriteAllText
        | Prim::FileAppendAllText => 2,
        Prim::StrIndent2
        | Prim::StringToGlobalType
        | Prim::GetGlobal
        | Prim::FileReadAllText
        | Prim::FileExists
        | Prim::FileDelete => 1,
    }
}

/// decl 表条目（参考版 `DeclEntry` 的快版）：定义的值与类型，可选 builtin。
pub(crate) struct DeclEntryF {
    pub(crate) vt: V,
    pub(crate) va: V,
    pub(crate) prim: Option<Prim>,
}

/// 可变全局表（参考版 `Infer.mutable_map`；单线程 RefCell）。key 用
/// `SmolStr`：≤23 字节内联（builtin 用的 "CheckIssues" 与负载里的短键
/// 全部内联），insert 免堆分配。
pub(crate) type MutableMap = RefCell<FxHashMap<SmolStr, V>>;

/// 从实参值取字面量内容（非字面量 → None；参考版同款 match）。返回值的
/// `'a` 与入参无 link——健全性依赖全局不变式：所有 `V` 的 XCell 都指向
/// **当前轮的 bump**或 `'static` 钉串（builtin 的 "true"/"false" 等），
/// 跨轮 `bump.reset()` 前一切句柄已消亡（`clear_round` 清空
/// mutable_map / decl 表，见 `cross_round_isolation` 测试）。
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

/// prim 的统一执行。`args` 是 [`Spine::collect_args`] 的产出（**逆应用
/// 序**，内层在前），[`arg`] 闭包按自然序（应用序）取第 k 个；调用方已
/// 做元数预检（这里仍保留 `len <` 守卫，与参考版逐句对应）。返回 `None`
/// 保持卡住（实参非字面量）；`change_mutable` 族要应用函数实参（走
/// [`vapp1`]），文件族失败 panic。
#[allow(clippy::too_many_arguments)]
fn prim_fire<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<SmolStr, DeclEntryF>,
    mmap: &MutableMap,
    prim: Prim,
    args: &[(V, Icit)], // collect_args 产出（逆应用序）
) -> Option<V> {
    let n = args.len();
    let arg = |k: usize| args[n - 1 - k].0; // 自然序（应用序）第 k 个
    match prim {
        Prim::StrConcat => {
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
        Prim::StrEq => {
            if n < 2 {
                return None;
            }
            match (lit_of(arg(0)), lit_of(arg(1))) {
                (Some(a), Some(b)) => {
                    let s = if a == b { "true" } else { "false" };
                    Some(v_xcell(bump.alloc(XCell::Lit(s))))
                }
                _ => None,
            }
        }
        Prim::StrIndent2 => {
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
        Prim::ReportCheckIssue => {
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
                    SmolStr::new("CheckIssues"),
                    v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&next)))),
                );
            }
            Some(v_u())
        }
        Prim::StringToGlobalType => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(a) => Some(match decls.get(a) {
                    Some(e) => e.vt,
                    None => v_xcell(bump.alloc(XCell::Decl(bump.alloc_str(a)))),
                }),
                _ => None,
            }
        }
        Prim::CreateGlobal => {
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
        Prim::ChangeMutable => {
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
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, arg(1),
                            old, Icit::Expl,
                        );
                        mmap.borrow_mut().insert(SmolStr::new(a), new);
                    }
                    Some(v_u())
                }
                _ => None,
            }
        }
        Prim::GetGlobal => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                // 缺名不再 panic:None 保持卡住的 Decl 头(参考版同款修改)
                Some(a) => mmap.borrow().get(a).copied(),
                _ => None,
            }
        }
        Prim::GetGlobalDefault => {
            if n < 2 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(a) => Some(
                    mmap.borrow()
                        .get(a)
                        .copied()
                        .unwrap_or(arg(1)),
                ),
                _ => None,
            }
        }
        Prim::ChangeMutableDefault => {
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
                                bump, spine, work, vals, icits, defs, metas, decls, mmap,
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
        Prim::FileReadAllText => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(path) => {
                    let content = std::fs::read_to_string(path)
                        .unwrap_or_else(|e| panic!("file_read_all_text: failed to read '{}': {}", path, e));
                    Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&content)))))
                }
                _ => None,
            }
        }
        Prim::FileWriteAllText => {
            if n < 2 {
                return None;
            }
            match (lit_of(arg(0)), lit_of(arg(1))) {
                (Some(path), Some(content)) => {
                    std::fs::write(path, content)
                        .unwrap_or_else(|e| panic!("file_write_all_text: failed to write '{}': {}", path, e));
                    Some(v_u())
                }
                _ => None,
            }
        }
        Prim::FileAppendAllText => {
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
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(path) => {
                    let exists = std::path::Path::new(path).exists();
                    let s = if exists { "true" } else { "false" };
                    Some(v_xcell(bump.alloc(XCell::Lit(s))))
                }
                _ => None,
            }
        }
        Prim::FileDelete => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
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

/// η 展开的可应用性守卫（参考版 `unification::v_applicable` 同款）：只有
/// 中性值——裸 Rigid(0)/未解 Flex(5)、以中性头（Rigid/Flex/Decl）开链的
/// tag 2、裸 Decl(7)——能吃 η 新变量。`string_to_global_type` 把 def 的
/// 登记值（可以是 λ）当"动态类型"返回后，λ 值会以类型身份流入 unify；
/// 对字面量/U/Π 压栈成卡住链虽也以失败告终，但直接判失败与参考版守卫
/// 对齐（参考版此处曾命中 `v_app` impossible panic），免去绕路。
#[inline]
pub(super) fn v_applicable(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        0 | 5 => true,
        2 => {
            let head = spine.spine_head(v_spine_of(v));
            match v_tag(head) {
                0 | 5 => true,
                7 => matches!(v_xcell_of(head), XCell::Decl(_)),
                _ => false, // U/Pi/LiteralType/字面量头的链（压栈惯例的产物）
            }
        }
        7 => matches!(v_xcell_of(v), XCell::Decl(_)),
        _ => false, // Lam(1) 已被前臂接住；U(3)/Pi(4)/LiteralType(6) 不可应用
    }
}

/// 参考版 `v_app` 的 Decl 臂：对 Decl 头应用实参——压栈得到全条累积
/// spine，再把**全部**实参（自然序）交给 prim（元数足够即触发；`None`
/// 保持卡住返回句柄）。无 prim / 未登记的名字同样保持卡住。
#[allow(clippy::too_many_arguments)]
pub(super) fn decl_apply<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<SmolStr, DeclEntryF>,
    mmap: &MutableMap,
    f: V, // 裸 Decl 单元或 decl 头的链
    a: V,
    i: Icit,
) -> V {
    let acc = spine.push(f, a, i);
    let name = decl_name(spine, f);
    if let Some(entry) = decls.get(name) {
        if let Some(prim) = entry.prim {
            // 元数预检：不足即保持卡住（strchain 每层的一次 1 参触发
            // 零收集零分配）；足够才按链长精确容量收集一次
            let n = spine.spine_len(v_spine_of(acc));
            if n >= prim_arity(prim) {
                let mut args: Vec<(V, Icit)> = Vec::with_capacity(n);
                spine.collect_args(v_spine_of(acc), &mut args); // 逆应用序
                if let Some(result) =
                    prim_fire(bump, spine, work, vals, icits, defs, metas, decls, mmap, prim, &args)
                {
                    return result;
                }
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
pub(super) fn vapp1<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<SmolStr, DeclEntryF>,
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
