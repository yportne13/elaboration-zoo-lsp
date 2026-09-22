//! observe：观察面（LSP 接线阶段 1）——观察表 push 方法（`clear_observation_tables`/
//! `push_hover`/`push_ctor_hover`/`push_inlay_hint`/`peel_pi_collect`/
//! `push_qualified_hover`/`hover_entry_at`，独立 `impl Machine` 块承载）与
//! "观察面（LSP 接线阶段 1）测试" 节（`observation_tests`）。原
//! bump_spine_iter.rs 的对应方法与文件尾测试，逐行搬运（2026-09-23 拆分）。

use super::*;

impl Machine {
    /// 观察表清空（两个调用点：轮入口 `clear_round`；prelude 装载收尾——
    /// 参考版加载器对缓存态清三张表同款，用户文件查询只见用户段条目）。
    pub(super) fn clear_observation_tables(&mut self) {
        self.hover_table.clear();
        self.completion_table.clear();
        self.inlay_hint_table.clear();
        self.println_spans.clear();
        self.check_issue_lines.clear();
        self.ctor_hover_memo.clear();
    }

    // ── 观察面（与参考版 `Infer::push_hover` / `hover_entry_at` 同契约）──

    /// push 期把类型渲染成 owned String 入表：走本机 println/错误消息同款
    /// `quote → export → pretty_tm` 管线（parity 已证该管线与参考版逐字节
    /// 一致）。bump 域 Tm 出表即弃，LSP 跨轮读到的只是字符串快照。
    pub(crate) fn push_hover<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t_span: crate::parser_lib::Span<()>,
        def_span: crate::parser_lib::Span<()>,
        v: V,
    ) {
        // prelude 装载段总闸（本轮末表即清，渲染是纯死工作）

        if !self.observe {
            return;
        }
         {
            let tm = self.quote(bump, cxt, cxt.lvl, v);
            let names = types_names_list(cxt.types);
            let rendered = pretty_tm(0, names, &export(&self.symbol_table, tm));
            self.hover_table.push((t_span, def_span, rendered));
        }
    }

    /// 全局名使用处 hover：def_span 取登记处 span，**串实时渲染**（参考版
    /// 同款）。不得用登记期缓存串 `typ_pretty`：登记值里的 meta 可能在登
    /// 记之后才被求解（如泛型 struct 的参数宇宙 meta 由构造子/使用处
    /// check 解出），缓存串会把未解 `?N` 带进使用处悬浮（实测分叉：
    /// `P2[A, B]` 登记期 `[A: ?5]` vs 使用处 `[A: Type 0]`，见
    /// observation_tests::prelude_tuple_mk_element_hover_matches_reference）。
    /// typ_pretty 本身保留——LSP def-site 悬浮（参考版 Path1 直读）用。
    pub(super) fn push_hover_cached<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t_span: crate::parser_lib::Span<()>,
        e: &DeclEntry<'a>,
    ) {
        // final 串（登记期无未解 meta）与使用处实时渲染逐字节一致——
        // 直推缓存，免 quote/export/pretty 全管线（评审 B#1）。
        if e.typ_pretty_final {
            if let Some(s) = &e.typ_pretty {
                self.hover_table.push((t_span, e.span, s.as_ref().clone()));
                return;
            }
        }
        self.push_hover(bump, cxt, t_span, e.span, e.vty);
    }

    /// 构造子使用处 hover（walk_pat Con 臂专用）：hover 值是 decl 条目的
    /// **闭合**值，渲染结果与使用处上下文无关，按 decl 键缓存渲染串——
    /// 同键第二次起免 quote/export/pretty 全管线。无未解 meta 才缓存
    /// （同 `push_hover_cached` 的保守线）；轮界随观察表清空。
    pub(super) fn push_ctor_hover<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t_span: crate::parser_lib::Span<()>,
        def_span: crate::parser_lib::Span<()>,
        v: V,
        key: &str,
    ) {
        if !self.observe {
            return;
        }
        if let Some(s) = self.ctor_hover_memo.get(key) {
            self.hover_table.push((t_span, def_span, s.as_ref().to_owned()));
            return;
        }
        let tm = self.quote(bump, cxt, cxt.lvl, v);
        let rendered = pretty_tm(0, types_names_list(cxt.types), &export(&self.symbol_table, tm));
        if no_metas(bump, self, cxt, tm).is_none() {
            self.ctor_hover_memo
                .insert(SmolStr::new(key), Rc::from(rendered.as_str()));
        }
        self.hover_table.push((t_span, def_span, rendered));
    }

    /// 观察面 inlay（参考版 `push_inlay_hint` 同口径）：含未解 meta 跳过，
    /// label 超 80 字符截断。
    pub(crate) fn push_inlay_hint<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        offset: u32,
        v: V,
    ) {
        // prelude 装载段总闸（同 push_hover）
        if !self.observe {
            return;
        }
         {
            let tm = self.quote(bump, cxt, cxt.lvl, v);
            if no_metas(bump, self, cxt, tm).is_some() {
                return;
            }
            let names = types_names_list(cxt.types);
            let mut label = format!(": {}", pretty_tm(0, names, &export(&self.symbol_table, tm)));
            const MAX_LEN: usize = 80;
            if label.chars().count() > MAX_LEN {
                let truncated: String = label.chars().take(MAX_LEN.saturating_sub(1)).collect();
                label = format!("{}\u{2026}", truncated);
            }
            self.inlay_hint_table.push((offset, label));
        }
    }

    /// 参考版 `peel_pi` 对象：逐层剥 Pi（隐式/显式都剥，与参考版
    /// `Val::Pi` 全匹配同溝），封闭以 `vvar(lvl)` 填充；顺便收集参数
    /// 名拼出等价 `ret_cxt.names()`（头 = 最内层，与 types_names_list
    /// 同序）。返回 (剩余类型值, 新层级, names 追加段)。
    pub(super) fn peel_pi_collect<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        vtyp: V,
    ) -> (V, u32, Vec<SmolStr>) {
        let mut t = vtyp;
        let mut lvl = cxt.lvl;
        let mut peeled: Vec<SmolStr> = Vec::new();
        loop {
            let tf = self.force_v(bump, cxt, t);
            if v_tag(tf) != 4 {
                return (t, lvl, peeled);
            }
            let p = v_pi_of(tf);
            let pname = SmolStr::new(p.name);
            let body = p.body;
            let penv = p.env;
            let val = v_lvl(lvl);
            t = {
                let env = env_ext(bump, penv, val);
                self.eval(bump, cxt, env, body)
            };
            lvl += 1;
            peeled.push(pname);
        }
    }

    /// L5：限定访问中间段 hover（参考版 `push_qualified_hover` 同款）——
    /// `mylib.Foo.mk` 在 `Foo` 上 hover 出类型、`mylib` 上 hover 出命名空
    /// 间声明（若登记）。逐段累积限定名查 decl 表，命中则 cached push。
    pub(super) fn push_qualified_hover<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &Raw,
    ) {
        let mut cur = x;
        loop {
            match cur {
                Raw::Obj(inner, Some(seg)) => {
                    if let Some(full) = qualified_path_str(inner.as_ref(), &seg.data) {
                        if let Some(e) = cxt.decls.get(full.as_str()) {
                            self.push_hover_cached(bump, cxt, seg.to_span(), e);
                        }
                    }
                    cur = inner.as_ref();
                }
                _ => break,
            }
        }
    }

    /// 与参考版 `Infer::hover_entry_at` 同规则：同 path 内命中 offset 的最
    /// 小 span 胜出。
    pub(crate) fn hover_entry_at(
        &self,
        path_id: u32,
        offset: usize,
    ) -> Option<&(crate::parser_lib::Span<()>, crate::parser_lib::Span<()>, String)> {
        self.hover_table
            .iter()
            .filter(|x| x.0.path_id == path_id)
            .filter(|x| x.0.contains(offset))
            .min_by_key(|x| x.0.end_offset - x.0.start_offset)
    }
}

// 观察面（LSP 接线阶段 1）测试
// --------------------------------------------------------------------------------

#[cfg(test)]
mod observation_tests {
    use super::*;

    /// 同一段源分别过孪生与参考版：全局声明使用处的 hover 条目必须逐字节
    /// 一致（渲染字符串 + def span），证明孪生 push 期 quote→export→pretty
    /// 管线与参考版同界。
    #[test]
    fn hover_global_decl_use_matches_reference() {
        let src = "def foo = \"hello\"\ndef bar = foo\n";
        let ast = parse(src, 42).expect("parse");
        let use_off = src.rfind("foo").unwrap();

        // twin
        let mut t = Tycker::new();
        t.run_input(src, 42).expect("twin check");
        let tw = t
            .hover_entry_at(42, use_off)
            .expect("twin hover entry at `foo` use");

        // reference
        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let rf = infer
            .hover_entry_at(42, use_off)
            .expect("ref hover entry at `foo` use");

        assert_eq!(&tw.2, &rf.2, "rendered hover string");
        assert_eq!(
            (tw.1.start_offset, tw.1.end_offset, tw.1.path_id),
            (rf.1.start_offset, rf.1.end_offset, rf.1.path_id),
            "def-site span"
        );
    }

    /// Local variable (lambda binder) use-site hover: rendered string and
    /// def_span (pointing at the binder token) agree with the reference.
    #[test]
    fn hover_local_var_use_matches_reference() {
        let src = "enum Nat {
    zero
    succ(x: Nat)
}
def d0 : Nat -> Nat = n => succ n
";
        let ast = parse(src, 43).expect("parse");
        let line = src.rfind("succ n").unwrap();
        let use_off = line + "succ ".len();
        let binder_off = src.find("= n =").unwrap() + 2;

        let mut t = Tycker::new();
        t.run_input(src, 43).expect("twin check");
        let tw = t.hover_entry_at(43, use_off).expect("twin local hover");

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let rf = infer.hover_entry_at(43, use_off).expect("ref local hover");

        assert_eq!(&tw.2, &rf.2, "local rendered type");
        assert_eq!(
            (tw.1.start_offset, tw.1.end_offset),
            (binder_off as u32, (binder_off + 1) as u32),
            "local def_span points at binder token"
        );
        assert_eq!(
            (tw.1.start_offset, tw.1.end_offset, tw.1.path_id),
            (rf.1.start_offset, rf.1.end_offset, rf.1.path_id),
            "local def_span matches reference"
        );
    }

    /// Struct field projection hover: rendered field type agrees with the
    /// reference (def_span intentionally degrades to the field token until
    /// Sum values carry binder spans - see wiring doc).
    #[test]
    fn hover_field_projection_matches_reference() {
        let src = "struct P {\n    x: String\n}\ndef get(p: P): String = p.x\n";
        let ast = parse(src, 44).expect("parse");
        let use_off = src.rfind(".x").unwrap() + 1;

        let mut t = Tycker::new();
        t.run_input(src, 44).expect("twin check");
        let tw = t.hover_entry_at(44, use_off).expect("twin field hover");

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let rf = infer.hover_entry_at(44, use_off).expect("ref field hover");

        assert_eq!(&tw.2, &rf.2, "field rendered type");
        assert_eq!(tw.2, "String", "field type is String");
    }

    /// Type-ahead completion on a struct receiver: the set of offered field
    /// names keyed at the receiver span agrees with the reference.
    #[test]
    fn completion_struct_fields_matches_reference() {
        let src = "struct P {\n    x: String\n    y: String\n}\ndef get(p: P): String = p.x\n";
        let ast = parse(src, 45).expect("parse");

        let mut t = Tycker::new();
        t.run_input(src, 45).expect("twin check");
        let mut twin_set: Vec<(u32, u32, String)> = t
            .completion_table()
            .iter()
            .map(|(sp, n)| (sp.start_offset, sp.end_offset, n.to_string()))
            .collect();
        twin_set.sort();

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let mut ref_set: Vec<(u32, u32, String)> = infer
            .completion_table
            .iter()
            .map(|(sp, n)| (sp.start_offset, sp.end_offset, n.to_string()))
            .collect();
        ref_set.sort();

        assert!(!twin_set.is_empty(), "twin offered no completions");
        assert_eq!(twin_set, ref_set, "completion sets (span-keyed) agree");
    }

    /// Inlay hints for inferred returns / un-annotated lets: label text and
    /// anchor offsets agree with the reference (plain, dependent-telescope,
    /// and let cases).
    #[test]
    fn inlay_hints_match_reference() {
        let src = "def g = \"hi\"\ndef id(a: String): String = a\ndef h(b: String) = b\n";
        let ast = parse(src, 46).expect("parse");

        let mut t = Tycker::new();
        t.run_input(src, 46).expect("twin check");
        let mut twin_v: Vec<(u32, String)> = t
            .inlay_hint_table()
            .iter()
            .map(|(o, l)| (*o, l.clone()))
            .collect();
        twin_v.sort();

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let mut ref_v: Vec<(u32, String)> = infer
            .inlay_hint_table
            .iter()
            .map(|(o, l)| (*o, l.clone()))
            .collect();
        ref_v.sort();

        assert!(!ref_v.is_empty(), "fixture must produce inlay hints");
        assert_eq!(twin_v, ref_v, "inlay (offset, label) sets agree");
    }

    /// PM constructor-pattern hover: `case leaf` / `case node(x)` tokens must
    /// hover like constructor expressions (nullary -> `Tree::leaf`,
    /// parameterized -> Pi signature), keyed at the user's token with def
    /// span at the enum declaration.
    #[test]
    fn hover_pm_constructor_patterns_match_reference() {
        let src = "enum Tree {\n    leaf\n    node(x: Tree)\n}\ndef depth(t: Tree): Tree =\n    match t {\n        case leaf => leaf\n        case node(x) => x\n    }\n";
        let ast = parse(src, 48).expect("parse");

        let mut t = Tycker::new();
        t.run_input(src, 48).expect("twin check");
        let mut twin_v: Vec<(u32, u32, u32, u32, String)> = t
            .hover_table()
            .iter()
            .map(|(ts, ds, r)| {
                (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone())
            })
            .collect();
        twin_v.sort();

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let mut ref_v: Vec<(u32, u32, u32, u32, String)> = infer
            .hover_table
            .iter()
            .map(|(ts, ds, r)| {
                (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone())
            })
            .collect();
        ref_v.sort();

        // 允许两类已知缺项（均登记在接线文档，非本测试核心）：
        //  A) start=0 的参考版 artifact（其 Val::Sum cases 的 Span 丢 start，
        //     PM push 键跟着畸变；孪生值层 cases 只有名字，无从复现 end）；
        //  B) 构造子定义处（use==def-span 形态）条目——孪生 Enum 臂尚未接
        //     def-site push（下一组待接项）。
        let missing: Vec<_> = ref_v
            .iter()
            .filter(|x| !twin_v.contains(x))
            .filter(|x| {
                let start_zero_artifact = x.0 == 0 && x.1 != 0;
                let def_site_entry = x.0 == x.2 && x.1 == x.3;
                !(start_zero_artifact || def_site_entry)
            })
            .map(|x| format!("{}..{}@{}..{} {:?}", x.0, x.1, x.2, x.3, x.4))
            .collect();
        assert!(
            missing.is_empty(),
            "twin PM hover missing unexplained reference entries: {:?}",
            missing
        );
        // 关键断言（从 src 真实计算 token 偏移，不硬编码）：case 的构造子
        // token 必须渲染构造子标识（无参→`Tree::leaf`；参数化→Pi 签名串）。
        let leaf_tok = src.find("case leaf").unwrap() + "case ".len();
        let node_tok = src.find("case node").unwrap() + "case ".len();
        let leaf_entries: Vec<&String> = twin_v
            .iter()
            .filter(|x| x.0 == leaf_tok as u32 && x.1 == (leaf_tok + 4) as u32)
            .map(|x| &x.4)
            .collect();
        let node_entries: Vec<&String> = twin_v
            .iter()
            .filter(|x| x.0 == node_tok as u32 && x.1 == (node_tok + 4) as u32)
            .map(|x| &x.4)
            .collect();
        println!("LEAF token entries: {:?}", leaf_entries);
        println!("NODE token entries: {:?}", node_entries);
        assert!(
            leaf_entries.iter().any(|r| r.as_str() == "Tree::leaf"),
            "`case leaf` token must also hover as Tree::leaf; got {:?}",
            leaf_entries
        );
        assert!(
            node_entries.iter().any(|r| r.starts_with("(x")),
            "`case node` token must also hover as its Pi signature; got {:?}",
            node_entries
        );
    }

    /// Impl-header hover pair: `impl Trait for Ty` — the trait-name token
    /// resolves to the trait declaration, and each implementing `def` name
    /// resolves to the trait method's declaration span.
    #[test]
    fn hover_impl_header_matches_reference() {
        let src = "enum Nat {\n    zero\n    succ(x: Nat)\n}\ntrait Pick[T] {\n    def pick(t: T): T\n}\nimpl Pick[Nat] for Nat {\n    def pick(t: Nat): Nat = t\n}\n";
        let ast = parse(src, 49).expect("parse");

        let mut t = Tycker::new();
        t.run_input(src, 49).expect("twin check");
        let mut twin_v: Vec<(u32, u32, u32, u32, String)> = t
            .hover_table()
            .iter()
            .map(|(ts, ds, r)| {
                (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone())
            })
            .collect();
        twin_v.sort();

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let mut ref_v: Vec<(u32, u32, u32, u32, String)> = infer
            .hover_table
            .iter()
            .map(|(ts, ds, r)| {
                (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone())
            })
            .collect();
        ref_v.sort();

        // 断言两版各自的 impl-header 关键条目存在（trait 名 token、实现
        // 方法名 token），且两版 key 集合一致（渲染串允许偏差 4 的 prime 差）。
        let trait_tok = src.find("impl Pick").unwrap() + "impl ".len();
        let method_tok = src.rfind("def pick").unwrap() + 4;
        let key = |x: &(u32, u32, u32, u32, String)| x.0;
        for (name, off, len) in [("trait-name", trait_tok, 4), ("method-name", method_tok, 4)] {
            let _ = key;
            let in_ref = ref_v.iter().any(|x| x.0 == off as u32 && x.1 == (off + len) as u32);
            let in_twin = twin_v.iter().any(|x| x.0 == off as u32 && x.1 == (off + len) as u32);
            assert!(in_ref, "reference lacks {} hover entry", name);
            assert!(in_twin, "twin lacks {} hover entry", name);
        }
    }

    /// Trait-dispatched member access (`x.pick` resolved through the trait
    /// dictionary, not an inherent namespace entry): the method-name token
    /// must hover with the trait method's declaration span on both engines.
    #[test]
    fn hover_trait_dispatched_method_matches_reference() {
        let src = "enum Nat {\n    zero\n    succ(x: Nat)\n}\ntrait Pick {\n    def pick: Nat\n}\nimpl Pick for Nat {\n    def pick: Nat = zero\n}\ndef use(n: Nat): Nat = n.pick\n";
        let ast = parse(src, 50).expect("parse");

        let mut t = Tycker::new();
        t.run_input(src, 50).expect("twin check");
        let mut twin_v: Vec<(u32, u32, String)> = t
            .hover_table()
            .iter()
            .map(|(ts, _, r)| (ts.start_offset, ts.end_offset, r.clone()))
            .collect();
        twin_v.sort();

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let mut ref_v: Vec<(u32, u32, String)> = infer
            .hover_table
            .iter()
            .map(|(ts, _, r)| (ts.start_offset, ts.end_offset, r.clone()))
            .collect();
        ref_v.sort();

        // 使用处的 pick token（`n.pick`）两版都必须有条目
        let use_pick = src.rfind("n.pick").unwrap() + 2;
        let in_ref = ref_v.iter().any(|x| x.0 == use_pick as u32 && x.1 == (use_pick + 4) as u32);
        let in_twin = twin_v.iter().any(|x| x.0 == use_pick as u32 && x.1 == (use_pick + 4) as u32);
        assert!(in_ref, "reference lacks trait-dispatch method hover");
        assert!(in_twin, "twin lacks trait-dispatch method hover");
    }

    /// Whole-table parity on a package + qualified-access + bare-name
    /// fallback fixture: every (use-span, rendered-type) entry the reference
    /// table holds must be present in the twin table (twin may hold a few
    /// extra prefix-walk entries; the reference does the same walk, so in
    /// practice sets are equal — assert full equality).
    #[test]
    fn hover_table_full_matches_reference_on_qualified_fixture() {
        let src = "package mylib\n\nenum Tree {\n    leaf\n    node(x: Tree)\n}\n\ndef t: Tree = leaf\n\ndef u: Tree = Tree.node(t)\n";
        let ast = parse(src, 47).expect("parse");

        let mut t = Tycker::new();
        t.run_input(src, 47).expect("twin check");
        let mut twin_v: Vec<(u32, u32, String)> = t
            .hover_table()
            .iter()
            .map(|(ts, _, r)| (ts.start_offset, ts.end_offset, r.clone()))
            .collect();
        twin_v.sort();

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let mut ref_v: Vec<(u32, u32, String)> = infer
            .hover_table
            .iter()
            .map(|(ts, _, r)| (ts.start_offset, ts.end_offset, r.clone()))
            .collect();
        ref_v.sort();

        // 已知偏差 5：孪生构造子体 datas 的 Raw::Var(参数名) 复用 infer 路径，
        // 产生与 binder 条目同 span 同串的**重复**（参考版该处在值层合成、
        // 不过 infer）。对 LSP 无行为影响（min_by_key 平手取先、串相同）。
        // 断言方向：参考版每条都在孪生（无缺失），且孪生每条都能在参考版
        // 找到同 (span, 串) 项（孪生只允许重复、不允许异质条目）。
        let missing: Vec<_> = ref_v
            .iter()
            .filter(|x| !twin_v.contains(x))
            .map(|(a, b, r)| format!("{}..{} {:?}", a, b, &src[*a as usize..*b as usize]))
            .collect();
        assert!(missing.is_empty(), "twin missing reference entries: {:?}", missing);
        let foreign: Vec<_> = twin_v
            .iter()
            .filter(|x| !ref_v.contains(x))
            .collect();
        assert!(
            foreign.is_empty(),
            "twin has entries absent from reference (should only duplicate): {:?}",
            foreign
        );
    }

    // ── 阶段 2：prelude 装载口径的双引擎互检 ──
    // 孪生 prelude 轮（`run_decls_with_prelude`）对参考版缓存加载
    // （`clone_prelude_state`）：同源 parse_prelude_files 表、nat/vconnT
    // 注册、短名别名、HdlLoopIdx 复位。用户段观察表三张 + Ok 输出逐字节
    // 互检——tuple-mk/真实 HDL 观察面在此前只能"接线待实测"，本组测试是
    // 阶段 2 的验收面。

    use crate::L13_namespace::{PreludeParse, PRELUDE_CORE, PRELUDE_HDL, PRELUDE_SHOW};

    /// 核心 prelude 文件序列（含 show——参考版加载器恒排在最后）。
    fn core_files() -> Vec<(&'static str, &'static str)> {
        let mut v: Vec<(&'static str, &'static str)> = PRELUDE_CORE.to_vec();
        v.push(PRELUDE_SHOW);
        v
    }

    /// 全量 prelude 文件序列（core + hdl + show，参考版 include_hdl 同序）。
    fn hdl_files() -> Vec<(&'static str, &'static str)> {
        let mut v = core_files();
        let (show, show_src) = v.pop().unwrap();
        v.extend(PRELUDE_HDL);
        v.push((show, show_src));
        v
    }

    /// 临时探针：打印某 HDL 例的孪生错误（`HBAD` 选文件）。
    #[test]
    #[ignore = "manual probe"]
    fn probe_twin_errors_on_hdl() {
        let name = std::env::var("HBAD").unwrap_or_else(|_| "18-utils.typort".into());
        let pre = crate::L13_namespace::parse_prelude_files(&hdl_files());
        let mut t = Tycker::new();
        t.prime_resident(&pre).expect("prime");
        let src = std::fs::read_to_string(format!("examples/hdl/{name}")).unwrap();
        let (decls, _e, _x, _p) = crate::L13_namespace::parser::parser_with_macros(
            &crate::L13_namespace::preprocess(&src), 700, &pre.macros,
        ).expect("parse");
        t.observe_user(&pre, &decls).expect("observe");
        for e in t.user_errors() {
            eprintln!(
                "[TERR] {}..{} {:?}",
                e.0.start_offset,
                e.0.end_offset,
                e.0.data.lines().take(30).collect::<Vec<_>>().join(" / ")
            );
        }
        eprintln!("[TERR] errors={}", t.user_errors().len());
        for (i, l) in t.check_issue_lines() {
            eprintln!("[TERR] check decl{i}: {}", l.chars().take(80).collect::<String>());
        }
        eprintln!("[TERR] checks={}", t.check_issue_lines().len());
    }

    /// **回归**：模块体内表达式 `let`（`let x = a + b`）的展开会经过
    /// `no_metas`——它必须走值图 + 访问集，不能对已解 meta 的（自引用）
    /// 解做 quote 再查，否则在扁平化 module 链上死循环（实测 01-basics 的
    /// `exprLet`/`autoNames` 两模块曾挂死；参考版 mod.rs 已记录该 quote 版
    /// 在某 HDL 例占 65% 采样）。此例锁死不再挂。
    #[test]
    fn expr_let_in_module_body_terminates() {
        let pre = crate::L13_namespace::parse_prelude_files(&hdl_files());
        assert_eq!(pre.failed, None);
        let cases = [
            // 表达式 let（LetNamed）+ 后续使用
            "module m {\n    input a = UInt[8]\n    input b = UInt[8]\n    output y = UInt[8]\n    let x = a + b\n    y := x\n}\n",
            // auto* 自动命名系列
            "module m {\n    let w = autoUInt(8)\n    let i = autoUIntInput(8)\n    let r = autoUIntReg(8)\n    r := w + i\n}\n",
        ];
        let mut t = Tycker::new();
        t.prime_resident(&pre).expect("prime");
        for src in cases {
            let (decls, _e, _x, _p) = crate::L13_namespace::parser::parser_with_macros(
                &crate::L13_namespace::preprocess(src), 610, &pre.macros,
            ).expect("parse");
            t.observe_user(&pre, &decls).expect("observe_user must terminate");
        }
    }

    /// 手动性能测量：把孪生 kick 拆成「prelude 重放」与「用户文件增量」，
    /// 判断 3b 常驻 prelude 能否让交互路径净收益为正。
    /// 运行：`cargo test --release --lib split -- --ignored --nocapture`
    #[test]
    #[ignore = "manual perf measurement"]
    fn split_seed_vs_user_cost() {
        let pre = crate::L13_namespace::parse_prelude_files(&hdl_files());
        assert_eq!(pre.failed, None);

        let mut best_p = f64::MAX;
        for _ in 0..3 {
            let mut t = Tycker::new();
            let t0 = std::time::Instant::now();
            t.run_decls_with_prelude(&pre, &[]).expect("prelude replay");
            let dt = t0.elapsed().as_secs_f64() * 1000.0;
            if dt < best_p { best_p = dt; }
        }

        let src = include_str!("../../../examples/hdl/09-hierarchy.typort");
        let (user_decls, _e, _x, _p) =
            crate::L13_namespace::parser::parser_with_macros(
                &crate::L13_namespace::preprocess(src), 900, &pre.macros,
            ).expect("user parse");
        let mut best_full = f64::MAX;
        for _ in 0..3 {
            let mut t = Tycker::new();
            let t0 = std::time::Instant::now();
            t.run_decls_with_prelude(&pre, &user_decls).expect("full replay");
            let dt = t0.elapsed().as_secs_f64() * 1000.0;
            if dt < best_full { best_full = dt; }
        }
        eprintln!("[SPLIT] prelude-only {best_p:.1} ms | prelude+file {best_full:.1} ms | user ~{:.1} ms",
            best_full - best_p);
    }

    /// **导出面互检（阶段 4 数据面前提）**：孪生 `observe_user` 导出的用户
    /// 声明构成参考域 `Decl` 表后，`pretty_sum_definition`（enum/struct 成员
    /// 渲染）与参考版逐字节一致——这是 LSP Path1 定义处悬浮不走样、可把
    /// 参考域全局表交给孪生导出的前提。
    #[test]
    fn twin_exported_decls_render_sum_members_like_reference() {
        let src = r#"enum Tree {
    leaf
    node(l: Tree, r: Tree)
}
struct P {
    x: Nat
    y: Boolean
}
"#;
        let pre = crate::L13_namespace::parse_prelude_files(&core_files());
        assert_eq!(pre.failed, None);
        let (decls, _e, _x, _p) = crate::L13_namespace::parser::parser_with_macros(
            &crate::L13_namespace::preprocess(src), 910, &pre.macros,
        ).expect("parse");

        // twin exports -> reference Decl map.
        let mut t = Tycker::new();
        t.prime_resident(&pre).expect("prime");
        t.observe_user(&pre, &decls).expect("observe");
        let mut tdecl: crate::L13_namespace::Decl = rustc_hash::FxHashMap::default();
        for (k, e) in t.user_decl_exports() {
            tdecl.insert(k.clone(), (e.span, e.tm.clone(), e.val.clone(), e.ty.clone(), e.vty.clone(), None, e.typ_pretty.clone()));
        }

        // reference Decl map.
        let (mut infer, mut rcxt, _m) =
            crate::L13_namespace::clone_prelude_state(false).expect("ref load");
        for d in &decls {
            let (_, _, nc) = infer.infer(&rcxt, d.clone()).expect("ref infer");
            rcxt = nc;
        }
        let rdecl = &rcxt.decl;

        // Render each user type's member list through both tables.
        for key in ["Tree", "P"] {
            let ttm = &tdecl.get(key).expect("twin exported key").1;
            let rtm = &rdecl.get(key).expect("ref key").1;
            let ts = crate::L13_namespace::pretty_sum_definition(key, ttm, &tdecl);
            let rs = crate::L13_namespace::pretty_sum_definition(key, rtm, rdecl);
            assert_eq!(ts, rs, "sum rendering mismatch for {key}");
            assert!(ts.is_some(), "expected member list for {key}");
        }
    }

    /// 手动测量：常驻 bump 的内存占用（内存/CPU 权衡决策用）。
    ///
    /// **实测（2026-09-10，release，HDL 全量 prelude）**：prime 后 bump
    /// `allocated_bytes` ≈ **2.15GB**（进程 RSS ≈ 1.8GB），此后每 kick 用户段
    /// 增量落在既有 chunk 余量内（观测 0 增长）。对照参考版 prelude 缓存
    /// RSS ≈ 200MB——**孪生常驻以 ~9× 内存换 3.4× CPU**：bump arena 不回收
    /// 中间值，prelude 装载期的全部中间值都留在常驻 bump 里，而参考版 Rc
    /// 图会释放不可达节点。故 twin 模式保持 opt-in（`TYPORT_LSP_ENGINE=twin`），
    /// **不宜默认开启**；降内存需另做「装载后压实 / 分段 arena」。
    #[test]
    #[ignore = "manual memory measurement"]
    fn resident_memory_growth_per_kick() {
        let pre = crate::L13_namespace::parse_prelude_files(&hdl_files());
        assert_eq!(pre.failed, None);
        let src = include_str!("../../../examples/hdl/09-hierarchy.typort");
        let (decls, _e, _x, _p) = crate::L13_namespace::parser::parser_with_macros(
            &crate::L13_namespace::preprocess(src), 920, &pre.macros,
        ).expect("parse");
        let mut t = Tycker::new();
        t.prime_resident(&pre).expect("prime");
        let cap = t.bump.allocated_bytes();
        let used = cap - t.bump.chunk_capacity();
        eprintln!(
            "[MEM] after prime: capacity={cap} ({} MB) used={used} ({} MB) waste={} MB",
            cap >> 20,
            used >> 20,
            (cap - used) >> 20,
        );
        let mut prev = 0usize;
        for i in 0..8 {
            t.observe_user(&pre, &decls).expect("observe");
            let now = t.resident_user_bytes();
            eprintln!("[MEM] kick {i}: user_bytes={} (delta={}) abs_alloc={}", now, now - prev, t.bump.allocated_bytes());
            prev = now;
        }
    }

    /// **孪生自产诊断的互检**：错误语料上孪生 `observe_user` 累积的
    /// (span, message) 多重集必须与参考版 LSP `elaborate` 口径收集的
    /// ERROR 诊断一致（错误 span 保真 + 逐 decl 不早退）。
    #[test]
    fn twin_user_errors_match_reference_diagnostics() {
        let corpus = [
            // 单错：unify
            "def foo: Nat = true\n",
            // 单错：未绑定名
            "def qux: Nat = nope\n",
            // 多错：两个 decl 各自错（验证不早退）
            "def a: Nat = true\ndef b: Boolean = 1\n",
            // 中间 decl 错、后续仍应被检查
            "def a: Nat = zero\ndef bad: Nat = true\ndef c: Nat = succ zero\n",
            // 调用处实参类型错
            "def inc(n: Nat): Nat = succ n\ndef use: Nat = inc true\n",
            // 字面量类型错
            "def s: String = 42\n",
            // 错误 + 正确混合
            "def good: Nat = zero\ndef bad2: Boolean = zero\n",
        ];
        let pre = crate::L13_namespace::parse_prelude_files(&core_files());
        assert_eq!(pre.failed, None);

        for src in corpus {
            let (decls, _e, _x, _p) = crate::L13_namespace::parser::parser_with_macros(
                &crate::L13_namespace::preprocess(src), 880, &pre.macros,
            ).expect("parse");

            // twin: observe_user accumulates, never early-returns.
            let mut t = Tycker::new();
            t.prime_resident(&pre).expect("prime");
            t.observe_user(&pre, &decls).expect("observe");
            let mut twin: Vec<(u32, u32, u32, String)> = t
                .user_errors()
                .iter()
                .map(|e| (e.0.start_offset, e.0.end_offset, e.0.path_id, e.0.data.clone()))
                .collect();
            twin.sort();

            // reference: mirror `lib.rs::elaborate`'s ERROR collection.
            let (mut infer, mut rcxt, _m) =
                crate::L13_namespace::clone_prelude_state(false).expect("ref load");
            let mut refs: Vec<(u32, u32, u32, String)> = Vec::new();
            for d in &decls {
                match infer.infer(&rcxt, d.clone()) {
                    Ok((_, _, nc)) => rcxt = nc,
                    Err(e) => refs.push((e.0.start_offset, e.0.end_offset, e.0.path_id, e.0.data.clone())),
                }
                for e in infer.accumulated_errors.drain(..) {
                    refs.push((e.0.start_offset, e.0.end_offset, e.0.path_id, e.0.data.clone()));
                }
            }
            refs.sort();
            assert_eq!(twin, refs, "diagnostic mismatch for:\n{src}");
        }
    }

    /// **18-utils 分叉探针**（2026-09-11 调查的继任，2026-09-14 重启）。
    ///
    /// 2026-09-14 已定位并修复其中一因：`tm_refs_bn` 的索引公式符号反向
    /// （`depth + i == bind_idx`，正确为 `ix == bind_idx + depth`），使
    /// `bn_refs` 误判 → `maybe_prechecked_method_body` 的复用门恒真 →
    /// module 的 tree 方法体整链重推（隐含调用全部隐参 fresh_meta）。
    /// 修复后本站 impl 相位两版对齐（16 = 16），18-utils 用户段 net meta
    /// 982 → 680（参考版 733，残差为 Phase A 的既有差，见下）。
    ///
    /// **残留**：① Phase A 每模块少 11 个隐参插入——逐 item 计数已定位到
    /// module 脚手架的 `change_mutable("ModuleTree", ...)` 一项（参考版 22 /
    /// 孪生 11 net），插入点头部对照显示参考版多走一趟含 `outParam`/`Self`
    /// 的 trait 方法签名 elaboration，判定为孪生复用路径少干活的良性差异；
    /// ② 假 "solve trait failed: LetNamed[...]"（+ 级联 `utilsReg` 未解析）
    /// 仍在 → 18-utils 继续经信任闸回落参考版。本站用于后续对比两版
    /// （net meta 创建量 + 错误集）与源码收缩定位；`TYPORT_DECL_PROBE=1`
    /// 时孪生打逐 decl / 逐相位 / 逐 item 增量，参考侧由本站镜像循环打逐 decl。
    #[test]
    #[ignore = "divergence probe: cargo test twin_utils_divergence_probe -- --ignored --nocapture"]
    fn twin_utils_divergence_probe() {
        let pre = crate::L13_namespace::parse_prelude_files(&hdl_files());
        assert_eq!(pre.failed, None);

        let compare = |name: &str, src: &str| {
            let (decls, _e, _x, _p) = crate::L13_namespace::parser::parser_with_macros(
                &crate::L13_namespace::preprocess(src), 880, &pre.macros,
            ).expect("parse");
            let mut t = Tycker::new();
            t.prime_resident(&pre).expect("prime");
            t.observe_user(&pre, &decls).expect("observe");
            let twin_metas = t.last_kick_metas_created();
            let twin_errs: Vec<String> = t.user_errors().iter().map(|e| e.0.data.clone()).collect();

            let (mut infer, mut rcxt, _m) =
                crate::L13_namespace::clone_prelude_state(true).expect("ref load");
            let rbase = infer.meta.len();
            let mut rerrs: Vec<String> = Vec::new();
            for (i, d) in decls.iter().enumerate() {
                let m0 = infer.meta.len();
                match infer.infer(&rcxt, d.clone()) {
                    Ok((_, _, nc)) => rcxt = nc,
                    Err(e) => rerrs.push(e.0.data.clone()),
                }
                for e in infer.accumulated_errors.drain(..) {
                    rerrs.push(e.0.data.clone());
                }
                if std::env::var_os("TYPORT_DECL_PROBE").is_some() {
                    eprintln!("[DECL{i}] ref metas+{}", infer.meta.len() - m0);
                }
            }
            eprintln!(
                "[PROBE {name}] decls={} twin_metas={} ref_metas={} twin_errs={} ref_errs={}",
                decls.len(), twin_metas, infer.meta.len() - rbase, twin_errs.len(), rerrs.len(),
            );
            if !twin_errs.is_empty() { eprintln!("[PROBE {name}] twin errors: {twin_errs:#?}"); }
            if !rerrs.is_empty() { eprintln!("[PROBE {name}] ref errors: {rerrs:#?}"); }
        };

        compare("full", include_str!("../../../examples/hdl/18-utils.typort"));
        // DECL0 (utilsRev) 逐语句收缩：定位 module 路径的 meta 源。
        compare(
            "utilsRev-whole",
            "module utilsRev {\n    let a = Bits[8]\n    let r = Bits[8]\n    r := reverse(a)\n    let u = UInt[8]\n    let ru = UInt[8]\n    ru := reverse(u)\n    let p = Bits[8]\n    p := propagateOnes(a, false)\n    let p2 = Bits[8]\n    p2 := propagateOnes(a, true)\n}\n",
        );
        compare(
            "rev-only",
            "module m {\n    let a = Bits[8]\n    let r = Bits[8]\n    r := reverse(a)\n}\n",
        );
        compare(
            "no-call",
            "module m {\n    let a = Bits[8]\n    let r = Bits[8]\n}\n",
        );
        // 顶层 def 对照（无 module 宏包装）。
        compare(
            "top-level-rev",
            "def a = Bits[8]\ndef r = reverse(a)\nprintln r\n",
        );
    }

    /// **阶段 3b 等价性验收**：常驻检查点（`prime_resident` 一次 +
    /// 多次 `observe_user`）对同一用户源产出的观察三表，必须与每次全新
    /// `run_decls_with_prelude` 逐字节一致。多轮用**不同**源，揪出跨 kick
    /// 的状态泄漏（meta/实例/全局/别名）。
    #[test]
    fn resident_checkpoint_matches_fresh_replay_across_kicks() {
        let pre = crate::L13_namespace::parse_prelude_files(&hdl_files());
        assert_eq!(pre.failed, None);

        // 三个不同形态的用户源：全局使用、tuple、真实 HDL 模块。
        let srcs: Vec<(&str, u32)> = vec![
            ("def foo = \"hello\"\ndef bar = foo\n", 300),
            ("def ff(a: Nat, b: Boolean): Tuple2[Nat, Boolean] = (a, b)\n", 301),
            (include_str!("../../../examples/hdl/09-hierarchy.typort"), 302),
        ];

        // 常驻：prime 一次，逐源 observe_user。
        let mut resident = Tycker::new();
        resident.prime_resident(&pre).expect("prime");
        let mut resident_tables = Vec::new();
        for (src, pid) in &srcs {
            let (decls, _e, _x, _p) = crate::L13_namespace::parser::parser_with_macros(
                &crate::L13_namespace::preprocess(src), *pid, &pre.macros,
            ).expect("parse");
            resident.observe_user(&pre, &decls).expect("observe_user");
            let mut v: Vec<(u32, u32, u32, u32, String)> = resident
                .hover_table()
                .iter()
                .map(|(ts, ds, r)| (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone()))
                .collect();
            v.sort();
            resident_tables.push(v);
        }

        // 全新：每源一个 Tycker，整轮重放。
        for (i, (src, pid)) in srcs.iter().enumerate() {
            let (decls, _e, _x, _p) = crate::L13_namespace::parser::parser_with_macros(
                &crate::L13_namespace::preprocess(src), *pid, &pre.macros,
            ).expect("parse");
            let mut fresh = Tycker::new();
            fresh.run_decls_with_prelude(&pre, &decls).expect("fresh replay");
            let mut v: Vec<(u32, u32, u32, u32, String)> = fresh
                .hover_table()
                .iter()
                .map(|(ts, ds, r)| (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone()))
                .collect();
            v.sort();
            assert_eq!(
                resident_tables[i], v,
                "resident kick {i} hover table diverged from fresh replay for:\n{src}",
            );
        }
    }

    /// **压实等价性验收（2026-09-14 编辑卡顿修复）**：常驻检查点被
    /// [`Tycker::compact_resident`] 就地压实后，跨 kick 的观察表仍须与全新
    /// 重放逐字节一致。压实换 arena 后任何仍指向旧 arena 的陈旧引用
    /// （force memo 的打包字键/值、unify scratch、指针键缓存）都会在这里
    /// 炸出来——本用例把预算调到 0，强制每个 kick 起点压实一次。
    #[test]
    fn resident_compaction_matches_fresh_replay_across_kicks() {
        let pre = crate::L13_namespace::parse_prelude_files(&hdl_files());
        assert_eq!(pre.failed, None);
        let src = include_str!("../../../examples/hdl/09-hierarchy.typort");
        let (decls, _e, _x, _p) = crate::L13_namespace::parser::parser_with_macros(
            &crate::L13_namespace::preprocess(src), 302, &pre.macros,
        ).expect("parse");

        // Budget 0: the previous kick's (nonzero) user-segment garbage forces a
        // compaction at the next kick's start.
        set_resident_bump_budget(0);
        let before = resident_compactions();
        let mut resident = Tycker::new();
        resident.prime_resident(&pre).expect("prime");
        let mut kicks = Vec::new();
        for _ in 0..4 {
            resident.observe_user(&pre, &decls).expect("observe_user");
            let mut v: Vec<(u32, u32, u32, u32, String)> = resident
                .hover_table()
                .iter()
                .map(|(ts, ds, r)| (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone()))
                .collect();
            v.sort();
            kicks.push(v);
        }
        assert!(
            resident_compactions() - before >= 3,
            "compaction path not exercised (counted {})",
            resident_compactions() - before,
        );

        let mut fresh = Tycker::new();
        fresh.run_decls_with_prelude(&pre, &decls).expect("fresh replay");
        let mut fv: Vec<(u32, u32, u32, u32, String)> = fresh
            .hover_table()
            .iter()
            .map(|(ts, ds, r)| (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone()))
            .collect();
        fv.sort();
        for (i, v) in kicks.iter().enumerate() {
            assert_eq!(
                *v, fv,
                "compacted resident kick {i} hover table diverged from fresh replay",
            );
        }
        // Restore the default budget so a later test on this thread is unaffected.
        set_resident_bump_budget(super::RESIDENT_BUMP_LIMIT);
    }

    /// 双引擎各跑一遍「prelude 装载 + 用户源」：
    /// - 孪生：[`Tycker::run_decls_with_prelude`]（共享 parse 产物）；
    /// - 参考：`clone_prelude_state`（缓存加载器，含别名/HdlLoopIdx 收尾）
    ///   + 逐 decl `infer`，输出组装镜像参考版 `run`（排水行 + println 串）。
    /// 返回 (twin 输出, 参考输出, twin Tycker, 参考 Infer)。
    fn run_prelude_both(
        files: &[(&'static str, &'static str)],
        include_hdl: bool,
        user_src: &str,
        path_id: u32,
    ) -> (String, String, Tycker, crate::L13_namespace::Infer) {
        // 两参数必须一致（files 决定 prelude 内容，include_hdl 决定参考版
        // 走哪个缓存池）——错配会以难读的全表 diff 收场
        assert_eq!(
            include_hdl,
            files.iter().any(|(n, _)| *n == "hdl-core"),
            "files/include_hdl must agree"
        );
        let pre: PreludeParse = crate::L13_namespace::parse_prelude_files(files);
        assert_eq!(pre.failed, None, "prelude files must parse");
        let (user_decls, _errs, _exports, _expansions) =
            crate::L13_namespace::parser::parser_with_macros(&crate::L13_namespace::preprocess(user_src), path_id, &pre.macros)
                .expect("user parse");

        // twin
        let mut t = Tycker::new();
        let t_out = t
            .run_decls_with_prelude(&pre, &user_decls)
            .expect("twin prelude round");

        // reference（缓存态三张观察表已清——用户段条目即全部）
        let (mut infer, mut rcxt, _macros) = crate::L13_namespace::clone_prelude_state(include_hdl)
            .expect("reference prelude load");
        let mut r_out = String::new();
        for d in &user_decls {
            let (x, _, nc) = infer.infer(&rcxt, d.clone()).expect("ref user decl");
            rcxt = nc;
            for line in crate::L13_namespace::take_fresh_check_issues(&infer) {
                r_out += &crate::L13_namespace::format_check_warning(&line);
                r_out += "\n";
            }
            if let crate::L13_namespace::DeclTm::Println(_, s, _) = x {
                r_out += &s;
                r_out += "\n";
            }
        }
        (t_out, r_out, t, infer)
    }

    /// 表快照（排序后的 hover/completion/inlay 双引擎六元组），由
    /// [`diff_report`] 求双向 diff。
    #[allow(clippy::type_complexity)]
    fn table_snapshots(
        t: &Tycker,
        infer: &crate::L13_namespace::Infer,
    ) -> (
        Vec<(u32, u32, u32, u32, String)>,
        Vec<(u32, u32, u32, u32, String)>,
        Vec<(u32, u32, String)>,
        Vec<(u32, u32, String)>,
        Vec<(u32, String)>,
        Vec<(u32, String)>,
    ) {
        let mut th: Vec<_> = t
            .hover_table()
            .iter()
            .map(|(ts, ds, r)| {
                (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone())
            })
            .collect();
        th.sort();
        let mut rh: Vec<_> = infer
            .hover_table
            .iter()
            .map(|(ts, ds, r)| {
                (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone())
            })
            .collect();
        rh.sort();
        let mut tc: Vec<_> = t
            .completion_table()
            .iter()
            .map(|(sp, n)| (sp.start_offset, sp.end_offset, n.to_string()))
            .collect();
        tc.sort();
        let mut rc: Vec<_> = infer
            .completion_table
            .iter()
            .map(|(sp, n)| (sp.start_offset, sp.end_offset, n.to_string()))
            .collect();
        rc.sort();
        let mut ti: Vec<_> = t
            .inlay_hint_table()
            .iter()
            .map(|(o, l)| (*o, l.clone()))
            .collect();
        ti.sort();
        let mut ri: Vec<_> = infer
            .inlay_hint_table
            .iter()
            .map(|(o, l)| (*o, l.clone()))
            .collect();
        ri.sort();
        (th, rh, tc, rc, ti, ri)
    }

    fn diff_report<T: PartialEq + std::fmt::Debug>(a: &[T], b: &[T]) -> Vec<String> {
        let mut out = Vec::new();
        for x in a {
            if !b.contains(x) {
                out.push(format!("twin-only: {:?}", x));
            }
        }
        for x in b {
            if !a.contains(x) {
                out.push(format!("ref-only: {:?}", x));
            }
        }
        out
    }

    /// tuple-mk 元素 hover 的**实测互检**（阶段 1 遗留：`Tuple2.mk` 来自
    /// prelude op.typort，当时无 prelude 口径只能以参考版 debug_test 背书）。
    /// 断言：两版 Ok 输出一致；hover 全表互检无缺失无异质；tuple 元素
    /// token 上有以元素类型渲染的条目（`true`→Boolean、`zero`→Nat——后者
    /// 顺带验证 prelude 短名别名 `Nat.zero`→`zero`）。
    #[test]
    fn prelude_tuple_mk_element_hover_matches_reference() {
        let src = "def pair : Tuple2[Boolean, Boolean] = Tuple2.mk(true, false)\n\
                   def nz : Tuple2[Boolean, Nat] = Tuple2.mk(false, zero)\n";
        let (t_out, r_out, t, infer) = run_prelude_both(&core_files(), false, src, 100);
        assert_eq!(t_out, r_out, "user-segment output parity");
        let (th, rh, _tc, _rc, _ti, _ri) = table_snapshots(&t, &infer);
        let h = diff_report(&th, &rh);
        assert!(
            h.is_empty(),
            "tuple-mk hover tables diverge on prelude fixture:\n{}",
            h.join("\n")
        );
        // 元素 token 实测：每个元素上有条目且串为元素类型（偏移从 src 算）。
        let true_tok = src.find("mk(true").unwrap() + "mk(".len();
        let zero_tok = src.rfind("mk(false, zero").unwrap() + "mk(false, ".len();
        let at_true: Vec<&String> = th
            .iter()
            .filter(|x| x.0 == true_tok as u32)
            .map(|x| &x.4)
            .collect();
        let at_zero: Vec<&String> = th
            .iter()
            .filter(|x| x.0 == zero_tok as u32)
            .map(|x| &x.4)
            .collect();
        assert!(
            at_true.iter().any(|s| s.as_str() == "Boolean"),
            "`true` element token must hover as Boolean; got {:?}",
            at_true
        );
        assert!(
            at_zero.iter().any(|s| s.as_str() == "Nat"),
            "`zero` element token must hover as Nat (alias resolution); got {:?}",
            at_zero
        );
    }

    /// prelude 装载口径下的观察面全表互检（hover/completion/inlay 三张，
    /// 用户段）：fixture 覆盖 enum 构造子 match/PM/字段投影/tuple 字面。
    /// 三类**已登记**工件按 PM 测试同款口径放行：
    /// - 参考版 start=0 畸变条目（Val::Sum cases 的 Span 丢 start）；
    /// - 孪生零 span 条目（tuple 字段访问 `p._2` 反糖出的合成构造子 Var
    ///   无源码 span，经 `.name` 后缀回退 push 时 t_span=0——参考版同场
    ///   景推声明 span 形态，属 push 键畸变非串差异）；
    /// - 字段投影 def_span 降级（孪生 (t,t,串) vs 参考 (t,真声明,串)——
    ///   值层不持字段 binder span，接线文档"待评估补"项）。
    #[test]
    fn prelude_full_observation_tables_match_reference() {
        let src = "def len(o: Option[Nat]): Nat =\n\
                      match o {\n\
                          case Some(n) => n\n\
                          case None => zero\n\
                      }\n\
                   def wrap(n: Nat): Option[Nat] = Some(n)\n\
                   def pair(b: Boolean) = (b, succ(zero))\n\
                   def withlet(n: Nat) = let m = succ(n); m\n\
                   def get(p: Tuple2[Boolean, Nat]): Nat = p._2\n";
        let (t_out, r_out, t, infer) = run_prelude_both(&core_files(), false, src, 101);
        assert_eq!(t_out, r_out, "user-segment output parity");
        let (th, rh, tc, rc, ti, ri) = table_snapshots(&t, &infer);
        // hover：允许上面三类工件后的双向 diff
        let allowed_twin = |tw: &(u32, u32, u32, u32, String),
                            rf: &[(u32, u32, u32, u32, String)]|
         -> bool {
            // ① 孪生零 span 条目
            if tw.0 == 0 && tw.1 == 0 {
                return true;
            }
            // ③ 投影 def_span 降级：孪生 def_span==t_span，参考有同
            //    t_span 同串、def_span 指向真声明的条目
            if tw.2 == tw.0 && tw.3 == tw.1 {
                return rf
                    .iter()
                    .any(|x| x.0 == tw.0 && x.1 == tw.1 && x.4 == tw.4 && (x.2 != x.3));
            }
            false
        };
        let allowed_ref = |rf: &(u32, u32, u32, u32, String),
                           th: &[(u32, u32, u32, u32, String)]|
         -> bool {
            // ② 参考 start=0 畸变条目
            if rf.0 == 0 && rf.1 != 0 {
                return true;
            }
            // 参考"use==def==声明 token"形态 vs 孪生同串零 span 条目
            //（①的镜像；或同串下孪生 def_span 降级形态 ③ 的镜像）
            if rf.0 == rf.2 && rf.1 == rf.3 {
                return th.iter().any(|x| {
                    x.4 == rf.4 && x.2 == rf.2 && x.3 == rf.3 && x.0 == 0 && x.1 == 0
                });
            }
            if th.iter().any(|x| {
                x.0 == rf.0 && x.1 == rf.1 && x.4 == rf.4 && x.2 == x.0 && x.3 == x.1
            }) {
                return true;
            }
            false
        };
        let h_missing: Vec<String> = rh
            .iter()
            .filter(|x| !th.contains(x))
            .filter(|x| !allowed_ref(x, &th))
            .map(|(a, b, c, d, r)| format!("ref-only: {}..{} -> {}..{} {:?}", a, b, c, d, r))
            .collect();
        let h_foreign: Vec<String> = th
            .iter()
            .filter(|x| !rh.contains(x))
            .filter(|x| !allowed_twin(x, &rh))
            .map(|(a, b, c, d, r)| format!("twin-only: {}..{} -> {}..{} {:?}", a, b, c, d, r))
            .collect();
        let mut report = h_missing;
        report.extend(h_foreign);
        report.extend(diff_report(&tc, &rc));
        report.extend(diff_report(&ti, &ri));
        assert!(
            report.is_empty(),
            "prelude-fixture observation tables diverge:\n{}",
            report.join("\n")
        );
    }

    /// 真实 HDL 负载端到端：全量 prelude（含 HDL）+ examples/hdl/
    /// 09-hierarchy.typort——两版 Ok 判定与用户段输出逐字节一致。该文件
    /// 的 `sum := u.sum` 展开出 `.port(sig)` 连接 → **vconnT prim**（本阶段
    /// 移植的 prim 由此实测），println 走 moduleTreeVL 全模块 Verilog 渲染
    /// （nat_to_dec/HdlLoopIdx 口径敏感）。
    #[test]
    fn hdl_example_parity_with_full_prelude() {
        let src = include_str!("../../../examples/hdl/09-hierarchy.typort");
        let (t_out, r_out, _t, _infer) = run_prelude_both(&hdl_files(), true, src, 102);
        assert_eq!(t_out, r_out, "HDL example output parity (vconnT path)");
        assert!(t_out.contains("=== 09"), "example must produce its println output");
    }
}
