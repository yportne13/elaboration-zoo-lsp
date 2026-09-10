//! 常驻检查点的 arena 压实（docs/lsp-twin-wiring-2026-09.md，内存攻坚）。
//!
//! bump arena 不回收中间值：`prime_resident` 重放 24 文件 prelude 期间产生的
//! 每个值都留在常驻 bump 里（实测 2.05GB 容量 / 1.48GB 已用），而真正**可达**
//! 的稳态状态（decl 表 + meta + 会话全局）参照参考版缓存只有 ~200-300MB。
//! 本模块把可达图深拷进一个按实测大小预置的新 bump，再丢弃旧 bump。
//!
//! **可达根**：
//! - `Resident.cxt`（decl 表、names、telescope/pruning/namespace 链）
//! - `Resident.metas` / `machine.metas`（MetaEntry + MetaSnap，快照含整份 Cxt）
//! - `Resident.mutable` / `machine.mutable`（会话全局）
//! - `machine.defs`（平坦环境区，下标语义 → 保序拷贝即可）
//! - `machine.spine.stack`（tag 2 的下标语义 → 保序拷贝 + 逐槽 remap f/a）
//! - `tm_import` / `val_import`（指针导入表）
//!
//! **无需拷贝**：`TraitState`/`Synth`（引用域 `Rc<Val>` 与 owned `Raw`，无 bump
//! 指针）、`symbol_table`/`import_map`（owned 串）、`trait_method_cache`
//! （引用域 Rc）、`Rc<String>` 渲染串、观察三表（owned）。
//!
//! **值语义**：打包值 `V` 的 tag 0/3/6 是立即数、tag 2 是 spine 下标、tag 5 是
//! meta 下标——一律原样保留（下标因保序拷贝而仍有效）；tag 1/4/7 是指针，逐个
//! 深拷并按旧打包字 memo（值图是 DAG 无环，memo 只为免重复拷共享子树）。

use std::cell::RefCell;
use std::rc::Rc;

use bumpalo::Bump;
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use super::*;

/// 深拷器：旧 bump 读、新 bump 写，按旧指针/旧打包字 memo。
struct Copier<'o, 'n> {
    #[allow(dead_code)]
    old: &'o Bump,
    new: &'n Bump,
    vmap: FxHashMap<u64, V>,
    tmap: FxHashMap<usize, &'n Tm<'n>>,
    xmap: FxHashMap<usize, &'n XCell<'n>>,
    cmap: FxHashMap<usize, &'n CloCell<'n>>,
    pmap: FxHashMap<usize, &'n PiCell<'n>>,
    emap: FxHashMap<usize, &'n EnvCons<'n>>,
    tcmap: FxHashMap<usize, &'n TCons<'n>>,
    lcmap: FxHashMap<usize, &'n LCons<'n>>,
    pcmap: FxHashMap<usize, &'n PrCons<'n>>,
    nmap: FxHashMap<usize, &'n NsCons<'n>>,
    dmap: FxHashMap<usize, Rc<Decls<'n>>>,
    namemap: FxHashMap<usize, Rc<Names>>,
    smap: FxHashMap<usize, Rc<MetaSnap<'static>>>,
    setmap: FxHashMap<usize, Rc<FxHashSet<SmolStr>>>,
    strs: FxHashMap<usize, &'n str>,
}

impl<'o, 'n> Copier<'o, 'n> {
    fn new(old: &'o Bump, new: &'n Bump) -> Self {
        Copier {
            old,
            new,
            vmap: FxHashMap::default(),
            tmap: FxHashMap::default(),
            xmap: FxHashMap::default(),
            cmap: FxHashMap::default(),
            pmap: FxHashMap::default(),
            emap: FxHashMap::default(),
            tcmap: FxHashMap::default(),
            lcmap: FxHashMap::default(),
            pcmap: FxHashMap::default(),
            nmap: FxHashMap::default(),
            dmap: FxHashMap::default(),
            namemap: FxHashMap::default(),
            smap: FxHashMap::default(),
            setmap: FxHashMap::default(),
            strs: FxHashMap::default(),
        }
    }

    fn s(&mut self, x: &'o str) -> &'n str {
        let key = x.as_ptr() as usize;
        if let Some(r) = self.strs.get(&key) {
            return r;
        }
        let r = self.new.alloc_str(x);
        self.strs.insert(key, r);
        r
    }

    // ── 值层 ──────────────────────────────────────────────────────────────

    fn v(&mut self, x: V) -> V {
        match v_tag(x) {
            1 => {
                if let Some(r) = self.vmap.get(&x.0) {
                    return *r;
                }
                let p = v_clo_of::<'o>(x) as *const CloCell<'o> as usize;
                let c = self.clo(unsafe { &*(p as *const CloCell<'o>) });
                let r = v_clo(c);
                self.vmap.insert(x.0, r);
                r
            }
            4 => {
                if let Some(r) = self.vmap.get(&x.0) {
                    return *r;
                }
                let p = v_pi_of::<'o>(x) as *const PiCell<'o> as usize;
                let c = self.pi(unsafe { &*(p as *const PiCell<'o>) });
                let r = v_pi(c);
                self.vmap.insert(x.0, r);
                r
            }
            7 => {
                if let Some(r) = self.vmap.get(&x.0) {
                    return *r;
                }
                let p = v_xcell_of::<'o>(x) as *const XCell<'o> as usize;
                let c = self.xcell(unsafe { &*(p as *const XCell<'o>) });
                let r = v_xcell(c);
                self.vmap.insert(x.0, r);
                r
            }
            // 立即数 / spine 下标 / meta 下标：原样（下标经保序拷贝仍有效）
            _ => x,
        }
    }

    fn clo(&mut self, p: &'o CloCell<'o>) -> &'n CloCell<'n> {
        let key = p as *const CloCell<'o> as usize;
        if let Some(r) = self.cmap.get(&key) {
            return r;
        }
        let name = self.s(p.name);
        let icit = p.icit;
        let env = self.env(p.env);
        let body = self.tm(p.body);
        let c = self.new.alloc(CloCell { name, icit, env, body });
        self.cmap.insert(key, c);
        c
    }

    fn pi(&mut self, p: &'o PiCell<'o>) -> &'n PiCell<'n> {
        let key = p as *const PiCell<'o> as usize;
        if let Some(r) = self.pmap.get(&key) {
            return r;
        }
        let name = self.s(p.name);
        let icit = p.icit;
        let dom = self.v(p.dom);
        let env = self.env(p.env);
        let body = self.tm(p.body);
        let c = self.new.alloc(PiCell { name, icit, dom, env, body });
        self.pmap.insert(key, c);
        c
    }

    fn xcell(&mut self, p: &'o XCell<'o>) -> &'n XCell<'n> {
        let key = p as *const XCell<'o> as usize;
        if let Some(r) = self.xmap.get(&key) {
            return r;
        }
        let b = self.new;
        let c: &'n XCell<'n> = match p {
            XCell::Lit(s) => {
                let s = self.s(s);
                b.alloc(XCell::Lit(s))
            }
            XCell::Nat(k) => b.alloc(XCell::Nat(*k)),
            XCell::Decl { name } => {
                let name = self.s(name);
                b.alloc(XCell::Decl { name })
            }
            XCell::Obj { val, name } => {
                let val = self.v(*val);
                let name = self.s(name);
                b.alloc(XCell::Obj { val, name })
            }
            XCell::Sum { name, params, cases, is_trait } => {
                let name = self.s(name);
                let is_trait = *is_trait;
                let params = self.sum_params_v(params);
                let cases = b.alloc_slice_fill_iter(cases.iter().map(|s| self.s(s)));
                b.alloc(XCell::Sum { name, params, cases, is_trait })
            }
            XCell::SumCase { typ, index, datas, is_trait } => {
                let typ = self.v(*typ);
                let index = *index;
                let is_trait = *is_trait;
                let datas = self.sum_datas_v(datas);
                b.alloc(XCell::SumCase { typ, index, datas, is_trait })
            }
            XCell::Call { name, args, body } => {
                let name = self.s(name);
                let args = b.alloc_slice_fill_iter(args.iter().map(|(a, i)| (self.v(*a), *i)));
                let body = self.v(*body);
                b.alloc(XCell::Call { name, args, body })
            }
            XCell::Match { scrutinee, env, cases } => {
                let scrutinee = self.v(*scrutinee);
                let env = self.env(*env);
                let cases = self.match_tm_cases(cases);
                b.alloc(XCell::Match { scrutinee, env, cases })
            }
        };
        self.xmap.insert(key, c);
        c
    }

    fn sum_params_v(&mut self, ps: &'o [SumParamV<'o>]) -> &'n [SumParamV<'n>] {
        let b = self.new;
        b.alloc_slice_fill_iter(ps.iter().map(|p| SumParamV {
            name: self.s(p.name),
            val: self.v(p.val),
            ty: self.v(p.ty),
            icit: p.icit,
        }))
    }

    fn sum_datas_v(&mut self, ds: &'o [SumDataV<'o>]) -> &'n [SumDataV<'n>] {
        let b = self.new;
        b.alloc_slice_fill_iter(ds.iter().map(|d| SumDataV {
            name: self.s(d.name),
            val: self.v(d.val),
            icit: d.icit,
        }))
    }

    // ── 项层 ──────────────────────────────────────────────────────────────

    fn tm(&mut self, t: &'o Tm<'o>) -> &'n Tm<'n> {
        let key = t as *const Tm<'o> as usize;
        if let Some(r) = self.tmap.get(&key) {
            return r;
        }
        let b = self.new;
        let n: &'n Tm<'n> = match t {
            Tm::Var(i) => b.alloc(Tm::Var(*i)),
            Tm::Decl(s) => {
                let s = self.s(s);
                b.alloc(Tm::Decl(s))
            }
            Tm::Lam(x, i, body) => {
                let x = self.s(x);
                let body = self.tm(body);
                b.alloc(Tm::Lam(x, *i, body))
            }
            Tm::App(f, a, i) => {
                let f = self.tm(f);
                let a = self.tm(a);
                b.alloc(Tm::App(f, a, *i))
            }
            Tm::AppPruning(h, pr) => {
                let h = self.tm(h);
                let pr = pr.map(|p| self.prcons(p));
                b.alloc(Tm::AppPruning(h, pr))
            }
            Tm::U(u) => b.alloc(Tm::U(*u)),
            Tm::Pi(x, i, a, body) => {
                let x = self.s(x);
                let a = self.tm(a);
                let body = self.tm(body);
                b.alloc(Tm::Pi(x, *i, a, body))
            }
            Tm::Let(x, a, v, body) => {
                let x = self.s(x);
                let a = self.tm(a);
                let v = self.tm(v);
                let body = self.tm(body);
                b.alloc(Tm::Let(x, a, v, body))
            }
            Tm::Meta(m) => b.alloc(Tm::Meta(*m)),
            Tm::LiteralType => b.alloc(Tm::LiteralType),
            Tm::LiteralIntro(s) => {
                let s = self.s(s);
                b.alloc(Tm::LiteralIntro(s))
            }
            Tm::Obj(h, f) => {
                let h = self.tm(h);
                let f = self.s(f);
                b.alloc(Tm::Obj(h, f))
            }
            Tm::Sum(name, params, cases, is_trait) => {
                let name = self.s(name);
                let is_trait = *is_trait;
                let params = b.alloc_slice_fill_iter(params.iter().map(|p| SumParamT {
                    name: self.s(p.name),
                    val: self.tm(p.val),
                    ty: self.tm(p.ty),
                    icit: p.icit,
                }));
                let cases = b.alloc_slice_fill_iter(cases.iter().map(|s| self.s(s)));
                b.alloc(Tm::Sum(name, params, cases, is_trait))
            }
            Tm::SumCase { typ, index, datas, is_trait } => {
                let typ = self.tm(typ);
                let index = *index;
                let is_trait = *is_trait;
                let datas = b.alloc_slice_fill_iter(datas.iter().map(|d| SumDataT {
                    name: self.s(d.name),
                    val: self.tm(d.val),
                    icit: d.icit,
                }));
                b.alloc(Tm::SumCase { typ, index, datas, is_trait })
            }
            Tm::Match(s, cases) => {
                let s = self.tm(s);
                let cases = self.match_tm_cases(cases);
                b.alloc(Tm::Match(s, cases))
            }
            Tm::Call(name, args, body) => {
                let name = self.s(name);
                let args = b.alloc_slice_fill_iter(args.iter().map(|(a, i)| (self.tm(a), *i)));
                let body = self.tm(body);
                b.alloc(Tm::Call(name, args, body))
            }
        };
        self.tmap.insert(key, n);
        n
    }

    fn match_tm_cases(
        &mut self,
        cases: &'o [(PatternDetail, &'o Tm<'o>)],
    ) -> &'n [(PatternDetail, &'n Tm<'n>)] {
        let b = self.new;
        b.alloc_slice_fill_iter(cases.iter().map(|(p, t)| (p.clone(), self.tm(t))))
    }

    // ── 环境 / 链 ─────────────────────────────────────────────────────────

    /// 平坦区是 `defs` 下标（保序拷贝仍有效），只拷 binds 链。
    fn env(&mut self, e: Env<'o>) -> Env<'n> {
        Env {
            flat_base: e.flat_base,
            flat_len: e.flat_len,
            binds: e.binds.map(|c| self.envcons(c)),
        }
    }

    fn envcons(&mut self, c: &'o EnvCons<'o>) -> &'n EnvCons<'n> {
        let key = c as *const EnvCons<'o> as usize;
        if let Some(r) = self.emap.get(&key) {
            return r;
        }
        let val = self.v(c.val);
        let next = c.next.map(|n| self.envcons(n));
        let n = self.new.alloc(EnvCons { val, next });
        self.emap.insert(key, n);
        n
    }

    fn tcons(&mut self, c: &'o TCons<'o>) -> &'n TCons<'n> {
        let key = c as *const TCons<'o> as usize;
        if let Some(r) = self.tcmap.get(&key) {
            return r;
        }
        let name = self.s(c.name);
        let ty = self.v(c.ty);
        let source = c.source;
        let next = c.next.map(|n| self.tcons(n));
        let n = self.new.alloc(TCons { name, ty, source, next });
        self.tcmap.insert(key, n);
        n
    }

    fn lcons(&mut self, c: &'o LCons<'o>) -> &'n LCons<'n> {
        let key = c as *const LCons<'o> as usize;
        if let Some(r) = self.lcmap.get(&key) {
            return r;
        }
        let name = self.s(c.name);
        let a_t = self.tm(c.a_t);
        let t_t = c.t_t.map(|t| self.tm(t));
        let next = c.next.map(|n| self.lcons(n));
        let n = self.new.alloc(LCons { name, a_t, t_t, next });
        self.lcmap.insert(key, n);
        n
    }

    fn prcons(&mut self, c: &'o PrCons<'o>) -> &'n PrCons<'n> {
        let key = c as *const PrCons<'o> as usize;
        if let Some(r) = self.pcmap.get(&key) {
            return r;
        }
        let slot = c.slot;
        let none_run = c.none_run;
        let after_run = c.after_run.map(|n| self.prcons(n));
        let next = c.next.map(|n| self.prcons(n));
        let n = self.new.alloc(PrCons { slot, none_run, after_run, next });
        self.pcmap.insert(key, n);
        n
    }

    fn nscons(&mut self, c: &'o NsCons<'o>) -> &'n NsCons<'n> {
        let key = c as *const NsCons<'o> as usize;
        if let Some(r) = self.nmap.get(&key) {
            return r;
        }
        let val = self.v(c.val);
        let methods = self.new.alloc_slice_fill_iter(c.methods.iter().cloned());
        let type_name = self.s(c.type_name);
        let next = c.next.map(|n| self.nscons(n));
        let n = self.new.alloc(NsCons { val, methods, type_name, next });
        self.nmap.insert(key, n);
        n
    }

    // ── 表 / 上下文 ───────────────────────────────────────────────────────

    fn decls(&mut self, d: &Rc<Decls<'o>>) -> Rc<Decls<'n>> {
        let key = Rc::as_ptr(d) as usize;
        if let Some(r) = self.dmap.get(&key) {
            return r.clone();
        }
        let mut out: Decls<'n> = FxHashMap::default();
        for (k, e) in d.iter() {
            let tm = self.tm(e.tm);
            let ty = self.tm(e.ty);
            let val = self.v(e.val);
            let vty = self.v(e.vty);
            let span = e.span;
            let prim = e.prim;
            let typ_pretty = e.typ_pretty.clone();
            out.insert(k.clone(), DeclEntry { span, typ_pretty, tm, ty, val, vty, prim });
        }
        let r = Rc::new(out);
        self.dmap.insert(key, r.clone());
        r
    }

    fn names(&mut self, n: &Rc<Names>) -> Rc<Names> {
        let key = Rc::as_ptr(n) as usize;
        if let Some(r) = self.namemap.get(&key) {
            return r.clone();
        }
        let by_name = n.by_name.clone();
        let mut by_lvl: FxHashMap<u32, (V, crate::parser_lib::Span<()>)> = FxHashMap::default();
        for (lvl, (v, sp)) in n.by_lvl.iter() {
            by_lvl.insert(*lvl, (self.v(*v), *sp));
        }
        let r = Rc::new(Names { by_name, by_lvl });
        self.namemap.insert(key, r.clone());
        r
    }

    fn strset(&mut self, s: &Rc<FxHashSet<SmolStr>>) -> Rc<FxHashSet<SmolStr>> {
        let key = Rc::as_ptr(s) as usize;
        if let Some(r) = self.setmap.get(&key) {
            return r.clone();
        }
        let r = Rc::new((**s).clone());
        self.setmap.insert(key, r.clone());
        r
    }

    /// Snapshot is stored with the 'static convention (MetaEntry hardcodes
    /// MetaSnap<'static>): build at 'n then re-tag the Rc pointer as 'static,
    /// matching the resident's own storage convention (the bump lives as long
    /// as the resident, and compaction re-copies).
    fn snap(&mut self, s: &Rc<MetaSnap<'o>>) -> Rc<MetaSnap<'static>> {
        let key = Rc::as_ptr(s) as usize;
        if let Some(r) = self.smap.get(&key) {
            return r.clone();
        }
        let lvl = s.lvl;
        let types = s.types.map(|t| self.tcons(t));
        let decls = self.decls(&s.decls);
        let cxt = self.cxt(&s.cxt);
        let inner: Rc<MetaSnap<'n>> = Rc::new(MetaSnap {
            lvl,
            types,
            decls,
            cxt: unsafe { std::mem::transmute::<Cxt<'n>, Cxt<'static>>(cxt) },
        });
        let r: Rc<MetaSnap<'static>> =
            unsafe { Rc::from_raw(Rc::into_raw(inner) as *const MetaSnap<'static>) };
        self.smap.insert(key, r.clone());
        r
    }

    fn cxt(&mut self, c: &Cxt<'o>) -> Cxt<'n> {
        let env = self.env(c.env);
        let names = self.names(&c.names);
        let types = c.types.map(|t| self.tcons(t));
        let locals = c.locals.map(|l| self.lcons(l));
        let pruning = c.pruning.map(|p| self.prcons(p));
        let decls = self.decls(&c.decls);
        let namespace = c.namespace.map(|n| self.nscons(n));
        let namespaces = self.strset(&c.namespaces);
        Cxt {
            env,
            update_from: c.update_from,
            names,
            types,
            locals,
            pruning,
            binds: c.binds,
            lvl: c.lvl,
            decls,
            namespace,
            namespace_prefix: c.namespace_prefix.clone(),
            namespaces,
            binding_name: c.binding_name.clone(),
        }
    }

    fn metas(&mut self, ms: &'o [MetaEntry]) -> Vec<MetaEntry> {
        ms.iter()
            .map(|m| match m {
                MetaEntry::Solved(a, b) => {
                    let a = self.v(*a);
                    let b = self.v(*b);
                    MetaEntry::Solved(a, b)
                }
                MetaEntry::Unsolved(a, snap, o, sp) => {
                    let a = self.v(*a);
                    let snap = self.snap(snap);
                    let o = self.v(*o);
                    MetaEntry::Unsolved(a, snap, o, *sp)
                }
            })
            .collect()
    }

    fn mutable(&mut self, m: &Mutable) -> Mutable {
        let mut map: FxHashMap<SmolStr, V> = FxHashMap::default();
        for (k, v) in m.map.iter() {
            map.insert(k.clone(), self.v(*v));
        }
        Mutable { map, replay: m.replay.clone() }
    }

    /// `tm_import` 的字段类型是 `&'static Tm<'static>`（'static 存放口径），
    /// 拷出的新引用同样按该口径存放。
    fn tm_import(
        &mut self,
        m: &'o FxHashMap<usize, &'static Tm<'static>>,
    ) -> FxHashMap<usize, &'static Tm<'static>> {
        let mut out: FxHashMap<usize, &'static Tm<'static>> = FxHashMap::default();
        for (k, t) in m.iter() {
            let t: &'o Tm<'o> =
                unsafe { std::mem::transmute::<&'static Tm<'static>, &'o Tm<'o>>(*t) };
            let n = self.tm(t);
            out.insert(*k, unsafe { std::mem::transmute::<&'n Tm<'n>, &'static Tm<'static>>(n) });
        }
        out
    }

    fn val_import(&mut self, m: &FxHashMap<usize, V>) -> FxHashMap<usize, V> {
        m.iter().map(|(k, v)| (*k, self.v(*v))).collect()
    }

    fn defs(&mut self, d: &[V]) -> Vec<V> {
        d.iter().map(|v| self.v(*v)).collect()
    }

    fn spine(&mut self, st: &[Entry]) -> Vec<Entry> {
        st.iter()
            .map(|e| Entry {
                f: self.v(e.f),
                a: self.v(e.a),
                icit: e.icit,
                len: e.len,
                base: e.base,
                hk: e.hk,
            })
            .collect()
    }
}

/// 压实开关（`TYPORT_TWIN_NO_COMPACT` 置位则关闭，对照测量用）。
pub(super) fn compact_enabled() -> bool {
    std::env::var_os("TYPORT_TWIN_NO_COMPACT").is_none()
}

impl Tycker {
    /// **就地压实**：把 `cxt`（'static 存放口径，指向当前 bump）与 machine
    /// 的 bump 可达状态深拷进一个按 `cap_hint` 预置的新 bump，换掉
    /// `self.bump`（旧 bump 随即释放）。返回 `(新 cxt, 新 bump 已用字节)`。
    /// prime 的每个文件边界与收尾各调一次，使 arena 始终只承载可达状态
    /// （不压实则 prime 期间累积 ~2GB 垃圾，峰值 RSS 1.8GB）。
    pub(super) fn compact_state(&mut self, cxt: Cxt<'static>, cap_hint: usize) -> (Cxt<'static>, usize) {
        let old = std::mem::replace(&mut self.bump, Bump::with_capacity(1 << 20));
        let nb = Bump::with_capacity(cap_hint.max(1 << 20));
        let (new_cxt, metas, mut_, tm_imp, val_imp, defs, spine) = {
            let mut c = Copier::new(&old, &nb);
            let cxt = c.cxt(&cxt);
            // 立刻把 cxt 重标为 'static：它是唯一借用 `nb` 的返回值，重标后
            // 该借用结束，才能在后面把 `nb` move 进 `self.bump`。
            let cxt: Cxt<'static> =
                unsafe { std::mem::transmute::<Cxt<'_>, Cxt<'static>>(cxt) };
            let metas = c.metas(&self.machine.metas);
            let mut_ = c.mutable(&self.machine.mutable.borrow());
            let tm_imp = c.tm_import(&self.machine.tm_import);
            let val_imp = c.val_import(&self.machine.val_import);
            let defs = c.defs(&self.machine.defs);
            let spine = c.spine(&self.machine.spine.stack);
            (cxt, metas, mut_, tm_imp, val_imp, defs, spine)
        };
        drop(old);
        self.machine.metas = metas;
        self.machine.mutable = RefCell::new(mut_);
        self.machine.tm_import = tm_imp;
        self.machine.val_import = val_imp;
        self.machine.defs = defs;
        self.machine.spine = Spine { stack: spine };
        // 指针/值型 scratch 在检查点处应已空，或使用前会被各自入口 clear；
        // 全部清掉，杜绝任何指向旧 bump 的陈旧引用被读到。
        self.machine.eval_work.clear();
        self.machine.quote_tasks.clear();
        self.machine.quote_done.clear();
        self.machine.quote_work.clear();
        self.machine.unify_work.clear();
        self.machine.unify_stack.clear();
        self.machine.quote_memo.clear();
        self.machine.vals.clear();
        self.machine.icits.clear();
        self.machine.constraints.clear();
        self.bump = nb;
        let used = self
            .bump
            .allocated_bytes()
            .saturating_sub(self.bump.chunk_capacity());
        (new_cxt, used)
    }
}
