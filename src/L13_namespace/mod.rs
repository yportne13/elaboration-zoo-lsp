     1|use colored::Colorize;
     2|use cxt::Cxt;
     3|use parser::{syntax::{Either, Icit, Raw}, IError};
     4|use pattern_match::Compiler;
     5|use smol_str::SmolStr;
     6|use syntax::{Pruning, close_ty};
     7|use pretty::pretty_tm;
     8|
     9|use crate::list::List;
    10|use crate::parser_lib::Span;
    11|
    12|pub mod cxt;
    13|mod elaboration;
    14|pub mod parser;
    15|mod pattern_match;
    16|mod syntax;
    17|mod unification;
    18|mod typeclass;
    19|pub mod pretty;
    20|mod canonical;
    21|
    22|#[cfg(test)]
    23|mod legacy_tests;
    24|
    25|type Rc<T> = std::sync::Arc<T>;
    26|
    27|type Decl = HashMap<SmolStr, (Span<()>, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>)>;
    28|
    29|#[derive(Debug, Clone, Copy, PartialEq)]
    30|pub struct MetaVar(u32);
    31|
    32|#[derive(Debug, Clone)]
    33|pub enum MetaEntry {
    34|    Solved(Rc<Val>, Rc<VTy>),
    35|    Unsolved(Rc<VTy>, Cxt, Rc<VTy>),
    36|}
    37|
    38|#[derive(Debug, Clone, Copy)]
    39|pub struct Ix(u32);
    40|
    41|#[derive(Debug, Clone)]
    42|enum BD {
    43|    Bound,
    44|    Defined,
    45|}
    46|
    47|#[derive(Clone, Debug)]
    48|pub enum DeclTm {
    49|    Def {
    50|        name: Span<SmolStr>,
    51|        typ: Rc<Val>,
    52|        body: Rc<Val>,
    53|        typ_pretty: String,
    54|        body_pretty: String,
    55|    },
    56|    Println(Rc<Tm>, String, Span<()>),
    57|    Enum {
    58|        //TODO:
    59|    },
    60|    Trait {
    61|        //TODO:
    62|    },
    63|    TraitImpl {
    64|        //TODO:
    65|    },
    66|    Package,
    67|    Import,
    68|}
    69|
    70|#[derive(Clone)]
    71|pub struct PrimFunc(Rc<dyn Fn(&Infer, &Decl, &Env, Rc<Val>) -> Rc<Val> + Send + Sync>);
    72|
    73|impl std::fmt::Debug for PrimFunc {
    74|    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    75|        write!(f, "PrimFunc")
    76|    }
    77|}
    78|
    79|#[derive(Debug, Clone)]
    80|pub enum Tm {
    81|    Var(Ix),
    82|    Decl(Span<SmolStr>),
    83|    Obj(Rc<Tm>, Span<SmolStr>),
    84|    Lam(Span<SmolStr>, Icit, Rc<Tm>),
    85|    App(Rc<Tm>, Rc<Tm>, Icit),
    86|    AppPruning(Rc<Tm>, Pruning),
    87|    U(u32),
    88|    Pi(Span<SmolStr>, Icit, Rc<Ty>, Rc<Ty>),
    89|    Let(Span<SmolStr>, Rc<Ty>, Rc<Tm>, Rc<Tm>),
    90|    Meta(MetaVar),
    91|    LiteralType,
    92|    LiteralIntro(Span<String>),
    93|    Prim(Rc<Val>, PrimFunc),
    94|    Sum(Span<SmolStr>, TmSumParams, TmSumCases, bool),
    95|    SumCase {
    96|        typ: Rc<Tm>,
    97|        case_name: Span<SmolStr>,
    98|        datas: TmSumCaseDatas,
    99|        is_trait: bool,
   100|    },
   101|    Match(Rc<Tm>, Vec<(PatternDetail, Rc<Tm>)>),
   102|    /// Call(name, display_args, val_args, body) - body was inlined from function `name`
   103|    Call(SmolStr, List<(Rc<Tm>, Icit)>, Rc<Tm>),
   104|}
   105|
   106|impl Tm {
   107|    pub fn no_metas(&self, infer: &Infer, decl: &Decl, l: Lvl) -> Option<(Cxt, Rc<Val>)> {
   108|        match self {
   109|            Tm::Var(_) | Tm::Decl(_) | Tm::U(_) | Tm::LiteralType | Tm::LiteralIntro(_) | Tm::Prim(_, _) => None,
   110|            Tm::Obj(tm, _) => tm.no_metas(infer, decl, l),
   111|            Tm::Lam(_, _, t) => t.no_metas(infer, decl, l + 1),
   112|            Tm::App(t, u, _) => t.no_metas(infer, decl, l).or_else(|| u.no_metas(infer, decl, l)),
   113|            Tm::AppPruning(t, _) => {
   114|                t.no_metas(infer, decl, l)
   115|            },
   116|            Tm::Pi(_, _, t, u) => t.no_metas(infer, decl, l).or_else(|| u.no_metas(infer, decl, l + 1)),
   117|            Tm::Let(_, a, t, u) => a.no_metas(infer, decl, l).or_else(|| t.no_metas(infer, decl, l)).or_else(|| u.no_metas(infer, decl, l)),
   118|            Tm::Meta(m) => match infer.lookup_meta(*m) {
   119|                MetaEntry::Unsolved(_, cxt, oty) => Some((cxt.clone(), oty.clone())),
   120|                MetaEntry::Solved(v, _) => {
   121|                    infer.quote(decl, l, v).no_metas(infer, decl, l)
   122|                }
   123|            },
   124|            Tm::Sum(_, items, _, _) => items.iter().flat_map(|(_, t, ty, _)| t.no_metas(infer, decl, l).or_else(|| ty.no_metas(infer, decl, l))).next(),
   125|            Tm::SumCase { typ, case_name: _, datas, is_trait: _ } => typ.no_metas(infer, decl, l)
   126|                .or_else(|| datas.iter().flat_map(|(_, t, _)| t.no_metas(infer, decl, l)).next()),
   127|            Tm::Match(tm, items) => tm.no_metas(infer, decl, l).or_else(|| items.iter().flat_map(|(_, t)| t.no_metas(infer, decl, l)).next()),
   128|            Tm::Call(_, args, body) => args.iter().flat_map(|(a, _)| a.no_metas(infer, decl, l)).next().or_else(|| body.no_metas(infer, decl, l)),
   129|        }
   130|    }
   131|}
   132|
   133|#[derive(Clone, Debug, PartialEq)]
   134|pub enum PatternDetail {
   135|    Any(Span<()>),
   136|    Bind(Span<SmolStr>),
   137|    Con(Span<SmolStr>, Vec<PatternDetail>),
   138|}
   139|
   140|impl PatternDetail {
   141|    fn bind_count(&self) -> u32 {
   142|        match self {
   143|            PatternDetail::Any(_) => 1,
   144|            PatternDetail::Bind(_) => 1,
   145|            PatternDetail::Con(_, pattern_details) => {
   146|                pattern_details.iter().map(|pattern_detail| pattern_detail.bind_count()).sum::<u32>()
   147|            },
   148|        }
   149|    }
   150|    fn bind_names(&self, ns: &List<SmolStr>) -> List<SmolStr> {
   151|        match self {
   152|            PatternDetail::Any(_) => ns.prepend(SmolStr::new("_")),
   153|            PatternDetail::Bind(name) => ns.prepend(name.data.clone()),
   154|            PatternDetail::Con(_, pattern_details) => {
   155|                pattern_details
   156|                    .iter()
   157|                    .fold(ns.clone(), |ns, pattern_detail| pattern_detail.bind_names(&ns))
   158|            },
   159|        }
   160|    }
   161|    fn bind_cxt(&self, cxt: &Cxt) -> Cxt {
   162|        match self {
   163|            PatternDetail::Any(_) => cxt.clone(),
   164|            PatternDetail::Bind(name) => cxt.bind(name.clone(), Tm::U(0).into(), Val::U(0).into()),
   165|            PatternDetail::Con(_, pattern_details) => {
   166|                pattern_details
   167|                    .iter()
   168|                    .fold(cxt.clone(), |cxt, pattern_detail| pattern_detail.bind_cxt(&cxt))
   169|            },
   170|        }
   171|    }
   172|}
   173|
   174|impl std::fmt::Display for PatternDetail {
   175|    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
   176|        match self {
   177|            PatternDetail::Any(_) => write!(f, "_"),
   178|            PatternDetail::Bind(name) => write!(f, "{}", name.data),
   179|            PatternDetail::Con(name, pattern_details) => {
   180|                let p = pattern_details
   181|                    .iter()
   182|                    .map(|pattern_detail| pattern_detail.to_string())
   183|                    .collect::<Vec<_>>();
   184|                if p.is_empty() {
   185|                    write!(f, "{}", name.data)
   186|                } else {
   187|                    write!(f, "{}({})", name.data, p.join(", "))
   188|                }
   189|            }
   190|        }
   191|    }
   192|}
   193|
   194|type Ty = Tm;
   195|
   196|#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd)]
   197|pub struct Lvl(u32);
   198|
   199|impl Add<u32> for Lvl {
   200|    type Output = Lvl;
   201|    fn add(self, rhs: u32) -> Lvl {
   202|        Lvl(self.0 + rhs)
   203|    }
   204|}
   205|
   206|impl Sub<u32> for Lvl {
   207|    type Output = Lvl;
   208|    fn sub(self, rhs: u32) -> Lvl {
   209|        Lvl(self.0 - rhs)
   210|    }
   211|}
   212|
   213|type Env = List<Rc<Val>>;
   214|type Spine = List<(Rc<Val>, Icit)>;
   215|
   216|#[derive(Clone)]
   217|pub struct Closure(Env, Rc<Tm>);
   218|
   219|impl std::fmt::Debug for Closure {
   220|    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
   221|        write!(f, "Closure(..{}, {:?})", self.0.len(), self.1)
   222|    }
   223|}
   224|
   225|#[derive(Debug, Clone)]
   226|pub enum Val {
   227|    Flex(MetaVar, Spine),
   228|    Rigid(Lvl, Spine),
   229|    Decl(Span<SmolStr>, Spine),
   230|    Obj(Rc<Val>, Span<SmolStr>, Spine),
   231|    Lam(Span<SmolStr>, Icit, Closure),
   232|    Pi(Span<SmolStr>, Icit, Rc<VTy>, Closure),
   233|    U(u32),
   234|    LiteralType,
   235|    LiteralIntro(Span<String>),
   236|    Prim(Rc<Val>, PrimFunc),
   237|    Sum(
   238|        Span<SmolStr>,
   239|        SumParams,
   240|        SumCases,
   241|        bool,
   242|    ),
   243|    SumCase {
   244|        is_trait: bool,
   245|        typ: Rc<Val>,
   246|        case_name: Span<SmolStr>,
   247|        datas: SumCaseDatas,
   248|    },
   249|    Match(Rc<Val>, Env, Vec<(PatternDetail, Rc<Tm>)>),
   250|    /// Call(name, args, body) - value inlined from function `name`
   251|    Call(SmolStr, List<(Rc<Val>, Icit)>, Rc<Val>),
   252|}
   253|
   254|type VTy = Val;
   255|
   256|// Arc-wrapped Vec types to avoid deep cloning on Sum/SumCase clones
   257|type SumParams = Rc<Vec<(Span<SmolStr>, Rc<Val>, Rc<VTy>, Icit)>>;
   258|type SumCases = Rc<Vec<Span<SmolStr>>>;
   259|type SumCaseDatas = Rc<Vec<(Span<SmolStr>, Rc<Val>, Icit)>>;
   260|type TmSumParams = Rc<Vec<(Span<SmolStr>, Rc<Tm>, Rc<Ty>, Icit)>>;
   261|type TmSumCases = Rc<Vec<Span<SmolStr>>>;
   262|type TmSumCaseDatas = Rc<Vec<(Span<SmolStr>, Rc<Tm>, Icit)>>;
   263|
   264|impl Val {
   265|    fn vvar(x: Lvl) -> Self {
   266|        Val::Rigid(x, List::new())
   267|    }
   268|
   269|    fn vmeta(m: MetaVar) -> Self {
   270|        Val::Flex(m, List::new())
   271|    }
   272|}
   273|
   274|fn lvl2ix(l: Lvl, x: Lvl) -> Ix {
   275|    Ix(l.0 - x.0 - 1)
   276|}
   277|
   278|pub fn tm_contains_match(tm: &Tm) -> bool {
   279|    match tm {
   280|        Tm::Match(..) => true,
   281|        Tm::Lam(_, _, body) => tm_contains_match(body),
   282|        _ => false,
   283|    }
   284|}
   285|
   286|pub fn wrap_match_in_call(name: SmolStr, tm: &Tm, _l: u32) -> Tm {
   287|    fn go(name: SmolStr, tm: &Tm, l: u32, icits: &mut Vec<Icit>) -> Tm {
   288|        match tm {
   289|            Tm::Lam(span, i, body) => {
   290|                icits.push(*i);
   291|                let result = Tm::Lam(span.clone(), *i, go(name, body, l + 1, icits).into());
   292|                icits.pop();
   293|                result
   294|            }
   295|            Tm::Match(scru, cases) => Tm::Call(
   296|                name,
   297|                {
   298|                    let mut list = List::new();
   299|                    for i in 0..l {
   300|                        list = list.prepend((Tm::Var(Ix(i)).into(), icits[(l - 1 - i) as usize]));
   301|                    }
   302|                    list
   303|                },
   304|                Tm::Match(scru.clone(), cases.clone()).into(),
   305|            ),
   306|            _ => tm.clone(),
   307|        }
   308|    }
   309|    go(name, tm, 0, &mut Vec::new())
   310|}
   311|
   312|pub fn count_lams(tm: &Tm) -> u32 {
   313|    match tm {
   314|        Tm::Lam(_, _, body) => 1 + count_lams(body),
   315|        _ => 0,
   316|    }
   317|}
   318|
   319|use std::ops::{Add, Sub};
   320|use im::{HashMap, HashSet};
   321|
   322|#[derive(Debug)]
   323|pub enum UnifyError {
   324|    Basic,
   325|    Stuck,
   326|    Trait(String),
   327|}
   328|
   329|fn empty_span<T>(data: T) -> Span<T> {
   330|    Span {
   331|        data,
   332|        start_offset: 0,
   333|        end_offset: 0,
   334|        path_id: 0,
   335|    }
   336|}
   337|
   338|pub struct Error(
   339|    pub Span<String>,
   340|    pub Vec<Box<dyn Fn() -> Option<String> + Send + Sync>>
   341|);
   342|
   343|impl std::fmt::Debug for Error {
   344|    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
   345|        // 只渲染第一个字段，输出效果如：Error(Span { ... })
   346|        f.debug_tuple("Error")
   347|            .field(&self.0)
   348|            .finish()
   349|    }
   350|}
   351|
   352|impl IError {
   353|    pub fn to_err(self) -> Error {
   354|        Error(self.msg.map(|x| format!("{:?}", x)), vec![])
   355|    }
   356|}
   357|
   358|#[derive(Clone)]
   359|pub struct Infer {
   360|    pub meta: Vec<MetaEntry>,
   361|    pub meta_contrains: Vec<(Rc<Val>, Rc<Val>)>,
   362|    trait_solver: typeclass::Synth,
   363|    trait_definition: HashMap<SmolStr, (Vec<(Span<SmolStr>, Raw, Icit)>, Vec<bool>, Vec<(Span<SmolStr>, Vec<(Span<SmolStr>, Raw, Icit)>, Raw)>)>,
   364|    trait_out_param: HashMap<SmolStr, Vec<bool>>,
   365|    pub mutable_map: Rc<std::sync::RwLock<HashMap<String, Rc<Val>>>>,
   366|    pub hover_table: Vec<(Span<()>, Span<()>, Cxt, Rc<Val>)>,
   367|    pub completion_table: Vec<(Span<()>, SmolStr)>,
   368|}
   369|
   370|impl Infer {
   371|    pub fn new() -> Self {
   372|        Self {
   373|            meta: vec![],
   374|            meta_contrains: vec![],
   375|            trait_solver: Default::default(),
   376|            trait_definition: Default::default(),
   377|            trait_out_param: Default::default(),
   378|            mutable_map: Default::default(),
   379|            hover_table: vec![],
   380|            completion_table: vec![],
   381|        }
   382|    }
   383|
   384|<<<<<<< HEAD
   385|    pub fn meta_len(&self) -> usize { self.meta.len() }
   386|    pub fn meta_capacity(&self) -> usize { self.meta.capacity() }
   387|    pub fn meta_contrains_len(&self) -> usize { self.meta_contrains.len() }
   388|    pub fn meta_contrains_capacity(&self) -> usize { self.meta_contrains.capacity() }
   389|    pub fn trait_definition_len(&self) -> usize { self.trait_definition.len() }
   390|=======
   391|    pub fn memory_stats(&self) -> serde_json::Value {
   392|        use serde_json::json;
   393|        let total = self.meta.len();
   394|        let solved = self.meta.iter().filter(|m| matches!(m, MetaEntry::Solved(..))).count();
   395|        let unsolved = self.meta.iter().filter(|m| matches!(m, MetaEntry::Unsolved(..))).count();
   396|        let meta_cap = self.meta.capacity();
   397|        let MetaEntry_sz = std::mem::size_of::<MetaEntry>();
   398|        let hover_len = self.hover_table.len();
   399|        let hover_cap = self.hover_table.capacity();
   400|        let constraints_len = self.meta_contrains.len();
   401|        let completions_len = self.completion_table.len();
   402|        json!({
   403|            "meta_entries": {
   404|                "total": total,
   405|                "solved": solved,
   406|                "unsolved": unsolved,
   407|                "capacity": meta_cap,
   408|                "entry_size": MetaEntry_sz,
   409|                "vec_allocation_bytes": meta_cap * MetaEntry_sz,
   410|            },
   411|            "hover_table": {
   412|                "len": hover_len,
   413|                "capacity": hover_cap,
   414|            },
   415|            "meta_contrains": {
   416|                "len": constraints_len,
   417|            },
   418|            "completion_table": {
   419|                "len": completions_len,
   420|            },
   421|        })
   422|    }
   423|>>>>>>> feat(bench): add memory benchmark infra with --stats flag
   424|    fn new_meta(&mut self, a: Rc<VTy>, cxt: Cxt, origin_typ: Rc<VTy>) -> u32 {
   425|        self.meta.push(MetaEntry::Unsolved(a, cxt, origin_typ));
   426|        self.meta.len() as u32 - 1
   427|    }
   428|    fn fresh_meta(&mut self, cxt: &Cxt, a: Rc<VTy>) -> Rc<Tm> {
   429|        if let Ok(Some((a, _))) = self.solve_trait(cxt, &a, false) {
   430|            a
   431|        } else if let Val::Sum(_, _, _, true) = a.as_ref() {
   432|            let m = self.new_meta(a.clone(), cxt.clone(), a);
   433|            Tm::Meta(MetaVar(m)).into()
   434|        } else {
   435|            let closed = self.eval(
   436|                &cxt.decl,
   437|                &List::new(),
   438|                &close_ty(&cxt.locals, self.quote(&cxt.decl, cxt.lvl, &a)),
   439|            );
   440|            let m = self.new_meta(closed, cxt.clone(), a);
   441|            Tm::AppPruning(Tm::Meta(MetaVar(m)).into(), cxt.pruning.clone()).into()
   442|        }
   443|    }
   444|    fn lookup_meta(&self, m: MetaVar) -> &MetaEntry {
   445|        &self.meta[m.0 as usize]
   446|    }
   447|    fn force(&self, decl: &Decl, t: &Rc<Val>) -> Rc<Val> {
   448|        //println!("{} {:?}", "force".red(), t);
   449|        match t.as_ref() {
   450|            Val::Flex(m, sp) => match self.lookup_meta(*m) {
   451|                MetaEntry::Solved(t_solved, _) => self.force(decl, &self.v_app_sp(decl, t_solved.clone(), sp)),
   452|                MetaEntry::Unsolved(_, _, _) => Val::Flex(*m, sp.clone()).into(),
   453|            },
   454|            Val::Obj(x, a, b) => {
   455|                Val::Obj(self.force(decl, x), a.clone(), b.clone()).into()
   456|            },
   457|            Val::Call(name, args, body) => {
   458|                Val::Call(name.clone(), args.clone(), self.force(decl, body)).into()
   459|            },
   460|            _ => t.clone(),
   461|        }
   462|    }
   463|    fn v_meta(&self, m: MetaVar) -> Rc<Val> {
   464|        match self.lookup_meta(m) {
   465|            MetaEntry::Solved(v, _) => v.clone(),
   466|            MetaEntry::Unsolved(_, _, _) => Val::vmeta(m).into(),
   467|        }
   468|    }
   469|
   470|    fn closure_apply(&self, decl: &Decl, closure: &Closure, u: Rc<Val>) -> Rc<Val> {
   471|        //println!("{} {:?} {:?}", "closure apply".yellow(), closure, u);
   472|        self.eval(decl, &closure.0.prepend(u), &closure.1)
   473|    }
   474|
   475|    fn v_app(&self, decl: &Decl, t: &Rc<Val>, u: Rc<Val>, i: Icit) -> Rc<Val> {
   476|        //println!("v_app {t:?} {u:?}");
   477|        match t.as_ref() {
   478|            Val::Lam(_, _, closure) => self.closure_apply(decl, closure, u),
   479|            Val::Flex(m, sp) => Val::Flex(*m, sp.prepend((u, i))).into(),
   480|            Val::Rigid(x, sp) => Val::Rigid(*x, sp.prepend((u, i))).into(),
   481|            Val::Decl(x, sp) => Val::Decl(x.clone(), sp.prepend((u, i))).into(),
   482|            Val::Obj(x, name, sp) => Val::Obj(x.clone(), name.clone(), sp.prepend((u, i))).into(),
   483|            Val::Call(name, args, body) => Val::Call(name.clone(), args.prepend((u.clone(), i)), self.v_app(decl, body, u, i)).into(),
   484|            x => panic!("impossible apply\n  {:?}\nto\n  {:?}", x, u),
   485|        }
   486|    }
   487|
   488|    fn v_app_sp(&self, decl: &Decl, t: Rc<Val>, spine: &Spine) -> Rc<Val> {
   489|        //spine.iter().rev().fold(t, |acc, (u, i)| self.v_app(acc, u.clone(), *i))
   490|        match spine {
   491|            List { head: None, .. } => t,
   492|            a => {
   493|                let (u, i) = a.head().unwrap();
   494|                self.v_app(decl, &self.v_app_sp(decl, t, &a.tail()), u.clone(), *i)
   495|            }
   496|        }
   497|    }
   498|
   499|    fn v_app_pruning(&self, decl: &Decl, env: &Env, v: Rc<Val>, pr: &Pruning) -> Rc<Val> {
   500|        //println!("{} {:?} {:?}", "v_app_bds".green(), v, bds);
   501|