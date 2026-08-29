use crate::{list::List, parser_lib::Span};
use smol_str::SmolStr;

use super::{
    Closure, Cxt, DeclTm, Error, Infer, Lvl, Tm, Val,
    cxt::DeclEntry,
    empty_span, lvl2ix,
    parser::syntax::{Decl, Either, Icit, Raw},
    pattern_match::Compiler,
};

impl Infer {
    fn insert_go(&mut self, cxt: &Cxt, t: Tm, va: Val) -> Result<(Tm, Val), Error> {
        match self.force(cxt.decl(), va) {
            Val::Pi(_, Icit::Impl, a, b) => {
                let m = self.fresh_meta(cxt.decl(), cxt, *a);
                let mv = self.eval(cxt.decl(), &cxt.env, m.clone());
                self.insert_go(
                    cxt,
                    Tm::App(Box::new(t), Box::new(m), Icit::Impl),
                    self.closure_apply(cxt.decl(), &b, mv),
                )
            }
            va => Ok((t, va)),
        }
    }

    fn insert_t(&mut self, cxt: &Cxt, act: Result<(Tm, Val), Error>) -> Result<(Tm, Val), Error> {
        act.and_then(|(t, va)| self.insert_go(cxt, t, va))
    }

    /// 隐式参数插入；如果项本身已经是隐式 λ 则不再插入（用户显式给出了隐式参数）。
    fn insert(&mut self, cxt: &Cxt, act: Result<(Tm, Val), Error>) -> Result<(Tm, Val), Error> {
        act.and_then(|x| match x {
            (t @ Tm::Lam(_, Icit::Impl, _), va) => Ok((t, va)),
            (t, va) => self.insert_t(cxt, Ok((t, va))),
        })
    }

    fn insert_until_go(
        &mut self,
        cxt: &Cxt,
        name: Span<String>,
        t: Tm,
        va: Val,
    ) -> Result<(Tm, Val), Error> {
        match self.force(cxt.decl(), va) {
            Val::Pi(x, Icit::Impl, a, b) => {
                if x.data == name.data {
                    Ok((t, Val::Pi(x, Icit::Impl, a, b)))
                } else {
                    let m = self.fresh_meta(cxt.decl(), cxt, *a);
                    let mv = self.eval(cxt.decl(), &cxt.env, m.clone());
                    self.insert_until_go(
                        cxt,
                        name,
                        Tm::App(Box::new(t), Box::new(m), Icit::Impl),
                        self.closure_apply(cxt.decl(), &b, mv),
                    )
                }
            }
            _ => Err(Error(format!("no named implicit arg {:?}", name))),
        }
    }

    fn insert_until_name(
        &mut self,
        cxt: &Cxt,
        name: Span<String>,
        act: Result<(Tm, Val), Error>,
    ) -> Result<(Tm, Val), Error> {
        act.and_then(|(t, va)| self.insert_until_go(cxt, name, t, va))
    }

    pub fn check(&mut self, cxt: &Cxt, t: Raw, a: Val) -> Result<Tm, Error> {
        let decl = cxt.decl();
        match (t, self.force(decl, a)) {
            // λ 检查：命名隐式 `[x = e]` 对准同名隐式 Π；显式对显式
            (Raw::Lam(x, i, t), Val::Pi(x_t, i_t, a, b_closure))
                if (i.clone(), i_t) == (Either::Name(x_t.clone()), Icit::Impl)
                    || i == Either::Icit(i_t) =>
            {
                let body = self.check(
                    &cxt.bind(x.clone(), self.quote(decl, cxt.lvl, *a.clone()), *a),
                    *t,
                    self.closure_apply(decl, &b_closure, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x, i_t, Box::new(body)))
            }
            // 非 λ 项 against 隐式 Π：插入一个隐式绑定器
            (t, Val::Pi(x, Icit::Impl, a, b_closure)) => {
                let body = self.check(
                    &cxt.new_binder(x.clone(), self.quote(decl, cxt.lvl, *a)),
                    t,
                    self.closure_apply(decl, &b_closure, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x, Icit::Impl, Box::new(body)))
            }
            // let
            (Raw::Let(x, a, t, u), a_prime) => {
                let a_checked = self.check(cxt, *a, Val::U)?;
                let va = self.eval(decl, &cxt.env, a_checked.clone());
                let t_checked = self.check(cxt, *t, va.clone())?;
                let vt = self.eval(decl, &cxt.env, t_checked.clone());
                let u_checked = self.check(
                    &cxt.define(x.clone(), t_checked.clone(), vt, a_checked.clone(), va),
                    *u,
                    a_prime,
                )?;
                Ok(Tm::Let(
                    x,
                    Box::new(a_checked),
                    Box::new(t_checked),
                    Box::new(u_checked),
                ))
            }
            // 洞
            (Raw::Hole, a) => Ok(self.fresh_meta(decl, cxt, a)),
            // match：编译 + 逐分支检查
            (Raw::Match(expr, clauses), expected) => {
                let (tm, typ) = self.infer_expr(cxt, *expr)?;
                let mut compiler = Compiler::new();
                compiler.compile(self, typ, tm.clone(), &clauses, cxt, expected)?;
                Ok(Tm::Match(Box::new(tm), compiler.pats))
            }
            // 一般情形：推断 + 合一
            (t, expected) => {
                let x = self.infer_expr(cxt, t);
                let (t_inferred, inferred_type) = self.insert(cxt, x)?;
                self.unify_catch(decl, cxt, expected, inferred_type)?;
                Ok(t_inferred)
            }
        }
    }

    pub fn infer(&mut self, cxt: &Cxt, t: Decl) -> Result<(DeclTm, Val, Cxt), Error> {
        let decl = cxt.decl();
        match t {
            Decl::Def {
                name,
                params,
                ret_type,
                body,
            } => {
                let typ = params.iter().rev().fold(ret_type.clone(), |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                });
                let bod = params.iter().rev().fold(body.clone(), |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let typ_tm = self.check(cxt, typ, Val::U)?;
                let vtyp = self.eval(decl, &cxt.env, typ_tm.clone());
                // 递归：先把名字登记成指向自身的中性占位，检查体，再用真实值覆盖。
                // 占位只存在于克隆出来的 decl 表里，不影响外层。
                let fake_cxt = cxt.decl_insert(
                    name.data.clone(),
                    DeclEntry {
                        ty: vtyp.clone(),
                        val: Val::Decl(SmolStr::new(&name.data), List::new()),
                    },
                );
                let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;
                let vt = self.eval(fake_cxt.decl(), &fake_cxt.env, t_tm.clone());
                let out_cxt = cxt.decl_insert(
                    name.data.clone(),
                    DeclEntry {
                        ty: vtyp,
                        val: vt,
                    },
                );
                Ok((DeclTm::Def, Val::U, out_cxt))
            }
            Decl::Println(t) => Ok((
                DeclTm::Println(self.infer_expr(cxt, t)?.0),
                Val::U,
                cxt.clone(),
            )),
            Decl::Enum {
                name,
                params,
                cases,
            } => {
                // enum 类型本体：λ params → Sum(name, [(p, Var p, type-of-p, icit)], cases)
                let new_params: Vec<_> = params
                    .iter()
                    .map(|x| (x.0.clone(), x.2, Raw::Var(x.0.clone())))
                    .collect();
                // 构造子缺省返回类型：Name 逐个应用到隐式参数（显式索引留给构造子的 -> 给出）
                let default_ret = params
                    .iter()
                    .filter(|x| x.2 == Icit::Impl)
                    .fold(Raw::Var(name.clone()), |ret, x| {
                        Raw::App(
                            Box::new(ret),
                            Box::new(Raw::Var(x.0.clone())),
                            Either::Icit(Icit::Impl),
                        )
                    });
                // 构造子类型：Pi(枚举隐式参数 ++ 构造子绑定器) -> (用户 -> ret || 缺省)
                let new_cases = cases
                    .iter()
                    .map(|(case_name, p, bind)| {
                        let ty = params
                            .iter()
                            .filter(|x| x.2 == Icit::Impl)
                            .cloned()
                            .chain(p.clone())
                            .rev()
                            .fold(bind.clone().unwrap_or(default_ret.clone()), |ret, x| {
                                Raw::Pi(x.0.clone(), x.2, Box::new(x.1.clone()), Box::new(ret))
                            });
                        (case_name.clone(), ty)
                    })
                    .collect::<Vec<_>>();
                let sum = Raw::Sum(
                    name.clone(),
                    new_params,
                    new_cases.iter().map(|x| x.0.clone()).collect(),
                );
                let typ = params
                    .iter()
                    .rev()
                    .fold(Raw::U, |a, b| {
                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                    });
                let bod = params.iter().rev().fold(sum, |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let typ_tm = self.check(cxt, typ, Val::U)?;
                let vtyp = self.eval(decl, &cxt.env, typ_tm.clone());
                // 先占位再检查本体（本体内部引用自身时报"指向自身的中性值"）
                let fake_cxt = cxt.decl_insert(
                    name.data.clone(),
                    DeclEntry {
                        ty: vtyp.clone(),
                        val: Val::Decl(SmolStr::new(&name.data), List::new()),
                    },
                );
                let t_tm = self.check(&fake_cxt, bod, vtyp.clone())?;
                let vt = self.eval(fake_cxt.decl(), &fake_cxt.env, t_tm.clone());
                let mut cxt = cxt.decl_insert(
                    name.data.clone(),
                    DeclEntry {
                        ty: vtyp,
                        val: vt,
                    },
                );
                // 逐构造子注册：体 = λ(隐式参数, 字段) → SumCase{typ: ret, datas: 字段自身}
                for ((case_name, binders, ret), (ctor_name, ctor_ty)) in
                    cases.into_iter().zip(new_cases.into_iter())
                {
                    let body_ret = Raw::SumCase {
                        typ: Box::new(ret.unwrap_or(default_ret.clone())),
                        case_name: case_name.clone(),
                        datas: binders
                            .iter()
                            .map(|(n, _, i)| (n.clone(), Raw::Var(n.clone()), *i))
                            .collect(),
                    };
                    let bod = params
                        .iter()
                        .filter(|x| x.2 == Icit::Impl)
                        .cloned()
                        .chain(binders)
                        .rev()
                        .fold(body_ret, |a, b| {
                            Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                        });
                    let typ_tm = self.check(&cxt, ctor_ty, Val::U)?;
                    let vtyp = self.eval(cxt.decl(), &cxt.env, typ_tm.clone());
                    let t_tm = self.check(&cxt, bod, vtyp.clone())?;
                    let vt = self.eval(cxt.decl(), &cxt.env, t_tm.clone());
                    let entry = DeclEntry {
                        ty: vtyp,
                        val: vt,
                    };
                    // 限定名 `Enum.case` + 裸名别名（后注册者覆盖同名裸名）
                    cxt = cxt.decl_insert(
                        SmolStr::new(format!("{}.{}", name.data, ctor_name.data)),
                        entry.clone(),
                    );
                    cxt = cxt.decl_insert(ctor_name.data.clone(), entry);
                }
                Ok((DeclTm::Enum, Val::U, cxt))
            }
        }
    }

    pub fn infer_expr(&mut self, cxt: &Cxt, t: Raw) -> Result<(Tm, Val), Error> {
        let decl = cxt.decl();
        match t {
            // 变量：先局部（src_names），再全局（decl 表）
            Raw::Var(x) => {
                if let Some((lvl, ty)) = cxt.src_names.get(&x.data) {
                    Ok((Tm::Var(lvl2ix(cxt.lvl, *lvl)), ty.clone()))
                } else if let Some(e) = cxt.decl_get(&x.data) {
                    Ok((Tm::Decl(SmolStr::new(&x.data)), e.ty.clone()))
                } else {
                    Err(Error(format!("name not in scope: {}", x.data)))
                }
            }

            Raw::Obj(x, f) => {
                // 限定构造子引用 `Enum.case`
                if let Raw::Var(n) = &*x {
                    let key = format!("{}.{}", n.data, f.data);
                    if let Some(e) = cxt.decl_get(&key) {
                        return Ok((Tm::Decl(SmolStr::new(key)), e.ty.clone()));
                    }
                }
                let (tm, ty) = self.infer_expr(cxt, *x)?;
                match self.force(decl, ty) {
                    // 接收者类型是 Sum：字段=索引参数，类型取参数的**类型槽**
                    Val::Sum(sname, params, _) => params
                        .iter()
                        .find(|(n, ..)| n == &f)
                        .map(|(_, _, fty, _)| (Tm::Obj(Box::new(tm), f.clone()), fty.clone()))
                        .ok_or_else(|| {
                            Error(format!("{} has no field {}", sname.data, f.data))
                        }),
                    // 接收者类型是构造子值：索引参数优先，否则剥构造子类型取字段真实类型
                    Val::SumCase {
                        typ,
                        case_name,
                        datas,
                    } => {
                        let (sname, params) = match self.force(decl, *typ) {
                            Val::Sum(sname, params, _) => (sname, params),
                            _ => return Err(Error(" ill-scoped SumCase".to_owned())),
                        };
                        if let Some((_, _, fty, _)) =
                            params.iter().find(|(n, ..)| n == &f)
                        {
                            return Ok((Tm::Obj(Box::new(tm), f.clone()), fty.clone()));
                        }
                        let ctor_ty = cxt
                            .decl_get(&format!("{}.{}", sname.data, case_name.data))
                            .ok_or_else(|| Error("missing constructor decl".to_owned()))?
                            .ty
                            .clone();
                        let impl_vals: Vec<Val> = params
                            .iter()
                            .filter(|(_, _, _, i)| *i == Icit::Impl)
                            .map(|(_, v, _, _)| v.clone())
                            .collect();
                        let mut ty = ctor_ty;
                        let mut impl_idx = 0;
                        loop {
                            match self.force(decl, ty) {
                                Val::Pi(bname, _, bdom, closure) => {
                                    if bname.data == f.data {
                                        return Ok((
                                            Tm::Obj(Box::new(tm), f.clone()),
                                            *bdom,
                                        ));
                                    }
                                    let u = if impl_idx < impl_vals.len() {
                                        let v = impl_vals[impl_idx].clone();
                                        impl_idx += 1;
                                        v
                                    } else {
                                        datas
                                            .iter()
                                            .find(|(n, _, _)| n == &bname)
                                            .map(|(_, v, _)| v.clone())
                                            .ok_or_else(|| {
                                                Error(format!(
                                                    "no field {} on {}",
                                                    f.data, sname.data
                                                ))
                                            })?
                                    };
                                    ty = self.closure_apply(decl, &closure, u);
                                }
                                _ => {
                                    return Err(Error(format!(
                                        "{} has no field {}",
                                        sname.data, f.data
                                    )))
                                }
                            }
                        }
                    }
                    _ => Err(Error(format!("cannot project field {}", f.data))),
                }
            }

            // λ 推断：域用 fresh meta，值域闭包封口
            Raw::Lam(x, Either::Icit(i), t) => {
                let new_meta = self.fresh_meta(decl, cxt, Val::U);
                let a = self.eval(decl, &cxt.env, new_meta);
                let new_cxt = cxt.bind(x.clone(), self.quote(decl, cxt.lvl, a.clone()), a.clone());
                let infered = self.infer_expr(&new_cxt, *t);
                let (t_inferred, b) = self.insert(&new_cxt, infered)?;
                let b_closure = self.close_val(decl, cxt, b);
                Ok((
                    Tm::Lam(x.clone(), i, Box::new(t_inferred)),
                    Val::Pi(x, i, Box::new(a), b_closure),
                ))
            }

            Raw::Lam(x, Either::Name(_), t) => Err(Error(format!("infer named lambda {x:?}"))),

            // 应用
            Raw::App(t, u, i) => {
                let (i, t, tty) = match i {
                    Either::Name(name) => {
                        let infered = self.infer_expr(cxt, *t);
                        let (t, tty) = self.insert_until_name(cxt, name, infered)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer_expr(cxt, *t)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Expl) => {
                        let infered = self.infer_expr(cxt, *t);
                        let (t, tty) = self.insert_t(cxt, infered)?;
                        (Icit::Expl, t, tty)
                    }
                };
                let (a, b_closure) = match self.force(decl, tty) {
                    Val::Pi(_, i_t, a, b_closure) => {
                        if i == i_t {
                            (*a, b_closure)
                        } else {
                            return Err(Error(format!("icit mismatch {i:?} {i_t:?}")));
                        }
                    }
                    tty => {
                        let new_meta = self.fresh_meta(decl, cxt, Val::U);
                        let a = self.eval(decl, &cxt.env, new_meta);
                        let b_closure = Closure(
                            cxt.env.clone(),
                            Box::new(self.fresh_meta(
                                decl,
                                &cxt.bind(
                                    empty_span("x".to_string()),
                                    self.quote(decl, cxt.lvl, a.clone()),
                                    a.clone(),
                                ),
                                Val::U,
                            )),
                        );
                        self.unify_catch(
                            decl,
                            cxt,
                            Val::Pi(
                                empty_span("x".to_string()),
                                i,
                                Box::new(a.clone()),
                                b_closure.clone(),
                            ),
                            tty,
                        )?;
                        (a, b_closure)
                    }
                };
                let u_checked = self.check(cxt, *u, a)?;
                Ok((
                    Tm::App(Box::new(t), Box::new(u_checked.clone()), i),
                    self.closure_apply(decl, &b_closure, self.eval(decl, &cxt.env, u_checked)),
                ))
            }

            Raw::U => Ok((Tm::U, Val::U)),

            Raw::Pi(x, i, a, b) => {
                let a_checked = self.check(cxt, *a, Val::U)?;
                let a_eval = self.eval(decl, &cxt.env, a_checked.clone());
                let b_checked = self.check(
                    &cxt.bind(x.clone(), self.quote(decl, cxt.lvl, a_eval.clone()), a_eval),
                    *b,
                    Val::U,
                )?;
                Ok((
                    Tm::Pi(x, i, Box::new(a_checked), Box::new(b_checked)),
                    Val::U,
                ))
            }

            Raw::Let(x, a, t, u) => {
                let a_checked = self.check(cxt, *a, Val::U)?;
                let va = self.eval(decl, &cxt.env, a_checked.clone());
                let t_checked = self.check(cxt, *t, va.clone())?;
                let vt = self.eval(decl, &cxt.env, t_checked.clone());
                let (u_inferred, b) = self.infer_expr(
                    &cxt.define(
                        x.clone(),
                        t_checked.clone(),
                        vt.clone(),
                        a_checked.clone(),
                        va,
                    ),
                    *u,
                )?;
                Ok((
                    Tm::Let(
                        x,
                        Box::new(a_checked),
                        Box::new(t_checked),
                        Box::new(u_inferred),
                    ),
                    b,
                ))
            }

            Raw::Hole => {
                let new_meta = self.fresh_meta(decl, cxt, Val::U);
                let a = self.eval(decl, &cxt.env, new_meta);
                let t = self.fresh_meta(decl, cxt, a.clone());
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => Ok((Tm::LiteralIntro(literal), Val::LiteralType)),

            // match 只能在检查模式下使用（期望类型决定分支体怎么查）
            Raw::Match(..) => Err(Error(
                "match cannot be inferred; give it an expected type".to_owned(),
            )),

            Raw::Sum(name, params, cases) => {
                let new_params = params
                    .iter()
                    .map(|(n, i, raw)| {
                        let (value_checked, value_ty) = self.infer_expr(cxt, raw.clone())?;
                        let ty = self.quote(decl, cxt.lvl, value_ty);
                        Ok((n.clone(), value_checked, ty, *i))
                    })
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok((Tm::Sum(name, new_params, cases), Val::U))
            }

            Raw::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let (typ_checked, _) = self.infer_expr(cxt, *typ)?;
                let typ_val = self.eval(decl, &cxt.env, typ_checked.clone());
                let datas = datas
                    .into_iter()
                    .map(|(n, raw, i)| {
                        let (tm, _) = self.infer_expr(cxt, raw)?;
                        Ok((n, tm, i))
                    })
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok((
                    Tm::SumCase {
                        typ: Box::new(typ_checked),
                        case_name,
                        datas,
                    },
                    typ_val,
                ))
            }
        }
    }

    /// 模式编译专用的精化合一：与 `unify` 的区别在于 rigid 侧不解 meta，
    /// 而是把"当前上下文里还未精化的 rigid 变量"的 env 槽改写为对侧的值
    /// （`Cxt::update_cxt`）。调用顺序约定：**先传被匹配类型（头部），再传
    /// 构造子返回类型**——这样精化方向总是"头部变量 := 模式引入的新变量"。
    pub fn unify_pm(&mut self, cxt: &Cxt, t: Val, u: Val) -> Result<Cxt, Error> {
        let decl = cxt.decl();
        // 与 unify 相同：递归深度防护（fuel 由外层调用充值，这里递减）。
        // SumCase 的 typ 索引槽互相嵌入时，Sum/SumCase 的递归会无限进行，
        // 必须在这里耗尽即返回错误。
        let f = self.unify_fuel.get();
        if f == 0 {
            return Err(Error("unify_pm: fuel exhausted".to_owned()));
        }
        self.unify_fuel.set(f - 1);
        match (self.force(decl, t), self.force(decl, u)) {
            (Val::Rigid(x1, sp1), Val::Rigid(x2, sp2))
                if sp1.is_empty() && sp2.is_empty() && x1 == x2 =>
            {
                Ok(cxt.clone())
            }
            (Val::Rigid(x, sp), v) if sp.is_empty() => self.refine_pm(cxt, x, v),
            (v, Val::Rigid(x, sp)) if sp.is_empty() => self.refine_pm(cxt, x, v),
            (Val::Sum(n1, p1, _), Val::Sum(n2, p2, _)) if n1.data == n2.data => {
                let mut cxt = cxt.clone();
                for (a, b) in p1.iter().zip(p2.iter()) {
                    cxt = self.unify_pm(&cxt, a.1.clone(), b.1.clone())?;
                }
                Ok(cxt)
            }
            (
                Val::SumCase {
                    typ: t1,
                    case_name: c1,
                    datas: d1,
                },
                Val::SumCase {
                    typ: t2,
                    case_name: c2,
                    datas: d2,
                },
            ) if c1.data == c2.data => {
                let mut cxt = cxt.clone();
                // **先比 datas 再比 typ**：datas 里的 meta 在此合一中被 solve，
                // 随后 typ 的比较（索引槽引用同样的 meta）才能快速终止；
                // 反之 typ 优先会在"索引槽 ↔ 构造子值"的互相引用上深递归。
                for (a, b) in d1.iter().zip(d2.iter()) {
                    cxt = self.unify_pm(&cxt, a.1.clone(), b.1.clone())?;
                }
                // typ 只查**名字**：两个构造子值在模式编译里必然来自同一个
                // 头部类型（其参数已在调用侧的 Sum-Sum 比较中逐槽精化过），
                // 递归比较 typ 的索引槽只会陷入"索引槽 ↔ 构造子值"的环
                // （双方的 typ 各自嵌着对方的构造子形态）。
                let n1 = sum_name_of(t1.as_ref());
                let n2 = sum_name_of(t2.as_ref());
                if n1 != n2 {
                    return Err(Error("SumCase 类型不一致".to_owned()));
                }
                Ok(cxt)
            }
            (t, u) => {
                self.unify_catch(decl, cxt, t, u)?;
                Ok(cxt.clone())
            }
        }
    }

    /// 把 rigid `x` 精化为 `v`。只精化当前上下文里还未精化的变量
    /// （env 槽仍是自身的 vvar）；已精化过则要求两次精化一致；
    /// 不属于本上下文的 rigid（探测替身等）回落普通合一。
    fn refine_pm(&mut self, cxt: &Cxt, x: Lvl, v: Val) -> Result<Cxt, Error> {
        if x.0 >= cxt.lvl.0 {
            let decl = cxt.decl();
            self.unify_catch(decl, cxt, Val::Rigid(x, List::new()), v)?;
            return Ok(cxt.clone());
        }
        let pos = (cxt.lvl.0 - x.0 - 1) as usize;
        let cur = cxt.env.iter().nth(pos).unwrap().clone();
        let unrefined = matches!(&cur, Val::Rigid(y, sp) if *y == x && sp.is_empty());
        if unrefined {
            Ok(cxt.update_cxt(self, x, v))
        } else {
            self.unify_pm(cxt, cur, v)
        }
    }
}

/// `Val::Sum` 的名字（用于 SumCase typ 的浅层比较）
fn sum_name_of(v: &Val) -> Option<String> {
    match v {
        Val::Sum(name, _, _) => Some(name.data.clone()),
        _ => None,
    }
}
