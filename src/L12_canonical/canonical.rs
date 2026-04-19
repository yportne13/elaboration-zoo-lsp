
use super::{
    Infer, MetaEntry, Cxt, Rc, Val, UnifyError, Ty, Span,
    MetaVar, Tm, Lvl, Ix, List, Closure, VTy, syntax::Locals,
    empty_span, Raw, Either, Spine, close_ty, Icit,
};

impl Infer {
    pub fn search(
        &mut self,
        cxt: &Cxt,
        target: &[(MetaVar, Rc<Val>)],
        origin_cxt: &Cxt,
        origin_target: &Rc<Val>,
        raw: Rc<dyn Fn(List<Raw>) -> Raw>,
        depth: u32,
        collect: Vec<String>,
        avoid_recurse: &str,//TODO: this is incorrect
    ) -> Result<String, UnifyError> {
        let mut typ = self.force(&cxt.decl, &target[0].1);
        let mut cxt = cxt.clone();
        let mut lamb = vec![];
        while let Val::Pi(span, icit, dom, clos) = typ.as_ref() {
            let lvl = cxt.lvl;
            if *icit == Icit::Expl {
                lamb.push(span.data.clone());
            }
            cxt = cxt.bind(span.clone(), self.quote(&cxt.decl, cxt.lvl, dom), dom.clone());
            typ = self.closure_apply(&cxt.decl, clos, Val::vvar(lvl).into());
        }

        if depth == 0 {
            //println!("search failed 0");
            return Err(UnifyError::Basic);
        } else {
            let names = cxt.names();
            let iterator = names.iter()
                .map(|t| {
                    let (l, (_, v)) = &cxt.src_names.get(t).unwrap();
                    let vtm = cxt.env.iter().nth((cxt.lvl - l.0 - 1).0 as usize).unwrap().clone();
                    (t.clone(), v, vtm)
                })
                .chain(
                    cxt.decl.iter()
                        .map(|t| (t.0.clone(), &t.1.4, t.1.2.clone()))
                )
                .filter(|(t, _, _)| ![
                    "create_global",
                    "change_mutable",
                    "change_mutable_default",
                    "string_to_global_type",
                    "string_concat",
                    "get_global",
                    "outParam",
                    avoid_recurse].contains(&t.as_str()));
            let lamb_string = lamb.iter()
                .map(|x| format!("{x} => "))
                .reduce(|a, b| a + &b)
                .unwrap_or(String::new());
            /*if matches!(self.meta[target[0].0.0 as usize], MetaEntry::Solved(_, _)) {
                if !target.get(1..).map(|x| x.is_empty()).unwrap_or(true) {
                    let mut collect_next = collect.clone();
                    collect_next.push(format!("{lamb_string}_"));
                    if let Ok(ret) = self.search(&cxt, &target[1..], origin_target, unify_list.clone(), depth, collect_next, avoid_recurse, meta_offset) {
                        return Ok(ret)
                    }
                } else {
                    return Ok(format!("({lamb_string}{}_)", collect.into_iter().map(|x| x + ", ").reduce(|a, b| a + &b).unwrap_or(String::new())));
                }
            }*/
            for (t, v, mut vtm) in iterator {
                let mut vt = v.clone();
                let mut new_list = vec![];
                //println!("{t}\n{:?}\n{:?}\n{:?}\n------------", vt, vtm, typ);
                //println!("1. {t} target: {}, depth: {depth}, {:?}", target.len(), target[0].0);
                while let Val::Pi(span, icit, dom, clos) = vt.as_ref() {
                    let icit = *icit;
                    let meta_var = self.meta.len();
                    let new_meta = self.fresh_meta(&cxt, dom.clone());
                    let meta = self.eval(&cxt.decl, &cxt.env, &new_meta);
                    let (meta_var, spine) = match meta.as_ref() {
                        Val::Flex(m, sp) => (*m, sp.clone()),
                        _ => (MetaVar(meta_var as u32), List::new()),
                    };
                    if icit == Icit::Expl {
                        new_list.push((meta_var, dom.clone()));
                    }
                    vt = self.closure_apply(&cxt.decl, clos, meta.clone());
                    vtm = self.v_app(&cxt.decl, &vtm, meta, icit);
                    //println!("{t}\n{:?}\n{:?}\n{:?}\n------------", vt, vtm, typ);
                }
                let this_raw = (0..new_list.len()).fold(Raw::Var(empty_span(t.clone())), |acc, _| {
                    Raw::App(acc.into(), Raw::Hole(empty_span(())).into(), Either::Icit(Icit::Expl))
                });
                let this_raw = lamb.iter()
                    .rev()
                    .fold(this_raw, |acc, x| {
                        Raw::Lam(empty_span(x.clone()), Either::Icit(Icit::Expl), acc.into())
                    });
                let raw_list = (0..(target.len() - 1)).fold(List::new(), |acc, _| {
                    acc.prepend(Raw::Hole(empty_span(())))
                }).prepend(this_raw.clone());
                let lamb = lamb.clone();
                if matches!(self.unify(cxt.lvl, &cxt, &vt, &typ, 100), Ok(_) | Err(UnifyError::Stuck))
                    && self.check::<true>(origin_cxt, raw.clone()(raw_list), origin_target).is_ok() {
                        /*println!(
                            "#### {:?}\n{}\n== {:?}",
                            super::pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, &vt)),
                            new_list.iter()
                                .map(|x| format!("{:?} {:?} {:?}", x.0, super::pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, &x.1)), x.2))
                                .collect::<Vec<_>>()
                                .join("\n"),
                            super::pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, &typ)),
                        );*/
                        let raw = raw.clone();
                        let new_list_len = new_list.len();
                        if new_list.is_empty() {
                            if !target.get(1..).map(|x| x.is_empty()).unwrap_or(true) {
                                let mut collect_next = collect.clone();
                                collect_next.push(format!("{lamb_string}{t}"));
                                if let Ok(ret) = self.search(&cxt, &target[1..], origin_cxt, origin_target, Rc::new(move |t| raw.clone()(t.prepend(this_raw.clone()))), depth, collect_next, avoid_recurse) {
                                    return Ok(ret)
                                }
                            } else {
                                //return Ok(format!("({lamb_string}{}{})", collect.into_iter().map(|x| x + ", ").reduce(|a, b| a + &b).unwrap_or(String::new()), t));
                                return Ok(format!("{}", raw(List::new().prepend(this_raw))))
                            }
                        } else if let Ok(ret) = self.search(&cxt, &[new_list, target[1..].to_vec()].concat(), origin_cxt, origin_target, Rc::new(move |z| raw.clone()({
                            let (a, b) = z.split_at(new_list_len);
                            b.prepend({
                                let ret = a.iter().fold(Raw::Var(empty_span(t.clone())), |acc, x| Raw::App(acc.into(), x.clone().into(), Either::Icit(Icit::Expl)));
                                lamb.clone().iter()
                                    .rev()
                                    .fold(ret, |acc, x| {
                                        Raw::Lam(empty_span(x.clone()), Either::Icit(Icit::Expl), acc.into())
                                    })
                            })
                        })), depth - 1, vec![], avoid_recurse) {
                            /*if !target.get(1..).map(|x| x.is_empty()).unwrap_or(true) {
                                let mut collect_next = collect.clone();
                                collect_next.push(format!("{lamb_string}{t}{ret}"));
                                if let Ok(ret) =  self.search(&cxt, &target[1..], origin_target, unify_list.clone(), depth, collect_next, avoid_recurse, meta_offset) {
                                    return Ok(ret)
                                }
                            } else {
                                return Ok(format!("({lamb_string}{}{}{})", collect.into_iter().map(|x| x + ", ").reduce(|a, b| a + &b).unwrap_or(String::new()), t, ret));
                            }*/
                            return Ok(ret)
                        }
                }
            }
        }
        //println!("search failed");
        Err(UnifyError::Basic)
    }
}
