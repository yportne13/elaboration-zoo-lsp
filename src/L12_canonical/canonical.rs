
use super::{
    Infer, MetaEntry, Cxt, Rc, Val, UnifyError, Ty, Span,
    MetaVar, Tm, Lvl, Ix, List, Closure, VTy, syntax::Locals,
    empty_span, Raw, Either, Spine, close_ty, Icit,
};

impl Infer {
    pub fn search(
        &mut self,
        cxt: &Cxt,
        target: &[Rc<Val>],
        origin_cxt: &Cxt,
        origin_target: &Rc<Val>,
        raw: Rc<dyn Fn(List<Raw>) -> Raw>,
        depth: u32,
        avoid_recurse: &str,//TODO: this is incorrect
    ) -> Result<String, UnifyError> {
        let mut typ = self.force(&cxt.decl, &target[0]);
        let mut cxt = cxt.clone();
        let mut lamb = List::new();
        while let Val::Pi(span, icit, dom, clos) = typ.as_ref() {
            let lvl = cxt.lvl;
            if *icit == Icit::Expl {
                lamb = lamb.prepend(span.data.clone());
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
            for (t, v, mut vtm) in iterator {
                let mut vt = v.clone();
                let mut new_list = vec![];
                //println!("{t}\n{:?}\n{:?}\n{:?}\n------------", vt, vtm, typ);
                //println!("1. {t} target: {}, depth: {depth}, {:?}", target.len(), target[0].0);
                while let Val::Pi(span, icit, dom, clos) = vt.as_ref() {
                    let icit = *icit;
                    let new_meta = self.fresh_meta(&cxt, dom.clone());
                    let meta = self.eval(&cxt.decl, &cxt.env, &new_meta);
                    if icit == Icit::Expl {
                        new_list.push(dom.clone());
                    }
                    vt = self.closure_apply(&cxt.decl, clos, meta.clone());
                    vtm = self.v_app(&cxt.decl, &vtm, meta, icit);
                    //println!("{t}\n{:?}\n{:?}\n{:?}\n------------", vt, vtm, typ);
                }
                let this_raw = (0..new_list.len()).fold(Raw::Var(empty_span(t.clone())), |acc, _| {
                    Raw::App(acc.into(), Raw::Hole(empty_span(())).into(), Either::Icit(Icit::Expl))
                });
                let this_raw = lamb.iter()
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
                                if let Ok(ret) = self.search(&cxt, &target[1..], origin_cxt, origin_target, Rc::new(move |t| raw.clone()(t.prepend(this_raw.clone()))), depth, avoid_recurse) {
                                    return Ok(ret)
                                }
                            } else {
                                return Ok(format!("{}", raw(List::new().prepend(this_raw))))
                            }
                        } else if let Ok(ret) = self.search(&cxt, &[new_list, target[1..].to_vec()].concat(), origin_cxt, origin_target, Rc::new(move |z| raw.clone()({
                            let (a, b) = z.split_at(new_list_len);
                            b.prepend({
                                let ret = a.iter().fold(Raw::Var(empty_span(t.clone())), |acc, x| Raw::App(acc.into(), x.clone().into(), Either::Icit(Icit::Expl)));
                                lamb.clone().iter()
                                    .fold(ret, |acc, x| {
                                        Raw::Lam(empty_span(x.clone()), Either::Icit(Icit::Expl), acc.into())
                                    })
                            })
                        })), depth - 1, avoid_recurse) {
                            return Ok(ret)
                        }
                }
            }
        }
        //println!("search failed");
        Err(UnifyError::Basic)
    }
}
