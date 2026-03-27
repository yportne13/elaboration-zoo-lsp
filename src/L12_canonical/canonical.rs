
use super::{
    Infer, MetaEntry, Cxt, Rc, Val, UnifyError, Ty, Span,
    MetaVar, Tm, Lvl, Ix, List, Closure, VTy, syntax::Locals,
    empty_span, Raw, Either, Spine, close_ty, Icit,
};

impl Infer {
    pub fn search(
        &mut self,
        cxt: &Cxt,
        target: Vec<(MetaVar, Rc<Val>, Spine)>,
        unify_list: Vec<(Rc<Val>, Rc<Val>)>,
        depth: u32,
        mut collect: Vec<String>,
        avoid_recurse: &str,//TODO: this is incorrect
        meta_offset: usize,
    ) -> Result<String, UnifyError> {
        //println!("Searching...");
        let meta_bak: Vec<_> = self.meta.iter().skip(meta_offset).cloned().collect();
        let meta_len_bak = self.meta.len();
        let mut typ = self.force(&cxt.decl, &target[0].1);
        let mut cxt = cxt.clone();
        let mut sp: Vec<_> = target[0].2.iter().collect();
        let mut spine = target[0].2.clone();
        let mut lamb = vec![];
        while let Val::Pi(span, icit, dom, clos) = typ.as_ref() {
            //let lvl = cxt.lvl;
            //cxt = cxt.bind(span.clone(), self.quote(&cxt.decl, cxt.lvl, dom), dom.clone());
            //typ = self.closure_apply(&cxt.decl, clos, Val::vvar(lvl).into());
            if let Some(x) = sp.last() {
                typ = self.closure_apply(&cxt.decl, clos, x.0.clone());
                sp.pop();
            } else {
                let lvl = cxt.lvl;
                lamb.push(span.data.clone());
                cxt = cxt.bind(span.clone(), self.quote(&cxt.decl, cxt.lvl, dom), dom.clone());
                spine = spine.prepend((Val::vvar(lvl).into(), *icit));
                typ = self.closure_apply(&cxt.decl, clos, Val::vvar(lvl).into());
            }
        }

        if depth == 0 {
            if self.meta.len() > meta_len_bak {
                self.meta.truncate(meta_len_bak);
            }
            for (i, entry) in meta_bak.clone().into_iter().enumerate() {
                self.meta[meta_offset + i] = entry;
            }
            //println!("search failed 0");
            return Err(UnifyError::Basic);
        } else {
            let names = cxt.names();
            let iterator = names.iter()
                .map(|t| {
                    let (l, (_, v)) = &cxt.src_names.get(t).unwrap();
                    let vtm = cxt.env.iter().nth((cxt.lvl - l.0 - 1).0 as usize).unwrap().clone();
                    (t, v, vtm)
                })
                .chain(
                    cxt.decl.iter()
                        .map(|t| (t.0, &t.1.4, t.1.2.clone()))
                )
                .filter(|(t, _, _)| ![
                    "create_global",
                    "change_mutable",
                    "string_to_global_type",
                    "string_concat",
                    "get_global",
                    avoid_recurse].contains(&t.as_str()));
            for (t, v, mut vtm) in iterator {
                let mut vt = v.clone();
                let mut new_list = vec![];
                //println!("{t}\n{:?}\n{:?}\n{:?}\n------------", vt, vtm, typ);
                while let Val::Pi(span, icit, dom, clos) = vt.as_ref() {
                    let icit = *icit;
                    let meta_var = self.meta.len();
                    let new_meta = self.fresh_meta(&cxt, dom.clone());
                    let meta = self.eval(&cxt.decl, &cxt.env, &new_meta);
                    let (meta_var, spine) = match meta.as_ref() {
                        Val::Flex(m, sp) => (*m, sp.clone()),
                        _ => (MetaVar(meta_var as u32), List::new()),
                    };
                    let closed = self.eval(
                        &cxt.decl,
                        &List::new(),
                        &close_ty(&cxt.locals, self.quote(&cxt.decl, cxt.lvl, dom)),
                    );
                    if icit == Icit::Expl {
                        new_list.push((meta_var, closed, spine));
                    }
                    vt = self.closure_apply(&cxt.decl, clos, meta.clone());
                    vtm = self.v_app(&cxt.decl, &vtm, meta, icit);
                    //println!("{t}\n{:?}\n{:?}\n{:?}\n------------", vt, vtm, typ);
                }
                //self.meta[target[0].0.0 as usize] = MetaEntry::Solved(vtm, target[0].1.clone());
                //println!("spine: {:?}", target[0].2);
                self.meta[target[0].0.0 as usize] = MetaEntry::Unsolved(target[0].1.clone(), cxt.clone());
                self.solve(cxt.lvl, &cxt.decl, target[0].0, spine.clone(), &vtm);
                if self.unify_catch(&cxt, &vt, &typ, empty_span(())).is_ok()
                    && unify_list.iter().all(|(a, b)| self.unify_catch(&cxt, a, b, empty_span(())).is_ok()) {
                        //println!("#### {:?}\n{:?}\n== {:?}", vt, new_list, typ);
                        let mut unify_list_d = unify_list.clone();
                        unify_list_d.push((vt, typ.clone()));
                        let lamb_string = lamb.iter()
                            .map(|x| format!("{x} => "))
                            .reduce(|a, b| a + &b)
                            .unwrap_or(String::new());
                        if new_list.is_empty() {
                            if !target.get(1..).map(|x| x.to_vec()).unwrap_or(vec![]).is_empty() {
                                collect.push(format!("{lamb_string}{t}"));
                                return self.search(&cxt, target[1..].to_vec(), unify_list, depth, collect, avoid_recurse, meta_offset);
                            } else {
                                return Ok(format!("({lamb_string}{}{})", collect.into_iter().map(|x| x + ", ").reduce(|a, b| a + &b).unwrap_or(String::new()), t));
                            }
                        } else if let Ok(ret) = self.search(&cxt, new_list, unify_list_d, depth - 1, vec![], avoid_recurse, meta_offset) {
                            if !target.get(1..).map(|x| x.to_vec()).unwrap_or(vec![]).is_empty() {
                                collect.push(format!("{lamb_string}{t}{ret}"));
                                return self.search(&cxt, target[1..].to_vec(), unify_list, depth, collect, avoid_recurse, meta_offset);
                            } else {
                                return Ok(format!("({lamb_string}{}{}{})", collect.into_iter().map(|x| x + ", ").reduce(|a, b| a + &b).unwrap_or(String::new()), t, ret));
                            }
                        }
                }
            }
        }


        // 所有候选都失败
        if self.meta.len() > meta_len_bak {
            self.meta.truncate(meta_len_bak);
        }
        for (i, entry) in meta_bak.clone().into_iter().enumerate() {
            self.meta[meta_offset + i] = entry;
        }
        //println!("search failed");
        Err(UnifyError::Basic)
    }
}
