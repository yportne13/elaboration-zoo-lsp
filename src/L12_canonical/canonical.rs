
use super::{
    Infer, MetaEntry, Cxt, Rc, Val, UnifyError, Ty, Span,
    MetaVar, Tm, Lvl, Ix, List, Closure, VTy, syntax::Locals,
    empty_span, Raw, Either,
};

impl Infer {
    pub fn search(
        &mut self,
        cxt: &Cxt,
        target: Vec<(MetaVar, Rc<Val>)>,
        unify_list: Vec<(Rc<Val>, Rc<Val>)>,
        depth: u32,
        mut collect: Vec<String>,
        avoid_recurse: &str,//TODO: this is incorrect
    ) -> Result<String, UnifyError> {
        //println!("Searching...");
        let infer_bak = self.clone();
        let mut typ = self.force(&cxt.decl, &target[0].1);
        let mut cxt = cxt.clone();
        while let Val::Pi(span, icit, dom, clos) = typ.as_ref() {
            let lvl = cxt.lvl;
            cxt = cxt.bind(span.clone(), self.quote(&cxt.decl, cxt.lvl, dom), dom.clone());
            typ = self.closure_apply(&cxt.decl, clos, Val::vvar(lvl).into());
        }
        /*let names = cxt.names();
        let iterator = names.iter()
            .map(|t| {
                let (l, (_, v)) = &cxt.src_names.get(t).unwrap();
                let vtm = cxt.env.iter().nth((cxt.lvl - l.0 - 1).0 as usize).unwrap().clone();
                (t, v, vtm)
            })
            .chain(
                cxt.decl.iter()
                    .map(|t| (t.0, &t.1.4, t.1.2.clone()))
            );
        for (t, v, vtm) in iterator {
            self.meta[target[0].0.0 as usize] = MetaEntry::Solved(vtm, target[0].1.clone());
            if self.unify_catch(&cxt, v, &typ, empty_span(())).is_ok()
                && unify_list.iter().all(|(a, b)| self.unify_catch(&cxt, a, b, empty_span(())).is_ok()) {
                    if !target.get(1..).map(|x| x.to_vec()).unwrap_or(vec![]).is_empty() {
                        collect.push(t.to_string());
                        return self.search(&cxt, target[1..].to_vec(), unify_list, depth, collect, avoid_recurse);
                    } else {
                        return Ok(format!("({}{})", collect.into_iter().map(|x| x + ", ").reduce(|a, b| a + &b).unwrap_or(String::new()), t));
                    }
            }
        }*/

        if depth == 0 {
            *self = infer_bak;
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
                .filter(|(t, _, _)| !["create_global", "change_mutable", avoid_recurse].contains(&t.as_str()));
            for (t, v, mut vtm) in iterator {
                let mut vt = v.clone();
                let mut new_list = vec![];
                //println!("{t}\n{:?}\n{:?}\n{:?}\n------------", vt, vtm, typ);
                while let Val::Pi(span, icit, dom, clos) = vt.as_ref() {
                    let icit = *icit;
                    let meta_var = self.meta.len();
                    let new_meta = self.fresh_meta(&cxt, dom.clone());
                    new_list.push((MetaVar(meta_var as u32), dom.clone()));
                    vt = self.closure_apply(&cxt.decl, clos, self.eval(&cxt.decl, &cxt.env, &new_meta));
                    vtm = self.v_app(&cxt.decl, &vtm, self.eval(&cxt.decl, &cxt.env, &new_meta), icit);
                    //println!("{t}\n{:?}\n{:?}\n{:?}\n------------", vt, vtm, typ);
                }
                self.meta[target[0].0.0 as usize] = MetaEntry::Solved(vtm, target[0].1.clone());
                if self.unify_catch(&cxt, &vt, &typ, empty_span(())).is_ok()
                    && unify_list.iter().all(|(a, b)| self.unify_catch(&cxt, a, b, empty_span(())).is_ok()) {
                        //println!("#### {:?}\n{:?}\n== {:?}", vt, new_list, typ);
                        let mut unify_list_d = unify_list.clone();
                        unify_list_d.push((vt, typ.clone()));
                        if new_list.is_empty() {
                            if !target.get(1..).map(|x| x.to_vec()).unwrap_or(vec![]).is_empty() {
                                collect.push(t.to_string());
                                return self.search(&cxt, target[1..].to_vec(), unify_list, depth, collect, avoid_recurse);
                            } else {
                                return Ok(format!("({}{})", collect.into_iter().map(|x| x + ", ").reduce(|a, b| a + &b).unwrap_or(String::new()), t));
                            }
                        } else if let Ok(ret) = self.search(&cxt, new_list, unify_list_d, depth - 1, vec![], avoid_recurse) {
                            if !target.get(1..).map(|x| x.to_vec()).unwrap_or(vec![]).is_empty() {
                                collect.push(format!("{t}{ret}"));
                                return self.search(&cxt, target[1..].to_vec(), unify_list, depth, collect, avoid_recurse);
                            } else {
                                return Ok(format!("({}{}{})", collect.into_iter().map(|x| x + ", ").reduce(|a, b| a + &b).unwrap_or(String::new()), t, ret));
                            }
                        }
                }
            }
        }


        // 所有候选都失败
        *self = infer_bak;
        //println!("search failed");
        Err(UnifyError::Basic)
    }
}
