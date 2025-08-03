

use super::{Infer, Cxt, Val, Tm, Closure, Spine, Lvl};

impl Infer {
    /// 在值上执行替换操作
    /// 
    /// 该函数使用Cxt中的subst字段（替换映射）来替换值中的变量。
    /// 替换映射是一个列表，每个元素表示将一个值替换为另一个值。
    /// 
    /// # 参数
    /// * `cxt` - 上下文，包含替换映射和其他相关信息
    /// * `v` - 要执行替换的值
    /// 
    /// # 返回
    /// 执行替换后的值
    pub fn subst(&self, cxt: &Cxt, v: Val) -> Val {
        match v {
            Val::Rigid(x, sp) => {
                // 检查变量x是否在替换映射中
                let mut replacement = None;
                for (from, to) in cxt.subst.iter() {
                    if let Val::Rigid(from_x, from_sp) = from {
                        // 只匹配没有应用的变量（空spine）
                        if *from_x == x && from_sp.is_empty() {
                            replacement = Some(to);
                            break;
                        }
                    }
                }
                
                match replacement {
                    Some(to) => {
                        // 递归地在替换值中执行替换（因为to可能包含其他需要替换的变量）
                        let to = self.subst(cxt, to.clone());
                        // 将替换值应用到原始spine
                        self.v_app_sp(to, sp)
                    }
                    None => {
                        // 递归地在spine上执行替换
                        let sp = self.subst_spine(cxt, sp);
                        Val::Rigid(x, sp)
                    }
                }
            }
            Val::Flex(m, sp) => {
                // 元变量：递归地在spine上执行替换
                let sp = self.subst_spine(cxt, sp);
                Val::Flex(m, sp)
            }
            Val::Obj(tm, name) => {
                // 对象：递归地在内部值上执行替换
                let tm = self.subst(cxt, *tm);
                Val::Obj(Box::new(tm), name)
            }
            Val::Lam(x, i, closure) => {
                // Lambda抽象：进入作用域，增加当前级别
                let new_cxt = Cxt {
                    lvl: cxt.lvl + 1,
                    ..cxt.clone()
                };
                
                // 在闭包体中应用替换
                let body = self.subst(&new_cxt, self.closure_apply(&closure, Val::vvar(cxt.lvl)));
                
                // 重新包装为lambda
                Val::Lam(x, i, Closure(cxt.env.clone(), Box::new(self.quote(cxt.lvl + 1, body))))
            }
            Val::Pi(x, i, a, b) => {
                // 递归地在类型部分执行替换
                let a = self.subst(cxt, *a);
                
                // Pi类型：进入作用域，增加当前级别
                let new_cxt = Cxt {
                    lvl: cxt.lvl + 1,
                    ..cxt.clone()
                };
                
                // 在类型体中应用替换
                let body = self.subst(&new_cxt, self.closure_apply(&b, Val::vvar(cxt.lvl)));
                
                Val::Pi(x, i, Box::new(a), Closure(cxt.env.clone(), Box::new(self.quote(cxt.lvl + 1, body))))
            }
            Val::U => Val::U,
            Val::LiteralType => Val::LiteralType,
            Val::LiteralIntro(x) => Val::LiteralIntro(x),
            Val::Prim => Val::Prim,
            Val::Sum(name, params, cases) => {
                // 递归地在参数类型上执行替换
                let params = params
                    .into_iter()
                    .map(|(name, val, vty, icit)| (name, self.subst(cxt, val), self.subst(cxt, vty), icit))
                    .collect();
                Val::Sum(name, params, cases)
            }
            Val::SumCase {
                sum_name,
                global_params,
                case_name,
                params,
                cases_name,
            } => {
                // 递归地在参数值上执行替换
                let global_params = global_params
                    .into_iter()
                    .map(|(name, val, vty, icit)| (name, self.subst(cxt, val), self.subst(cxt, vty), icit))
                    .collect();
                let params = params
                    .into_iter()
                    .map(|(name, val, icit)| (name, self.subst(cxt, val), icit))
                    .collect();
                Val::SumCase {
                    sum_name,
                    global_params,
                    case_name,
                    params,
                    cases_name,
                }
            }
            Val::Match(tm, env, cases) => {
                // 递归地在匹配目标上执行替换
                let tm = self.subst(cxt, *tm);
                
                // 递归地在每个匹配分支的项上执行替换
                let cases = cases
                    .into_iter()
                    .map(|(pat, body)| (pat, self.subst_tm(cxt, body)))
                    .collect();
                
                Val::Match(Box::new(tm), env, cases)
            }
        }
    }
    
    /// 在spine上执行替换操作
    /// 
    /// Spine表示应用序列，需要递归地在每个应用项上执行替换
    fn subst_spine(&self, cxt: &Cxt, spine: Spine) -> Spine {
        if let Some((val, icit)) = spine.head() {
            let val = self.subst(cxt, val.clone());
            let tail = self.subst_spine(cxt, spine.tail().clone());
            spine.prepend((val, *icit))
        } else {
            spine
        }
    }
    
    /// 在项上执行替换操作（辅助函数）
    /// 
    /// 由于Match结构中包含Tm，需要这个辅助函数
    fn subst_tm(&self, cxt: &Cxt, t: Tm) -> Tm {
        match t {
            Tm::Var(x) => {
                // 将De Bruijn索引转换为级别
                let lvl = if x.0 > 1919810 {
                    Lvl(x.0)
                } else {
                    Lvl(cxt.lvl.0 - x.0 - 1)
                };
                
                // 只替换自由变量（级别小于当前级别）
                if lvl < cxt.lvl {
                    let mut replacement = None;
                    for (from, to) in cxt.subst.iter() {
                        if let Val::Rigid(from_x, from_sp) = from {
                            if *from_x == lvl && from_sp.is_empty() {
                                replacement = Some(to);
                                break;
                            }
                        }
                    }
                    
                    match replacement {
                        Some(to) => self.quote(cxt.lvl, to.clone()),
                        None => Tm::Var(x)
                    }
                } else {
                    Tm::Var(x)
                }
            }
            // 其他Tm变体的替换实现
            Tm::Obj(tm, name) => {
                let tm = self.subst_tm(cxt, *tm);
                Tm::Obj(Box::new(tm), name)
            }
            Tm::Lam(x, i, t) => {
                let new_cxt = Cxt {
                    lvl: cxt.lvl + 1,
                    ..cxt.clone()
                };
                let t = self.subst_tm(&new_cxt, *t);
                Tm::Lam(x, i, Box::new(t))
            }
            Tm::App(t, u, i) => {
                let t = self.subst_tm(cxt, *t);
                let u = self.subst_tm(cxt, *u);
                Tm::App(Box::new(t), Box::new(u), i)
            }
            Tm::Pi(x, i, a, b) => {
                let a = self.subst_tm(cxt, *a);
                let new_cxt = Cxt {
                    lvl: cxt.lvl + 1,
                    ..cxt.clone()
                };
                let b = self.subst_tm(&new_cxt, *b);
                Tm::Pi(x, i, Box::new(a), Box::new(b))
            }
            Tm::Let(x, ty, t, u) => {
                let ty = self.subst_tm(cxt, *ty);
                let t = self.subst_tm(cxt, *t);
                let new_cxt = Cxt {
                    lvl: cxt.lvl + 1,
                    ..cxt.clone()
                };
                let u = self.subst_tm(&new_cxt, *u);
                Tm::Let(x, Box::new(ty), Box::new(t), Box::new(u))
            }
            Tm::U => Tm::U,
            Tm::Meta(m) => Tm::Meta(m),
            Tm::AppPruning(t, pr) => {
                let t = self.subst_tm(cxt, *t);
                Tm::AppPruning(Box::new(t), pr)
            }
            Tm::LiteralIntro(x) => Tm::LiteralIntro(x),
            Tm::LiteralType => Tm::LiteralType,
            Tm::Prim => Tm::Prim,
            Tm::Sum(name, params, cases) => {
                let params = params
                    .into_iter()
                    .map(|(name, ty, vty, icit)| (name, self.subst_tm(cxt, ty), self.subst_tm(cxt, vty), icit))
                    .collect();
                Tm::Sum(name, params, cases)
            }
            Tm::SumCase {
                sum_name,
                global_params,
                case_name,
                params,
                cases_name,
            } => {
                let global_params = global_params
                    .into_iter()
                    .map(|(name, ty, vty, icit)| (name, self.subst_tm(cxt, ty), self.subst_tm(cxt, vty), icit))
                    .collect();
                let params = params
                    .into_iter()
                    .map(|(name, tm, icit)| (name, self.subst_tm(cxt, tm), icit))
                    .collect();
                Tm::SumCase {
                    sum_name,
                    global_params,
                    case_name,
                    params,
                    cases_name,
                }
            }
            Tm::Match(tm, cases) => {
                let tm = self.subst_tm(cxt, *tm);
                let cases = cases
                    .into_iter()
                    .map(|(pat, body)| (pat, self.subst_tm(cxt, body)))
                    .collect();
                Tm::Match(Box::new(tm), cases)
            }
        }
    }
}
