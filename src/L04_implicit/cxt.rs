use super::*;


#[derive(Debug, Copy, Clone, PartialEq)]
pub enum NameOrigin {
    Inserted,
    Source,
}

type Types = List<(Span<String>, NameOrigin, Val)>;

#[derive(Debug)]
pub struct Cxt {
    pub env: Env,      // Used for evaluation
    pub lvl: Lvl,      // Used for unification
    pub types: Types,  // Used for raw name lookup and pretty printing
    pub bds: List<BD>, // Used for fresh meta creation
}

impl Cxt {
    pub fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            types: List::new(),
            bds: List::new(),
        }
    }

    pub fn bind(&self, x: Span<String>, a: Val) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            types: self.types.prepend((x, NameOrigin::Source, a)),
            bds: self.bds.prepend(BD::Bound),
        }
    }

    pub fn new_binder(&self, x: Span<String>, a: Val) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            types: self.types.prepend((x, NameOrigin::Inserted, a)),
            bds: self.bds.prepend(BD::Bound),
        }
    }

    pub fn define(&self, x: Span<String>, t: Val, a: Val) -> Self {
        Cxt {
            env: self.env.prepend(t),
            lvl: self.lvl + 1,
            types: self.types.prepend((x, NameOrigin::Source, a)),
            bds: self.bds.prepend(BD::Defined),
        }
    }
}
