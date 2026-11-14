//! smalltt 基准用例 → typort 源码生成器（按层族分模块，互不重叠的写域）。
//!
//! 约定：每个用例返回的源码**最后一个 def 就是该用例要计时/quote 的对象**
//! （smalltt 的 [elabtime]/[nftime] 行）。为此，非 nf 用例会追加一个
//! `nf_dummy` 之类的极小尾 def，使 ref_nf 口径只做一次平凡 quote，
//! 从而 ref/ref_nf 两个口径都把时间花在 check（= 该用例的 elab 工作量）上。

pub mod l07_l08;
pub mod l09_l10;
pub mod stlc;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Family {
    L07,
    L08,
    L09,
    L10,
}

pub struct Spec {
    pub name: &'static str,
    pub sizes: &'static [&'static str],
    /// true = 该用例的 benchmark 是 nf 口径（ref_nf 才是主指标）
    pub nf: bool,
}

/// 该层支持的用例表（L07/L08 = 07/08 族 + stlc 族；L09/L10 = 09/10 族）。
pub fn specs_for(f: Family) -> Vec<&'static Spec> {
    match f {
        Family::L07 | Family::L08 => l07_l08::SPECS.iter().chain(stlc::SPECS.iter()).collect(),
        Family::L09 | Family::L10 => l09_l10::SPECS.iter().collect(),
    }
}

/// 生成某层某用例某 size 的 typort 源码；Err = 该层不支持（打印原因）。
pub fn source(f: Family, case: &str, size: &str) -> Result<String, String> {
    match f {
        Family::L07 | Family::L08 => {
            if let Ok(s) = l07_l08::source(case, size) {
                return Ok(s);
            }
            stlc::source(case, size)
        }
        Family::L09 | Family::L10 => l09_l10::source(case, size),
    }
}

pub fn case_wanted(cli_case: &str, name: &str) -> bool {
    let c = cli_case.trim();
    c == "all" || c.split(',').any(|x| x.trim() == name)
}

pub fn sizes_for<'a>(cli_sizes: &Option<String>, spec: &'a Spec) -> Vec<&'a str> {
    match cli_sizes {
        None => spec.sizes.to_vec(),
        Some(s) => spec
            .sizes
            .iter()
            .copied()
            .filter(|sz| s.split(',').any(|x| x.trim() == *sz))
            .collect(),
    }
}
