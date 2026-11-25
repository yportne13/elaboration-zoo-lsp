//! `check_pm_final` 的第二次合一是必需的——红绿对照。
//!
//! ## 背景
//!
//! `check_pm_final` 做两次合一：
//!   1. 内部 `check_pm` ——求解，结果经 `subst_cxt` 烘焙进臂上下文；
//!   2. `ori ≐ tmv`（构造子返回类型 ≐ 臂体推断类型），末尾是 `.unwrap_or(cxt)`。
//!
//! 第 2 次**永不报错**，唯一效果是再做一次急切精化（`update_cxt`）。因此很容易
//! 被误判为冗余——B3' 的第 21 轮就是这么假设的，实测被否决：
//!
//! | 判据 | 保留 | 丢弃第 2 次 |
//! |---|---|---|
//! | L12/L13 判定差异 | 23 / 170 | **31 / 170** |
//! | 新增差异 | — | 11 个（L07/L08/L09 的证明类语料，Ok → Err） |
//! | 消除差异 | — | 3 个（L11 的 scn_* ） |
//!
//! 净差 +8，且失败集中在**证明类**语料——它们依赖臂上下文里被精化过的类型
//! 才能通过体检查。
//!
//! ## 本测试的作用
//!
//! 锁定那几个证明类语料必须通过。若有人（包括未来的我）再次试图删掉
//! `check_pm_final` 的第 2 次合一，这里会立刻变红。

use std::path::{Path, PathBuf};

fn corpus(layer: &str, name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tools/bench_corpus")
        .join(layer)
        .join(name)
}

/// 深链/证明类语料需要大栈，与其它 L13 语料测试同款对策。
fn elaborates(path: &Path) -> bool {
    let Ok(src) = std::fs::read_to_string(path) else {
        panic!("语料缺失：{}", path.display());
    };
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || elaboration_zoo_lsp::L13_namespace::run(&src, 0).is_ok())
        .expect("spawn big-stack thread")
        .join()
        .expect("worker panicked")
}

/// 丢弃 `check_pm_final` 的第 2 次合一时，这 11 个语料会从 Ok 翻成 Err。
/// 本用例锁定它们必须 Ok。
#[test]
fn proof_corpus_needs_the_final_unification() {
    let cases = [
        ("L07", "ex_proof_add_assoc.typort"),
        ("L07", "ex_proof_add_comm.typort"),
        ("L07", "ex_proof_add_succ_right.typort"),
        ("L07", "ex_proof_add_zero_right.typort"),
        ("L07", "ex_proof_mul_one_right.typort"),
        ("L07", "ex_proof_mul_zero_right.typort"),
        ("L07", "hw_proof_suite.typort"),
        ("L08", "ex_proof_add_assoc.typort"),
        ("L08", "ex_proof_add_zero_right.typort"),
        ("L09", "extract_07.typort"),
        ("L09", "proj_container_lib.typort"),
    ];
    let mut bad = Vec::new();
    for (layer, name) in cases {
        let p = corpus(layer, name);
        if !elaborates(&p) {
            bad.push(format!("{} {}", layer, name));
        }
    }
    assert!(
        bad.is_empty(),
        "这些证明类语料必须能通过 —— 它们依赖 check_pm_final 第 2 次合一的精化，\
         若此处变红，多半是有人删掉了那次合一（见模块文档）。\n{:#?}",
        bad
    );
}
