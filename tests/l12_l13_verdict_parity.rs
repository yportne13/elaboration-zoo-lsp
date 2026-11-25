//! L12 vs L13 判定对照（B3' 的独立判据）。
//!
//! 背景：`tools/l13_oracle_check.ps1` 冻结的是「L13 现在的行为」——如果 σ 正确但确实
//! 改变了行为，那个 oracle 永远会红，无法区分「σ 错了」与「σ 对了但行为该变」。
//! 本套件用 **L12 的实现（σ 路线，已全绿）** 作基准：同一份语料喂给 L12 与 L13，
//! 比对**判定**（Ok / Err）而不是输出文本（L07↔L13 的渲染本就故意不同）。
//!
//! 语料：tools/bench_corpus/{common,L07..L12} 共 170 个 .typort。

use std::path::Path;

fn corpus_files() -> Vec<(String, String)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut out = Vec::new();
    for layer in ["common", "L07", "L08", "L09", "L10", "L11", "L12"] {
        let dir = root.join("tools/bench_corpus").join(layer);
        let Ok(rd) = std::fs::read_dir(&dir) else { continue };
        for e in rd.flatten() {
            let p = e.path();
            if p.extension().and_then(|s| s.to_str()) != Some("typort") {
                continue;
            }
            out.push((layer.to_owned(), p.display().to_string()));
        }
    }
    out
}

/// 深链语料在默认 2 MB 栈上会爆栈，与 L13 内部测试同款对策：64 MB 栈线程。
/// 泛型 `E` 让 L12 / L13 各自不同的 `Error` 类型都能传进来（只看 Ok/Err）。
fn run_verdict<F, E>(f: F) -> bool
where
    F: FnOnce() -> Result<String, E> + Send + 'static,
    // E is built and consumed inside the worker thread (only the bool crosses
    // the boundary), so it does NOT need to be Send -- L13's Error holds Rc.
    E: 'static,
{
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || f().is_ok())
        .expect("spawn big-stack thread")
        .join()
        .unwrap_or(false)
}

/// 同一份语料在 L12 与 L13 上的判定（Ok = 通过，Err = 报错）。
#[test]
fn l12_and_l13_agree_on_corpus_verdicts() {
    let files = corpus_files();
    assert!(files.len() >= 150, "语料缺失：只找到 {} 个", files.len());

    let mut agree = 0usize;
    let mut diffs = Vec::new();

    for (layer, path) in &files {
        let Ok(src) = std::fs::read_to_string(path) else { continue };
        let name = Path::new(path)
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("?")
            .to_owned();

        let src_l12 = src.clone();
        let l12 = run_verdict(move || elaboration_zoo_lsp::L12_canonical::run(&src_l12, 0));
        let src_l13 = src.clone();
        let l13 = run_verdict(move || elaboration_zoo_lsp::L13_namespace::run(&src_l13, 0));

        if l12 == l13 {
            agree += 1;
        } else {
            diffs.push(format!("{} {}: L12={} L13={}", layer, name, l12, l13));
        }
    }

    eprintln!(
        "corpus verdict agreement: {}/{} ({} differences)",
        agree,
        files.len(),
        diffs.len()
    );
    for d in diffs.iter().take(40) {
        eprintln!("  {}", d);
    }
    // 已知差异（L07↔L13 known-diff）允许存在，但必须有界；先记录再收紧。
    assert!(
        diffs.len() * 100 <= files.len() * 15,
        "L12/L13 判定差异过多（{} / {}），超出 15% 容差\n{:#?}",
        diffs.len(),
        files.len(),
        diffs
    );
}
