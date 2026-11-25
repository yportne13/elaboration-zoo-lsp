//! 链继承门禁（P7）：把"第 N 章 = 第 N-1 章完整继承 + 本章新特性"钉成可复跑的断言。
//!
//! 数据来源：docs/inheritance/ 下的账本 TSV（tools/inherit_audit.py 生成）。
//! 判定：
//! 1. 每个转换的 line_keep 不低于阈值；
//! 2. 账本里每一条非 identical 条目，都必须在同名 allow 白名单里有一行登记
//!    （文件 / 条目 / 结论 / 理由）。没登记 = 继承面私自退化 = 红灯。
//!
//! 维护规则：
//! - 代码改动让某条目从 identical 变成 changed/missing ⇒ 要么改回去，要么在
//!   allow 文件里补一行并写清"为什么这是本章允许的差异"。
//! - 阈值只许升不许降（改阈值等于改验收口径，必须在评审里说明）。

use std::collections::HashMap;

/// (上一章, 本章, 账本文件, keep 下限, allow 文件)
const CHAPTERS: &[(&str, &str, &str, f64, &str)] = &[
    ("L07_sum_type", "L08_product_type", "L07_sum_type-to-L08_product_type.tsv", 0.94, "allow-L08.tsv"),
    ("L08_product_type", "L09_mltt", "L08_product_type-to-L09_mltt.tsv", 0.98, "allow-L09.tsv"),
    ("L09_mltt", "L10_typeclass", "L09_mltt-to-L10_typeclass.tsv", 0.99, "allow-L10.tsv"),
    ("L10_typeclass", "L11_macro", "L10_typeclass-to-L11_macro.tsv", 0.99, "allow-L11.tsv"),
    ("L11_macro", "L12_canonical", "L11_macro-to-L12_canonical.tsv", 0.99, "allow-L12.tsv"),
    ("L12_canonical", "L13_namespace", "L12_canonical-to-L13_namespace.tsv", 0.51, "allow-L13.tsv"),
];

fn ledger_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("docs/inheritance")
}

/// 账本行：(file, kind, item, prev_lines, deleted, status, keep)
struct Row {
    file: String,
    item: String,
    status: String,
}

fn parse_ledger(text: &str) -> Vec<Row> {
    let mut rows = Vec::new();
    for line in text.lines().skip(1) {
        let c: Vec<&str> = line.split('\t').collect();
        if c.len() < 7 {
            continue;
        }
        rows.push(Row {
            file: c[0].to_owned(),
            item: c[2].to_owned(),
            status: c[5].to_owned(),
        });
    }
    rows
}

/// allow 白名单行：(file, item) -> 理由
fn parse_allow(text: &str) -> HashMap<(String, String), String> {
    let mut map = HashMap::new();
    for line in text.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let c: Vec<&str> = line.split('\t').collect();
        if c.len() < 4 {
            continue;
        }
        // 文件 / 条目 / 结论 / 理由
        let key = (c[0].trim().to_owned(), c[1].trim().to_owned());
        map.insert(key, format!("[{}] {}", c[2].trim(), c[3].trim()));
    }
    map
}

fn audit_one(prev: &str, next: &str, ledger: &str, min_keep: f64, allow_file: &str) {
    let dir = ledger_dir();
    let path = dir.join(ledger);
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("读不到账本 {}: {}", path.display(), e));
    assert!(
        text.starts_with("file\tkind\titem\tprev_lines\tdeleted\tstatus\tkeep"),
        "{} 表头不对（重跑 tools/inherit_audit.py）",
        ledger
    );

    let rows = parse_ledger(&text);
    assert!(!rows.is_empty(), "{} 是空账本", ledger);

    // 1) keep 阈值：用账本里的 keep 列直接算总 keep（item_lines 加权）
    let mut item_lines = 0u64;
    let mut deleted = 0u64;
    for line in text.lines().skip(1) {
        let c: Vec<&str> = line.split('\t').collect();
        if c.len() < 7 {
            continue;
        }
        item_lines += c[3].parse::<u64>().unwrap_or(0);
        deleted += c[4].parse::<u64>().unwrap_or(0);
    }
    let keep = 1.0 - (deleted as f64) / (item_lines.max(1) as f64);
    assert!(
        keep >= min_keep,
        "{}: line_keep {:.4} 低于下限 {:.2}（{} -> {}），继承面退化了",
        ledger,
        keep,
        min_keep,
        prev,
        next
    );

    // 2) 每一条非 identical 都要有登记
    let allow_path = dir.join(allow_file);
    let allow_text = std::fs::read_to_string(&allow_path)
        .unwrap_or_else(|e| panic!("读不到白名单 {}: {}", allow_path.display(), e));
    let allow = parse_allow(&allow_text);

    let mut unregistered = Vec::new();
    for row in rows.iter().filter(|r| r.status != "identical") {
        if !allow.contains_key(&(row.file.clone(), row.item.clone())) {
            unregistered.push(format!("{}:{} [{}]", row.file, row.item, row.status));
        }
    }
    assert!(
        unregistered.is_empty(),
        "{}: {} 条非 identical 未登记（补 {} 或在 allow 里写清理由）：\n  {}",
        ledger,
        unregistered.len(),
        allow_file,
        unregistered.join("\n  ")
    );
}

#[test]
fn chain_inheritance_ledgers_hold() {
    for (prev, next, ledger, min_keep, allow) in CHAPTERS {
        audit_one(prev, next, ledger, *min_keep, allow);
    }
}

/// 白名单本身要有意义：每行必须带理由、且必须真对应账本里的一行
/// （防止 allow 文件留着一堆已消失的过期条目）。
#[test]
fn allow_lists_are_live_and_justified() {
    for (prev, next, ledger, _keep, allow_file) in CHAPTERS {
        let dir = ledger_dir();
        let text = std::fs::read_to_string(dir.join(ledger)).unwrap();
        let rows = parse_ledger(&text);
        let allow_text = std::fs::read_to_string(dir.join(allow_file)).unwrap();
        let allow = parse_allow(&allow_text);
        assert!(!allow.is_empty(), "{} 是空白名单", allow_file);

        for ((file, item), reason) in allow.iter() {
            let live = rows.iter().any(|r| &r.file == file && &r.item == item && r.status != "identical");
            assert!(
                live,
                "{} 的登记 {}/{} 在账本里已不存在或已 identical（过期条目，请删掉）",
                allow_file, file, item
            );
            assert!(
                reason.len() > 8,
                "{} 的登记 {}/{} 理由太短（写清为什么这是本章允许的差异）",
                allow_file, file, item
            );
        }
        let _ = (prev, next);
    }
}
