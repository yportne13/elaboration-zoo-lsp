import io, os, re

LEDGERS = [
    ("L07_sum_type", "L08_product_type", "L07_sum_type-to-L08_product_type.tsv", "allow-L08.tsv"),
    ("L08_product_type", "L09_mltt", "L08_product_type-to-L09_mltt.tsv", "allow-L09.tsv"),
    ("L09_mltt", "L10_typeclass", "L09_mltt-to-L10_typeclass.tsv", "allow-L10.tsv"),
    ("L10_typeclass", "L11_macro", "L10_typeclass-to-L11_macro.tsv", "allow-L11.tsv"),
    ("L11_macro", "L12_canonical", "L11_macro-to-L12_canonical.tsv", "allow-L12.tsv"),
    ("L12_canonical", "L13_namespace", "L12_canonical-to-L13_namespace.tsv", "allow-L13.tsv"),
]

FEATURES = {
    "L08": "本章新特性：struct/new 语法糖、左结合投影链、struct 模式糖、Point.mk 渲染、(Obj,Obj) 合同臂",
    "L09": "本章新特性：Type N 分层宇宙（Tm/Val::U(u32)、check_universe、enum universe_lvl）",
    "L10": "本章新特性：trait/typeclass（Synth 求解、trait 三表、trait_wrap、trait 文法）",
    "L11": "本章新特性：macro_rules（token/元变量/重复、解析期展开、深度护栏）",
    "L12": "本章新特性：Val 级 trait 求解（替换 Typ 桥接）、Tm/Val::Call 内联节点",
    "L13": "生产层架构分叉：Span<SmolStr>/4 元 Sum/Val::Nat/update_cxt 载体/FUNC_PROF（见 L13-triage.md）",
}

def classify(prev, next_, f, item):
    """返回 (结论, 理由)。"""
    ch = next_.split("_")[0]  # L08 / L09 ...
    if f.startswith("bump_spine_iter"):
        return ("FROZEN", "孪生引擎已封印（feature 默认关、parity 编空、lib 零引用），只登记不回填")
    # 章名重命名：L07_DEBUG_ON -> L08_DEBUG_ON 等
    m = re.search(r"^(L\d\d)_(DEBUG_ON|LOOP)", item)
    if m:
        return ("RENAME", "章名重命名 %s_* → %s_*（调试开关随层改名）" % (m.group(1), ch))
    if item in ("span_from_name", "unify", "unify_sp", "unify_iter", "rename_iter", "pretty", "raw_span"):
        return ("PATH", "crate 路径/模块前缀改名（L0N_sum_type → %s），逻辑不变" % next_)
    return ("FEATURE", FEATURES.get(ch, "本章增量"))

out_dir = "docs/inheritance"
for prev, next_, ledger, allow in LEDGERS:
    rows = io.open(os.path.join(out_dir, ledger), encoding="utf-8").read().strip().split("\n")[1:]
    lines = ["# 继承门禁白名单（%s ← %s）" % (next_, prev),
             "# 每行：文件<TAB>条目<TAB>结论<TAB>理由",
             "# 结论取值：FEATURE(本章新特性) / RENAME(章名重命名) / PATH(路径改名) /",
             "#           FROZEN(孪生封印) / REPLACED(本章主动替换) / MOTION(合并移位)",
             "# 由 tools/gen_allow.py 从账本生成；条目消失或变 identical 时本行必须删除。"]
    twin_n = feat_n = ren_n = path_n = 0
    for line in rows:
        c = line.split("\t")
        if len(c) < 7 or c[5] == "identical":
            continue
        verdict, reason = classify(prev, next_, c[0], c[2])
        if verdict == "FROZEN": twin_n += 1
        elif verdict == "FEATURE": feat_n += 1
        elif verdict == "RENAME": ren_n += 1
        elif verdict == "PATH": path_n += 1
        lines.append("%s\t%s\t%s\t%s" % (c[0], c[2], verdict, reason))
    io.open(os.path.join(out_dir, allow), "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")
    print("%-14s %3d frozen / %3d feature / %2d rename / %2d path" % (allow, twin_n, feat_n, ren_n, path_n))
