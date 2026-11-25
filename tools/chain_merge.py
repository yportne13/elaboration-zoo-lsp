import io, os, subprocess, shutil, sys

def extract(commit, chapter, dst_root):
    """把某个提交里的章节树解出来到 tmp/chain_base/src/<chapter>"""
    shutil.rmtree(dst_root, ignore_errors=True)
    os.makedirs(dst_root, exist_ok=True)
    tar = os.path.join(dst_root, "_x.tar")
    with open(tar, "wb") as f:
        subprocess.run(["git", "--git-dir", "F:/projects/hermes/elaboration-zoo-lsp/.git",
                        "archive", commit, "src/" + chapter], stdout=f, check=True)
    subprocess.run(["tar", "-xf", "_x.tar"], cwd=dst_root, check=True)
    os.remove(tar)

def rels(base):
    out = []
    for root, _, fs in os.walk(base):
        for fn in fs:
            out.append(os.path.relpath(os.path.join(root, fn), base).replace("\\", "/"))
    return sorted(out)

def merge(commit, prev, nxt):
    base_dir = "tmp/chain_base/src/" + prev
    extract(commit, prev, "tmp/chain_base")
    ours_dir = "src/" + prev
    theirs_dir = "src/" + nxt
    base, ours, theirs = rels(base_dir), rels(ours_dir), rels(theirs_dir)
    print("base:", len(base), "ours:", len(ours), "theirs:", len(theirs))
    print("ours-only (新文件，需平移到下一章):", [f for f in ours if f not in base])
    print("theirs-only (本章新文件):", [f for f in theirs if f not in base])

    clean, conflicts = [], {}
    for f in base:
        if f not in theirs or f not in ours:
            print("  skip (缺一侧):", f)
            continue
        tmp = os.path.join("tmp/chain_merge/" + prev + "/", f)
        os.makedirs(os.path.dirname(tmp), exist_ok=True)
        shutil.copyfile(os.path.join(ours_dir, f), tmp)
        r = subprocess.run(["git", "merge-file", "-p", tmp,
                            os.path.join(base_dir, f), os.path.join(theirs_dir, f)],
                           capture_output=True, text=True, encoding="utf-8", errors="replace")
        txt = r.stdout
        out_path = os.path.join("tmp/chain_merge/" + prev + "/", f + ".conflicted")
        io.open(out_path, "w", encoding="utf-8", newline="\n").write(txt)
        if "<<" + "<<<<" in txt:
            conflicts[f] = txt.count("<<" + "<<<<")
        else:
            io.open(os.path.join(theirs_dir, f), "w", encoding="utf-8", newline="\n").write(txt)
            clean.append(f)
    print("clean merges:", len(clean))
    print("conflicted:", conflicts)

commit = sys.argv[1]
merge(commit, sys.argv[2], sys.argv[3])
