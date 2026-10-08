# tools/ -- Windows-hosted verification helpers

This directory holds the day-to-day verification entry points. Everything here
was grown out of round-1 scratch scripts that lived in `target/prelude_scratch/`
(gitignored) and kept being re-invented; they are checked in now so round 3 does
not have to rebuild them.

**All of these tools are read-only with respect to the repository.** They read
sources and existing binaries, and they write only into their own log directory
(`target/gate_l13_logs/`, `target/probe_logs/`, or wherever `-OutDir`/`-LogDir`
points). None of them edits sources or the git index.

| tool | what it does |
|---|---|
| `gate_l13.ps1` | Windows-native four-suite pre-commit gate (mirror of `gate_l13.sh`) |
| `BoundedProcess.ps1` | shared process runner: reliable exit codes, timeout, memory ceiling, UTF-8 streams |
| `probe/run_probe.ps1` | bounded `l13bench --file` probe wrapper with a calibrated judge |
| `probe/run_check.ps1` | bounded `typort check` probe wrapper (full prelude incl. `show`) |
| `probe/calib/*.typort` | the must-fail / must-pass calibration samples |
| `prelude_doc_cov.py` | per-file / per-area doc coverage from `typort doc` JSON |

---

## 1. Quick start (PowerShell 5.1 on Windows)

```powershell
# pre-commit gate
powershell -ExecutionPolicy Bypass -File tools/gate_l13.ps1 -Label myname

# one probe (cheap loop; core prelude, no show)
powershell -ExecutionPolicy Bypass -File tools/probe/run_probe.ps1 -File target/x.typort

# a probe that prints .show (needs the full prelude)
powershell -ExecutionPolicy Bypass -File tools/probe/run_check.ps1 -File target/x.typort

# prove the probe judge still discriminates, without running a real probe
powershell -ExecutionPolicy Bypass -File tools/probe/run_probe.ps1 -Calibrate
powershell -ExecutionPolicy Bypass -File tools/probe/run_check.ps1 -Calibrate

# doc coverage
& .\target\debug\typort.exe doc target/prelude_scratch/doc_measure.typort `
    --out target/doc_json --format json --min-coverage 0
python tools/prelude_doc_cov.py target/doc_json --fail-under 60
```

### Why the checked-in `.sh` gate is not usable on this host

`tools/gate_l13.sh` is the canonical gate for Linux/CI and stays canonical. But
this development host is Windows + PowerShell 5.1, and **WSL bash on this machine
has no `cargo` on its PATH**, so the `.sh` gate cannot actually run here. That is
the entire reason `gate_l13.ps1` exists: same four suites, same skip recipe, same
`fail=N` summary and exit code. Keep the two in sync when you change either.

---

## 2. `gate_l13.ps1`

Four suites, mirroring `gate_l13.sh`:

| suite | command |
|---|---|
| `lib` | `cargo test --lib L13_namespace::` |
| `parity` | `cargo test --test l13_fast_parity -- --skip L13_namespace::` |
| `twin` | `cargo test --test twin_engine_tests` |
| `hdl042` | `cargo test --test hdl042_engine_tests` |

The `--skip` is a *libtest* flag for the parity suite: `tests/l13_fast_parity.rs`
re-compiles all of `src/L13_namespace/mod.rs` through `#[path]`, so the L13 tests
would otherwise run a second time. They already ran in the `lib` suite, so the
skip removes duplication without losing an assertion. Use `-Full` to drop it
(needed when you touched parity/normalisation itself, and for a release gate).

Parameters:

```
-Label <name>            prefix for the suite logs (default "gate")
-Suites <a,b,c,d>        run only these suites, e.g. -Suites hdl042 (quick smoke)
-SkipTwin                skip twin_engine_tests (~80s); do NOT use when touching LSP wiring
-Full                    parity runs without the L13 skip
-CargoTargetDir <dir>    exported as CARGO_TARGET_DIR; logs land under it too
-CargoArgs <a,b>         extra cargo-level flags, e.g. -CargoArgs --release,--quiet
-OutDir <dir>            where the logs go (default <target>/gate_l13_logs)
-TimeoutSec <n>          per-suite hard timeout (default 3600)
-RetryWaitSec <n>        wait before one automatic retry after an exe-lock failure
-KillStaleSec <n>        kill probe processes older than n seconds before each suite
                         (default 0 = never kill anything)
-MinLib/-MinParity/      per-suite minimum passing counts (defaults 500/15/27/2);
-MinTwin/-MinHdl042      below them the suite fails as BELOW-MIN
-MinFreeGB <n>           warn when the target drive has less free space (default 2)
-HardMinFreeGB <n>       exit 2 below this much free space (default 0.5)
-Quiet                   only print the per-suite result lines
```

Exit code: `0` when every suite passed, `1` when any suite failed. A non-zero
cargo exit is a failure, but a *timed-out* suite is reported as `TIMEOUT` rather
than being confused with a compile error.

The gate prints each suite's raw `test result:` line(s) on success, which is what
to paste into a report:

```
    [lib ok: 121.4s] test result: ok. 606 passed; 0 failed; 6 ignored; 0 measured; 0 filtered out
```

### Two rules the gate enforces on top of cargo's exit code

* **A suite only passes if it actually ran tests.** cargo exits 0 when a filter
  matches nothing, so a mistyped filter (lowercase `l13` matches no test path) or
  a wrong `--skip` would otherwise be certified as a pass. Every suite must
  produce a `test result:` line with `passed > 0`; a zero-test run is reported as
  `NO-TESTS` and fails the gate. Verified against the real trap:
  `cargo test --lib l13` exits 0 with `0 passed; 0 failed; 973 filtered out`.
* **The failure list is truncated; the counts are authoritative.** On failure the
  gate prints the parsed `N passed / M failed` on the verdict line itself,
  repeats the raw `test result:` lines, and then labels the truncated message
  list (`failure list: first 40 of 106 matching lines`). Never quantify a failure
  from that list -- one run of this gate was misread as "12 failed" when the real
  number was 68.

---

## 3. Probe wrappers (`probe/run_probe.ps1`, `probe/run_check.ps1`)

### Why a wrapper is mandatory, not a convenience

`l13bench` has **no termination guard on the engine**. A probe that makes
elaboration diverge runs forever and grows without bound; round 1 measured a
13.8 GB process. Worse, on Windows a running `l13bench.exe`/`typort.exe` holds
the top-level binary open, so every teammate's `cargo build` fails while it runs
(see section 5). The wrappers therefore enforce:

* a **wall-clock timeout** (`-TimeoutSec`) and a **memory ceiling** (`-MemGB`),
  both enforced from outside the process, and the child is always killed;
* `-max-infer-ms` for `typort check` (a budget, not a guarantee: round 1 saw
  processes outlive it by minutes);
* logs merged from **both** streams and read back with `-Encoding UTF8`.

### Why the judge must be calibrated before it is believed

Round 1 shipped a probe judge that scanned only **stderr** for the failure
marker. But `l13bench` prints its `[diag]` lines -- including the failure marker
-- to **stdout**. That judge therefore returned `PASS` for *every* probe,
including deliberately broken ones, and two rounds of "evidence" were silently
bogus before anyone noticed.

Both wrappers now refuse to report a verdict unless, in the same run, a
known-bad sample still classifies as failing and a known-good sample still
classifies as passing. Cost: about 1.5s for `run_probe`, and one extra
`typort check` run for `run_check` (tens of seconds under load -- budget for it).
`-Calibrate` runs the calibration alone; `-NoCalibrate` skips it (batch loops
only, and say so when you report the result).

Two distinct calibration failures are reported:

* `judge-mismatch` -- the sample produced classifiable output of the WRONG class:
  the judge is broken. Stop and fix it.
* `no-evidence` -- the sample produced nothing classifiable at all, e.g. because a
  teammate's `build.ps1` killed the child mid-run. The wrapper retries the sample
  up to 3 times before giving up; a busy machine is not a judge bug.

### Verdicts

`run_probe.ps1` (l13bench):

| verdict | meaning |
|---|---|
| `PASS` | both engines elaborated every decl (`twin` and `basic` both report all-decls-passed) |
| `DECL-FAIL` | an engine reported a first-failing decl -- real probe failure |
| `PRELUDE-PARSE-FAIL` | `prelude PARSE-FAILED`: the builtin prelude itself is broken |
| `USER-PARSE-FAIL` | `parse failed`: the probe file does not parse |
| `TIMEOUT` / `MEM-LIMIT` | killed by the external guard |
| `EXTERNAL-KILL` | the child died non-zero with no diagnostics: something outside the wrapper terminated it |
| `NO-OUTPUT` | no `[diag]` line and a clean exit: nothing to judge |
| `INCONCLUSIVE` | output present but unclassifiable -- **read the raw tail, do not record it as a pass** |
| `JUDGE-BROKEN` | calibration failed; all other verdicts are worthless |

`run_check.ps1` (typort check) -- `typort check` **always exits 0**, so the exit
code carries no information:

| verdict | meaning |
|---|---|
| `PASS` | no `error:` line, and every `println` produced a `note:` value |
| `ERRORS(n)` | n `error:` lines |
| `NO-OUTPUT(...)` | a probe with `println` produced zero value notes: truncated, NOT a pass |
| `EXTERNAL-KILL` / `TIMEOUT` / `MEM-LIMIT` | as above |
| `JUDGE-BROKEN` | calibration failed |

Exit codes for both: `0` PASS, `3` any non-PASS verdict, `2` usage/environment
error, `4` judge not verified.

### Pick the right wrapper

`--with-prelude core|hdl` deliberately **excludes `show.typort`**. A probe that
prints `.show` will always fail under `run_probe.ps1`; that is a harness
limitation, not a probe bug. Use `run_check.ps1`, which loads the whole prelude.

---

## 4. `prelude_doc_cov.py`

```powershell
& .\target\debug\typort.exe doc target/prelude_scratch/doc_measure.typort `
    --out target/doc_json --format json --min-coverage 0
python tools/prelude_doc_cov.py target/doc_json            # dir or doc.json both work
python tools/prelude_doc_cov.py target/doc_json --nested   # include members
python tools/prelude_doc_cov.py target/doc_json --fail-under 60
```

`doc_measure.typort` contains exactly one **documented** declaration, so the
reported denominator is the builtin prelude's own item count.

* Default (top-level) counts `def` / `struct` / `enum` / `trait` items. `impl`
  blocks are anonymous and are **not** counted -- that is why documentation work
  is measured in "top-level items".
* `--nested` additionally counts `members` (trait methods, enum cases, record
  fields). Note that round-1's scratch script listed only speculative key names
  and missed the real `members` key, so its `--nested` silently counted nothing;
  that is fixed here. Today the top-level number can be 100% while the nested
  number is much lower -- check both when you claim a file is fully documented.
* `--fail-under PCT` makes it usable as a gate (exit 1 below the threshold).

---

## 5. Pitfall: cargo's "uplift copy" and locked `.exe` files

**Symptom.** `cargo build --bin typort --bin l13bench` ends with:

```
error: failed to remove file `...\target\debug\typort.exe`
Caused by: Access is denied. (os error 5)
```

**What is actually happening.** The compile and link **succeeded**. Cargo links
the real product to `target/debug/deps/<bin>.exe` and only then tries to replace
`target/debug/<bin>.exe` ("uplift copy"). On Windows that replacement fails while
any process still has the old exe open -- typically a teammate's probe. The build
is not broken; only the copy is.

**Workaround.** Take the fresh product from `deps/` and run it from your own
directory. This also removes the whole class of "we are locking each other's
binaries" contention:

```powershell
Copy-Item target\debug\deps\typort.exe   target\mybin\typort.exe   -Force
Copy-Item target\debug\deps\l13bench.exe target\mybin\l13bench.exe -Force
& .\target\mybin\typort.exe check myprobe.typort --max-infer-ms 20000

# or point a wrapper at your copy
powershell -ExecutionPolicy Bypass -File tools/probe/run_probe.ps1 `
    -File myprobe.typort -Exe target\mybin\l13bench.exe
```

Compare the `LastWriteTime` of `target/debug/deps/<bin>.exe` against your source
change to confirm the artifact is the one you just built.

**Same trap for tests.** `cargo test --test <name>` also builds every `[[bin]]`,
so it can fail at the uplift copy even though the test binary itself linked fine.
In that case run the freshly linked test binary directly -- it is equivalent to
`cargo test`:

```powershell
Get-ChildItem target\debug\deps\<name>-*.exe | Sort-Object LastWriteTime -Descending |
    Select-Object -First 1 | ForEach-Object { & $_.FullName }
```

`gate_l13.ps1` handles the common case automatically: when a suite's log carries
the `failed to remove file` / `os error 5` signature, it waits `-RetryWaitSec`
and retries the suite once. It never kills other people's processes unless you
explicitly pass `-KillStaleSec` (default 0).

**Related gotcha:** a teammate's build wrapper may kill every running
`typort`/`l13bench` to free the lock. That is why the probe wrappers have an
explicit `EXTERNAL-KILL` verdict instead of blaming your probe.

---

## 5b. Pitfall: `Start-Process -PassThru` cannot report an exit code

Do not build a Windows wrapper around `Start-Process ... -PassThru` and read
`$p.ExitCode`. In PowerShell 5.1, when the streams are redirected, that property
reads back **empty even after the process has exited**. The consequence is a
tool that miscounts both ways: a suite whose tests all printed
`test result: ok.` gets reported as a failure (because `$null -ne 0` is true),
and a genuinely failed command can be reported as fine.

The first version of `gate_l13.ps1` had exactly that bug -- it reported
`fail=4` while `hdl042` had actually passed 2/2. All suites and probes now go
through `BoundedProcess.ps1`, which uses `System.Diagnostics.Process` directly:
real `ExitCode`, live `WorkingSet64` polling for the memory ceiling, and both
streams decoded as UTF-8. Dot-source it and call `Invoke-BoundedProcess`:

```powershell
. .\tools\BoundedProcess.ps1
$r = Invoke-BoundedProcess -FilePath "cargo" -Arguments @("test","--lib","L13_namespace::") `
     -WorkingDirectory (Get-Location).Path -TimeoutSec 3600
$r.ExitCode; $r.TimedOut; $r.PeakGB; $r.AllLines
```

`gate_l13.ps1` additionally falls back to reading the `test result:` lines when
an exit code still cannot be obtained, and says so in the output rather than
silently guessing.

**Beware `target/release/`.** Old release binaries linger for weeks and bake in an
old prelude. Always pass an explicit binary (`TYPORT=...`, or `-Exe`) and print
its path and mtime before drawing conclusions from any run.

---

## 6. HDL behavioral verification (L3) on Windows

`tools/spinalhdl-verify/` elaborates the case files in
`tools/spinalhdl-verify/cases/` with `typort check`, generates a C++ testbench
plus stimulus, compiles it with Verilator, runs it, and compares the result
against the Python reference models.

### The simulator really is installed on this host

```
C:\msys64\mingw64\bin\verilator_bin.exe   Verilator 4.024
C:\msys64\mingw64\bin\iverilog.exe
C:\msys64\mingw64\bin\make.exe
C:\msys64\mingw64\bin\g++.exe
```

Three pipeline bugs used to make the harness report "no verilator" and **skip
everything with exit 0** -- which is how a month of behavioral verification
silently disappeared. Keep all three fixes when editing `verify.py` or
`dualclock_runner.py`; without them the harness goes back to silently skipping.

1. **Extensionless wrapper.** msys ships
   `C:\msys64\mingw64\bin\verilator` with no extension. Python's
   `shutil.which("verilator")` matches PATHEXT and returns `None` on Windows,
   while `shutil.which("verilator_bin")` finds it. The resolver now tries
   `$VERILATOR`, then `verilator`, then `verilator_bin`. Check it by hand:

   ```powershell
   python -c "import shutil; print(shutil.which('verilator'), shutil.which('verilator_bin'))"
   # -> None C:\msys64\mingw64\bin\verilator_bin.EXE
   ```

2. **Windows absolute paths confuse msys Verilator 4.024.** It concatenates
   `-Mdir` with the source path and then reports
   `Cannot find file containing module`. All verilator invocations therefore run
   with a relative source name and a relative `-Mdir` from inside the work
   directory.

3. **Backslashes inside generated C++ string literals.** Writing a Windows stim
   path straight into the testbench produced `\U` / `\A`, which g++ rejects with
   `incomplete universal character name`. The templates now use
   `os.path.basename(stim_file)`.

### Always know which prelude snapshot ran

The first version defaulted to `target/release/typort(.exe)`. On this machine
that file is from **2026-09-29**, so a run without an explicit `TYPORT`
elaborated every case against a month-old prelude -- and reproduced the
already-fixed FIFO deadlock as if it were current. The resolver now:

* honours `$TYPORT` verbatim (an explicit choice is a promise), otherwise
* picks the **newest mtime** among `target/debug/typort[.exe]`,
  `target/debug/deps/typort[.exe]` and `target/release/typort[.exe]`, and
* prints the chosen path, mtime, size and the full candidate list at startup,
* and exits 1 when no binary exists at all, instead of guessing.

That banner is the audit trail:

```
[typort] using F:\...\target\debug\typort.exe
[typort] mtime=2026-10-08 14:32:09 size=19957760 bytes  (source=newest)
[typort] candidates:
[typort]   2026-10-08 14:32:09  19957760  F:\...\target\debug\typort.exe  <- chosen
[typort]   2026-09-29 03:49:29   7798784  F:\...\target\release\typort.exe
```

A rebuild can replace the binary mid-run, so freeze a copy first when the result
is evidence. **Do not use "is `src/` clean?" as the test for a good snapshot**: a
round's closing tree legitimately carries deliberate, reviewed changes (round 2
kept `mod.rs`, `hdl-check-graph.typort`, `hdl-macros.typort` and two test modules
modified on purpose). An empty `git status --short -- src` is meaningful only
when the tree really is at a bare commit, as in round 1's `645dc3bd` A/B -- and
then write that fact down explicitly.

What actually establishes provenance is a recorded fingerprint:

```powershell
git rev-parse HEAD                                      # commit the tree is based on
git diff --stat                                         # every source change still present
Get-Process cargo, rustc -ErrorAction SilentlyContinue   # no writer in flight
Copy-Item target\debug\typort.exe target\prelude_scratch\my_sim\typort.exe -Force
$b = "target\prelude_scratch\my_sim\typort.exe"
Get-FileHash $b -Algorithm SHA256; Get-Item $b | Select-Object Length, LastWriteTime
$env:TYPORT = (Resolve-Path $b).Path
python -X utf8 tools/spinalhdl-verify/verify.py
```

Record, next to the log: `git rev-parse HEAD`, `git diff --stat`, the **sha256 of
every changed source file**, and the frozen binary's `size + mtime + sha256`. If
the source binary changes while the run is in flight, the log no longer
describes one prelude snapshot. (`run_meta_head.txt` under
`target/prelude_scratch/hdl_a_sim/` is an example of a snapshot taken while a
teammate's instrumentation was in the tree: it shows
`M src/prelude/hdl/hdl-check-graph.typort`. It was adequate for attributing a
reference-model bug, but it was NOT a clean-baseline snapshot, and it was not
presented as one.)

### Fingerprint every frozen copy -- a filename is not provenance

For any A/B comparison, record **`size` + `mtime` + `sha256`** for the frozen
binary, plus `git rev-parse HEAD` (or the tree state) it came from:

```powershell
$b = "target\prelude_scratch\my_sim\typort.exe"
Get-FileHash $b -Algorithm SHA256
Get-Item $b | Select-Object Length, LastWriteTime
```

**Names lie.** This round a copy named
`target/prelude_scratch/hdl_a_sim/typort_head.exe` (mtime 14:51:49) was *not* a
clean-HEAD build at all -- it contained a teammate's in-flight patch
(`HDL038=1 / HDL037=1`), while the actual clean HEAD build was
`verify2/bin/typort_r2.exe` (13:56:32, `HDL038=2 / HDL039=0`). The name said
"head"; the bytes said otherwise. A related miss: a reading taken from a
mid-round build (11:47:26) was compared against a committed-state assertion and
produced a phantom "test blind spot". Both were measurement accidents, not
product defects. Only the hash + mtime + tree state settle provenance.

### A warning-level reproduction is not proof that a source defect exists

"Latent" defects can be shown to exist by reading the source and instrumenting
it. But **observability must be measured on a clean baseline**: if a warning
appears only under a patched/instrumented build, that tells you the *instrument*
fires, not that the defect is reachable in the shipped tree. Separate the two
claims in the report, and re-measure the second one on a frozen clean build.

### Reference models can be stale -- check the contract, not the diff

The first full L3 run reported 50/51 with `vStreamM2s` failing. The RTL was
**right** and the Python reference was **wrong**: `RefStreamM2s` still encoded
`input.ready = rValid || pop_ready`, which
`docs/hdl-stream-fsm-design.md:38` records as defect **F1** (full/empty condition
swapped); the corrected contract is `input.ready = pop_ready || !rValid`, and
`hdl-stream.typort:106` implements that. A month-old release binary produced the
identical 56 mismatches, so it was never a regression -- the reference simply
disagreed with a correct design.

So when a case fails, classify it against the design doc **before** suspecting
the RTL. The doc's own fix list (F1 m2sPipe, F2 s2mPipe, F3 throwWhen,
F4 haltWhen/takeWhen, F5 flowMuxPayload) is the checklist of places where the
design was deliberately changed and a reference model may have been left behind.

Related coverage gap found the same way: of those five fixed entry points, only
**F1 has an L3 case at all** (`v_stream_sequential.typort`). F2, F3, F4 and F5
have no behavioral case, so their fixes rest on L1/L2 only -- the design doc
flags exactly this blind spot (its "O4" note). Treat "all default cases pass" as
coverage of what the cases exercise, not of the whole library.

### Fallback simulator

`iverilog.exe` sits on the same PATH and can stand in when Verilator is
unavailable, but the generated testbench and `-Mdir` flow here are
Verilator-shaped, so switching simulators is a code change rather than a flag.
Treat iverilog as a rescue option for a single module, not a drop-in.

### Results

`DEFAULT_CASES` is the five files in `tools/spinalhdl-verify/cases/`. Full-set
runs and their logs are kept under `target/prelude_scratch/<owner>_sim/` (with
the frozen binary and a `run_meta.txt` recording HEAD and mtimes).

---

## 7. Conventions for reporting

* Paste the raw `test result:` / verdict line, not a paraphrase.
* Say whether calibration ran (`-NoCalibrate` means the judge was unverified).
* Quote the exe path and its mtime when a run's result depends on the built
  prelude.
* `INCONCLUSIVE` is not a pass. Read the raw tail and say what you saw.
* Keep log directories per-owner (`-OutDir`, `-LogDir`) so parallel runs do not
  overwrite each other's evidence.

## 8. Not yet formalized

* `build.ps1` (wait-for-quiet, kill stale probes, build, retry once on the exe
  lock) still lives in `target/prelude_scratch/`. It belongs here next; until
  then use `cargo build --bin typort --bin l13bench` plus the `deps/` recipe in
  section 5.
* `tools/spinalhdl-verify/` and the other `tools/*.sh` helpers are owned by other
  workstreams; this README does not cover them.
