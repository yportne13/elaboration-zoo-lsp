//! `typort tutorial` — interactive, in-terminal tour of the Typort language.
//!
//! Each lesson explains one concept, opens your `$EDITOR` on a small source
//! file, and type-checks your solution through the real elaborator. A hidden
//! check function is appended to every attempt, so a lesson counts as passed
//! only when the required declarations exist and compute to the expected
//! values (definitional equality does the grading).

use std::fs;
use std::io::{self, BufRead, Write};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use colored::Colorize;
use lsp_types::{Diagnostic, DiagnosticSeverity, MessageType, Url};

use crate::client::{render_diagnostics_stderr, ClientLike};
use crate::{Backend, TextDocumentItem};

// ---------------------------------------------------------------------------
// Lessons
// ---------------------------------------------------------------------------

struct Lesson {
    title: &'static str,
    /// Concept explanation shown before editing.
    concept: &'static str,
    /// What the user has to do.
    task: &'static str,
    starter: &'static str,
    /// Appended to the user's code before checking; forces the required
    /// declarations to exist with the expected types/behaviour.
    check: &'static str,
}

macro_rules! lesson {
    ($title:expr, $concept:expr, $task:expr, $starter:expr, $check:expr $(,)?) => {
        Lesson { title: $title, concept: $concept, task: $task, starter: $starter, check: $check }
    };
}

const LESSONS: &[Lesson] = &[
    lesson!(
        "值与类型",
        concat!(
            "Typort 中一切表达式都有类型。内置的 Nat 是皮亚诺自然数：\n",
            "  zero 是 0，succ(n) 是 n+1；整数字面量是语法糖，`3` 就是\n",
            "  succ(succ(succ(zero)))。\n",
            "\n",
            "顶层定义用 def：<名字>: <类型> = <表达式>"
        ),
        "把 `_`（待填的洞）换成任意一个 Nat 表达式，比如 42 或 6 * 7。",
        "def answer: Nat = _\n",
        "def __tut_check(): Eq answer answer = rfl\n",
    ),
    lesson!(
        "定义函数",
        concat!(
            "函数定义带参数与返回类型：\n",
            "  def triple(n: Nat): Nat = n * 3\n",
            "\n",
            "`+`、`*` 不是语法：它们通过类型类（Add/Mul）的实例派发到\n",
            "prelude 里的 nat_add/nat_mul。调用可以用空格 f x 或括号 f(x)。"
        ),
        "实现 triple(n) = n * 3（把 `_` 换成函数体）。",
        "def triple(n: Nat): Nat = _\n",
        "def __tut_check(): Eq (triple 14) 42 = rfl\n",
    ),
    lesson!(
        "模式匹配",
        concat!(
            "match 对数据进行分支，case 是构造子模式：\n",
            "  match n {\n",
            "      case zero    => zero\n",
            "      case succ(m) => m\n",
            "  }\n",
            "\n",
            "succ(m) 把构造子的参数绑定为新名字 m。"
        ),
        "实现 my_pred：0 的前驱还是 0，succ(m) 的前驱是 m。",
        "def my_pred(n: Nat): Nat =\n    match n {\n        case zero => zero\n        case succ(m) => _\n    }\n",
        "def __tut_check(): Eq (my_pred 5) 4 = rfl\n",
    ),
    lesson!(
        "递归",
        concat!(
            "归纳类型天然配递归：按第二个参数分解加法\n",
            "  x + 0       = x\n",
            "  x + succ(n) = succ(x + n)\n",
            "\n",
            "（注意第二行对 y 归纳，这正是 prelude 里 nat_add 的形状。）"
        ),
        "用 match + 递归实现 add(x, y)，不要直接用 `+`。",
        "def add(x: Nat, y: Nat): Nat =\n    match y {\n        case zero => x\n        case succ(n) => _\n    }\n",
        "def __tut_check(): Eq (add 2 3) 5 = rfl\n",
    ),
    lesson!(
        "自定义枚举",
        concat!(
            "enum 声明一个求和类型，每个 case 一个构造子：\n",
            "  enum Color {\n",
            "      red\n",
            "      green\n",
            "      blue\n",
            "  }\n",
            "\n",
            "限定名是 Color.red，但 prelude 会自动给裸名别名。"
        ),
        "定义 enum Color（含 red/green/blue），并让 favorite 等于其中之一。",
        "// 在这里定义 Color，然后填空：\ndef favorite: Color = _\n",
        "def __tut_check(): Eq favorite favorite = rfl\n",
    ),
    lesson!(
        "match 与枚举",
        concat!(
            "枚举的每个构造子都是一个 case；漏写分支会被类型检查器抓住。"
        ),
        "实现 next：季节循环 spring → summer → autumn → winter → spring。",
        "enum Season {\n    spring\n    summer\n    autumn\n    winter\n}\n\ndef next(s: Season): Season =\n    match s {\n        case spring => summer\n        case summer => autumn\n        case autumn => winter\n        case winter => _\n    }\n",
        "def __tut_check(): Eq (next winter) spring = rfl\n",
    ),
    lesson!(
        "结构体",
        concat!(
            "struct 是积类型（命名的元组）：\n",
            "  struct Pair[A, B] {\n",
            "      first: A\n",
            "      second: B\n",
            "  }\n",
            "\n",
            "构造：new Pair(1, true)；访问：p.first / p.second。\n",
            "[A, B] 是隐式类型参数，由使用处的类型推导。"
        ),
        "实现 swap，交换两个分量的顺序（Pair[A,B] 变成 Pair[B,A]）。",
        "struct Pair[A, B] {\n    first: A\n    second: B\n}\n\ndef swap[A, B](p: Pair[A, B]): Pair[B, A] = _\n",
        "def __tut_check(): Eq (swap (new Pair(1, true))) (new Pair(true, 1)) = rfl\n",
    ),
    lesson!(
        "多态函数",
        concat!(
            "方括号声明隐式类型参数，调用时自动推导或用 f[T] 手动给出：\n",
            "  def ident[A](x: A): A = x\n",
            "  ident[Nat] 7   // 显式填 A = Nat\n",
            "  ident true     // 推导 A = Boolean"
        ),
        "实现恒等函数 ident：原样返回参数。",
        "def ident[A](x: A): A = _\n",
        "def __tut_check(): Eq (ident true) true = rfl\n",
    ),
    lesson!(
        "Option 与高阶函数",
        concat!(
            "Option[A] 表示可能缺失的值（prelude 已提供）：\n",
            "  None | Some(x)\n",
            "\n",
            "函数作为值传递：f: A -> B，调用 f x。"
        ),
        "实现 map_opt：None 原样返回；Some(x) 返回 Some(f x)。",
        "def map_opt[A, B](o: Option[A], f: A -> B): Option[B] =\n    match o {\n        case None => _\n        case Some(x) => _\n    }\n",
        "def __tut_check(): Eq (map_opt(Some 1, x => x + 2)) (Some 3) = rfl\n",
    ),
    lesson!(
        "依赖类型入门：Vec",
        concat!(
            "Vec[A](len) 是长度索引的向量，类型里带着数据：\n",
            "  enum Vec[A](len: Nat) {\n",
            "      nil -> Vec[A] 0\n",
            "      cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (l + 1)\n",
            "  }\n",
            "\n",
            "返回类型可以依赖值参数：Vec[Nat] n 的 n 是一个 Nat 表达式。\n",
            "显式填隐式参数用方括号：zeros[3]。"
        ),
        "实现 zeros[n]: 长度为 n 的全零向量（对 n 递归；cons(0, ...) 包一层）。",
        "// 提示：zero 情形是 nil；succ(m) 情形是 cons(0, zeros[m])\ndef zeros[n: Nat]: Vec[Nat] n = _\n",
        "def __tut_check(): Eq (zeros[2]) (cons(0, cons(0, nil))) = rfl\n",
    ),
    lesson!(
        "等式与证明",
        concat!(
            "Eq x y 是「x = y」的类型；构造它的项就是证明：\n",
            "  rfl          — 自反性（两边可定义归约到同一值时即可）\n",
            "  add_comm(a,b) 等 prelude 引理 — 组合已有事实\n",
            "\n",
            "由于 2+3 与 5 都能归约成同一个字面量，这里 rfl 就够了；\n",
            "而 add_comm(2, 3) 同样成立——两条路都通。"
        ),
        "为 `2 + 3 = 5` 给出一个证明（试试 rfl，再试试 add_comm(2, 3)）。",
        "def two_plus_three: Eq (2 + 3) 5 = _\n",
        "def __tut_check(): Eq (2 + 3) 5 = two_plus_three\n",
    ),
    lesson!(
        "类型类与运算符重载",
        concat!(
            "trait 声明接口，impl 为具体类型提供实例：\n",
            "  impl Add[Wrap, Wrap] for Wrap {\n",
            "      def +(that: Wrap): Wrap = ...\n",
            "  }\n",
            "\n",
            "之后 wrap(1) + wrap(2) 中的 + 就派发到这里；方法体里\n",
            "this 指代左操作数。"
        ),
        "为 Wrap 实现 Add：解开包装、Nat 相加、再包回去。",
        "enum Wrap {\n    wrap(v: Nat)\n}\n\nimpl Add[Wrap, Wrap] for Wrap {\n    def +(that: Wrap): Wrap = _\n}\n",
        "def __tut_check(): Eq (wrap(40) + wrap(2)) (wrap 42) = rfl\n",
    ),
    lesson!(
        "HDL 初体验",
        concat!(
            "Typort 也是一门硬件描述语言。module 宏声明一个电路模块：\n",
            "  module m {\n",
            "      input  a = Bool      // 输入端口\n",
            "      output s = Bool      // 输出端口\n",
            "      s := a ^ b           // := 驱动信号（^ 异或、&& 与、|| 或、! 非）\n",
            "  }\n",
            "\n",
            "moduleTreeVL(m.create.tree) 打印生成的模块树（显示为 note）。"
        ),
        "驱动半加器的两个输出：sum = a XOR b，carry = a AND b。",
        "module half_adder {\n    input a = Bool\n    input b = Bool\n    output sum = Bool\n    output carry = Bool\n\n    sum := sum_todo\n    carry := carry_todo\n}\n\nprintln(moduleTreeVL(half_adder.create.tree))\n",
        "",
    ),
];

const CHECK_MARKER: &str = "\n// ---- typort tutorial check ----\n";

// ---------------------------------------------------------------------------
// Capturing client
// ---------------------------------------------------------------------------

#[derive(Default)]
struct Capture {
    diags: Mutex<Vec<Diagnostic>>,
}

/// A `ClientLike` that records published diagnostics instead of rendering.
struct CapturingClient {
    capture: Arc<Capture>,
}

impl ClientLike for CapturingClient {
    fn publish_diagnostics(&self, _uri: Url, diagnostics: Vec<Diagnostic>, _version: Option<i32>) {
        self.capture.diags.lock().unwrap().extend(diagnostics);
    }
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, _message: String) {}
}

fn has_errors(diags: &[Diagnostic]) -> bool {
    diags.iter().any(|d| d.severity == Some(DiagnosticSeverity::ERROR))
}

// ---------------------------------------------------------------------------
// Progress persistence
// ---------------------------------------------------------------------------

fn progress_path() -> Option<PathBuf> {
    let home = std::env::var_os("USERPROFILE")
        .or_else(|| std::env::var_os("HOME"))?;
    Some(PathBuf::from(home).join(".typort-tutorial-progress.json"))
}

fn load_progress() -> Vec<usize> {
    let Some(path) = progress_path() else { return vec![] };
    let Ok(text) = fs::read_to_string(&path) else { return vec![] };
    #[derive(serde::Deserialize)]
    struct Progress { #[serde(default)] completed: Vec<usize> }
    serde_json::from_str(&text).unwrap_or(Progress { completed: vec![] }).completed
}

fn save_progress(completed: &[usize]) {
    let Some(path) = progress_path() else { return };
    #[derive(serde::Serialize)]
    struct Progress<'a> { completed: &'a [usize] }
    if let Ok(json) = serde_json::to_string_pretty(&Progress { completed }) {
        let _ = fs::write(&path, json);
    }
}

// ---------------------------------------------------------------------------
// Editing
// ---------------------------------------------------------------------------

fn editor_command() -> String {
    std::env::var("VISUAL")
        .or_else(|_| std::env::var("EDITOR"))
        .unwrap_or_else(|_| if cfg!(windows) { "notepad".into() } else { "vi".into() })
}

/// Launch the external editor on `path`; returns false when it could not be
/// spawned or exited unsuccessfully (caller falls back to stdin editing).
fn open_editor(path: &PathBuf) -> bool {
    let cmd = editor_command();
    let mut parts = cmd.split_whitespace();
    let Some(prog) = parts.next() else { return false };
    std::process::Command::new(prog)
        .args(parts)
        .arg(path)
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// Minimal fallback when no external editor is available: read the program
/// from stdin until a line with a single `.`.
fn edit_via_stdin(current: &str) -> Option<String> {
    eprintln!("外部编辑器不可用；请直接粘贴代码，单独一行 `.` 结束。当前内容：");
    print_numbered(current);
    eprintln!("--- 在下面输入，单独一行 `.` 结束 ---");
    let mut buf = String::new();
    for line in io::stdin().lock().lines() {
        let Ok(line) = line else { break };
        if line.trim() == "." {
            return Some(buf);
        }
        buf.push_str(&line);
        buf.push('\n');
    }
    Some(buf)
}

fn print_numbered(code: &str) {
    for (i, line) in code.lines().enumerate() {
        eprintln!("{:>3} | {}", i + 1, line);
    }
}

fn read_line_trimmed() -> Option<String> {
    let mut s = String::new();
    match io::stdin().lock().read_line(&mut s) {
        Ok(0) => None,
        Ok(_) => Some(s.trim().to_string()),
        Err(_) => None,
    }
}

// ---------------------------------------------------------------------------
// Lesson runner
// ---------------------------------------------------------------------------

#[derive(PartialEq)]
enum Outcome {
    Passed,
    Skipped,
    Quit,
}

struct TutorialCtx {
    backend: Arc<Backend<CapturingClient>>,
    capture: Arc<Capture>,
    workdir: PathBuf,
    version: i32,
}

fn init_backend() -> TutorialCtx {
    let capture = Arc::new(Capture::default());
    let backend = Backend::new(CapturingClient { capture: capture.clone() });
    // Full prelude (incl. HDL) so the final HDL lesson can use `module`,
    // `moduleTreeVL`, `:=` etc. — same loading path as `typort check`.
    backend.load_prelude();
    let workdir = std::env::temp_dir().join("typort_tutorial");
    let _ = fs::create_dir_all(&workdir);
    TutorialCtx { backend, capture, workdir, version: 0 }
}

impl TutorialCtx {
    fn check(&mut self, uri: Url, text: &str) -> Vec<Diagnostic> {
        self.version += 1;
        self.capture.diags.lock().unwrap().clear();
        self.backend.on_change::<false>(TextDocumentItem {
            uri,
            text,
            version: Some(self.version),
        });
        std::mem::take(&mut *self.capture.diags.lock().unwrap())
    }
}

fn run_lesson(ctx: &mut TutorialCtx, idx: usize, done_before: bool) -> Outcome {
    let lesson = &LESSONS[idx];
    let path = ctx.workdir.join(format!("lesson_{:02}.typort", idx + 1));

    println!("{}", format!("第 {} / {} 课 · {}", idx + 1, LESSONS.len(), lesson.title).bold());
    println!("{}", lesson.concept);
    println!("{} {}", "任务:".green().bold(), lesson.task);

    // Resume from whatever was last written for this lesson, else starter.
    let mut code = fs::read_to_string(&path).unwrap_or_else(|_| lesson.starter.to_string());

    loop {
        if fs::write(&path, &code).is_err() {
            eprintln!("无法写入练习文件 {}", path.display());
            return Outcome::Quit;
        }

        let ok_editor = open_editor(&path);
        code = if ok_editor {
            fs::read_to_string(&path).unwrap_or(code)
        } else {
            match edit_via_stdin(&code) {
                Some(c) => c,
                None => return Outcome::Quit,
            }
        };

        let mut full = code.clone();
        if !full.ends_with('\n') {
            full.push('\n');
        }
        full.push_str(CHECK_MARKER);
        full.push_str(lesson.check);

        let uri = Url::from_file_path(path.canonicalize().unwrap_or_else(|_| path.clone()))
            .expect("temp path to url");
        let diags = ctx.check(uri, &full);
        render_diagnostics_stderr(&format!("lesson_{:02}.typort", idx + 1), &full, &diags);

        if !has_errors(&diags) {
            println!("{}", "✓ 通过！".green().bold());
            return Outcome::Passed;
        }

        println!();
        println!("{}", "还有错误 —— 类型检查器就是你的陪练。".yellow());
        print!("[{}] [回车] 继续编辑 · v 查看 · r 重置 · s 跳过 · q 退出 > ",
            if done_before { "已完成" } else { "进行中" });
        let _ = io::stdout().flush();

        let Some(choice) = read_line_trimmed() else { return Outcome::Quit };
        match choice.as_str() {
            "" => {}
            "v" | "V" => print_numbered(&code),
            "r" | "R" => {
                code = lesson.starter.to_string();
                println!("{}", "已恢复初始代码。".dimmed());
            }
            "s" | "S" => return Outcome::Skipped,
            "q" | "Q" => return Outcome::Quit,
            _ => {}
        }
    }
}

/// First uncompleted lesson index (0-based); if everything is done, fall
/// back to the last lesson for a review pass.
fn resume_start(completed: &[usize]) -> usize {
    completed.iter().max().map_or(0, |&m| (m + 1).min(LESSONS.len() - 1))
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

pub struct TutorialOptions {
    pub start_lesson: Option<usize>,
    pub list: bool,
    pub reset: bool,
}

pub fn run(opts: TutorialOptions) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    if opts.reset {
        if let Some(p) = progress_path() {
            match fs::remove_file(&p) {
                Ok(()) => println!("已清除进度记录（{}）。", p.display()),
                Err(_) => println!("没有找到进度记录。"),
            }
        }
        return Ok(());
    }

    let completed = load_progress();

    if opts.list {
        println!("{}", "Typort 交互式教程".bold());
        for (i, l) in LESSONS.iter().enumerate() {
            let mark = if completed.contains(&i) { "✓" } else { " " };
            println!("  [{mark}] {:2}. {}", i + 1, l.title);
        }
        println!("\n运行 `typort tutorial --lesson N` 从第 N 课开始。");
        return Ok(());
    }

    println!("{}", "═══ Typort 交互式教程 ═══".bold());
    println!("每课先讲概念，再在你的编辑器里改代码；类型检查通过即过关。");
    println!("随时输入 q 退出，进度保存在本地，下次继续。\n");

    // Resume point: explicit --lesson N, else first uncompleted lesson.
    let start = match opts.start_lesson {
        Some(n) if n >= 1 && n <= LESSONS.len() => n - 1,
        Some(n) => {
            println!(
                "{}",
                format!("警告: 没有第 {n} 课（共 {} 课），已回落到当前位置。", LESSONS.len()).yellow()
            );
            resume_start(&completed)
        }
        None => resume_start(&completed),
    };

    if completed.len() == LESSONS.len() && start == LESSONS.len() - 1 {
        println!(
            "{}",
            "你已完成全部课程；现在复习最后一课。用 --reset 可从头开始。".dimmed()
        );
    }

    let mut ctx = init_backend();
    let mut completed = completed;
    let mut passed_here = 0usize;

    for idx in start..LESSONS.len() {
        let done_before = completed.contains(&idx);
        match run_lesson(&mut ctx, idx, done_before) {
            Outcome::Passed => {
                if !done_before {
                    completed.push(idx);
                    save_progress(&completed);
                }
                passed_here += 1;
                if idx + 1 < LESSONS.len() {
                    print!("\n[回车] 下一课 · q 退出 > ");
                    let _ = io::stdout().flush();
                    match read_line_trimmed() {
                        None => break,
                        Some(c) if c.eq_ignore_ascii_case("q") => break,
                        _ => {}
                    }
                }
            }
            Outcome::Skipped => continue,
            Outcome::Quit => break,
        }
    }

    let total_done = completed.len();
    println!("\n{}", "═══ 本轮结束 ═══".bold());
    println!("本轮通过 {passed_here} 课，总进度 {total_done} / {}", LESSONS.len());
    if total_done == LESSONS.len() {
        println!("{}", "全部完成！接下来可以读 examples/ 目录里的真实代码了。".green());
    } else {
        println!("继续：typort tutorial");
    }
    Ok(())
}
