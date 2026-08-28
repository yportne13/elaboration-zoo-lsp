//! L01 NBE 变体基准的独立二进制。
//!
//! 与 `typort`（语言服务器/编译器的总二进制）完全解耦：本 bin 不引用
//! `elaboration_zoo_lsp` 库，只通过 `#[path]` 直接编译 `src/list.rs` 和
//! `src/L01_nbe/`——L01 的基准因此不关心（也不被阻塞于）其余各层
//! （L02…L13）的编译状态。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l01bench [--max-church 8000] [--rounds 5] [--only cek]
//!                                     [--workload church|dup|all]
//! ```

use clap::Parser;

// NBE 求值大量小分配（Rc 环境节点、Box 项、Vec 字节），Windows 默认堆
// 在这个模式上比 mimalloc 慢约 4 倍（typort 的 cli.rs 同样挂载）；基准
// 必须与生产二进制使用同一分配器才有可比性。
#[global_allocator]
static ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[path = "../list.rs"]
mod list;

#[path = "../L01_nbe/mod.rs"]
pub mod L01_nbe;

#[derive(Parser)]
#[command(
    name = "l01bench",
    about = "L01 NBE 变体基准：church_pair(n) 归一化，正确性断言 + 多轮计时",
    after_help = "n > 8000 时只有 cek 能跑（其余变体递归链栈溢出）。"
)]
struct Cli {
    /// 最大教堂数规模 n（从 1000 起翻倍）
    #[arg(long, default_value_t = 4000)]
    max_church: usize,

    /// 每变体每规模的计时轮数
    #[arg(long, default_value_t = 5)]
    rounds: usize,

    /// 只跑指定变体（逗号分隔多值，如 cek 或 bump_arena,bump_tree）
    #[arg(long)]
    only: Option<String>,

    /// 负载族：church（church_pair，默认）| dup（复制强制，开记忆化轴）| all
    #[arg(long, default_value = "church")]
    workload: String,
}

fn main() {
    let cli = Cli::parse();
    // 大栈线程：bump 系迭代变体（cek_bump/bump_iter/bump_spine_iter）全链路
    // 迭代化后 4MB 栈即可跑到 51 万+（L01_STACK_MB=4 可复验）；仍需大栈的
    // 只有 `cek`（Value 派生 Clone/Drop 对深 Box 树递归，见 cek.rs 头注释）
    // 和小 n 段的递归 import/export 接线。默认 128MB 留足余量。
    let stack_mb: usize = std::env::var("L01_STACK_MB")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(128);
    std::thread::Builder::new()
        .stack_size(stack_mb << 20)
        .spawn(move || {
            L01_nbe::bench::run(cli.max_church, cli.rounds, cli.only.as_deref(), &cli.workload)
        })
        .unwrap()
        .join()
        .unwrap();
}