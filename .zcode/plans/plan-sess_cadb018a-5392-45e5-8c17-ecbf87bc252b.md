# TyportHDL 接入 EDA 工具链（Verilator 优先，SpinalSim 风格）

## 已确认的决策
- **不做** in-HDL 仿真原语（assert/initial/延时/$display 先不要）
- 仿真照 **SpinalHDL SpinalSim** 走：测试床用宿主语言 **Rust** 写，交互式驱动 Verilator 编译出的模型（`dut.set/get`、时钟激励、波形），而非 veryl 的 in-HDL `#[test]` 发射式
- 第一版只接 Verilator；进程调用按 veryl 的 Runner trait 思路设计成可扩展
- 直接引入 **Typort.toml** 项目配置
- 每完成一个阶段 commit 一次

## 架构总览
```
.typort 源 ──Backend elaboration──► typort emit --top 'adder[8]'
                                        │
                        ┌───────────────┴───────────────┐
                        ▼                               ▼
                 out/adder.v                     out/manifest.json
                        │                        （端口/宽度/方向/时钟域）
                        ▼
              src/sim/ 仿真库（同 crate 新模块）
              SimConfig::compile() → verilator --cc --exe + 生成的 C++ harness（stdin 命令协议）→ make
                        ▼
              Dut 句柄: set/get/sleep/clock().fork()/波形   ←—— Rust 测试（cargo test，缺 verilator 自动跳过）
```

## 分步提交计划

### Commit 1 — `typort emit`：Verilog 落盘通道（工具底座）
- `src/bin/cli.rs` 增 `emit` 子命令：`typort emit <files...> --top 'adder[8]' [--out DIR | --stdout]`
- 实现复用 Backend + 虚拟 URI 机制（`builtin:///` 先例）：合成虚拟源 `println(allModulesVL(<top>.create.tree))`，elaborate 后从 `DeclTm::Println`（lib.rs:1016）捕获字符串写盘
- `--top` 语法与 create 参数形态一致（`adder[8]`，多参数逗号分隔）
- 测试：对 `examples/hdl` 若干例 emit，断言生成 Verilog 含关键片段（沿用 legacy_tests 的 substring 断言风格）
- 这是后续所有工具的统一入口，终结 verify.py 的 stderr 正则抓取

### Commit 2 — manifest：结构化设计元数据（语言底座）
- prelude 新增 `moduleTreeManifest(t): String`（JSON）：各模块名、端口（名/方向/宽度）、时钟域（clk/reset 名、极性、edge——ModuleDef 已携带 ClockDomain，hdl-core.typort:85）、实例层次、参数
- `typort emit --manifest` 同时输出 manifest.json
- 测试：emit 后用 serde_json 解析断言字段
- sim 库消费 manifest 访问端口，不再解析 Verilog 文本

### Commit 3 — sim 底座：Verilator 编译流水线
- 新模块 `src/sim/`（同 crate，不 workspace 化，可直接调 Backend 库内 API 完成 emit，免去子进程自调用）
- `SimConfig { top, files, verilator_path(env VERILATOR 可覆盖), compile_args, trace }` → `compile()`：在 workdir 生成 C++ harness（stdin 行命令协议：set/get/eval/tick/sleep/finish，宽端口 hex 字符串），调 `verilator --cc --exe`（参数对齐 verify.py 已验证的组合）→ `make`
- 进程调用用 `std::process::Command`（同步，符合现有无线程池模型）
- 缺 verilator 时返回明确错误；集成测试检测后跳过（学 verify.py 的 skip 模式）
- 测试：adder 跑通 emit→编译→产物存在（有 verilator 才跑）

### Commit 4 — Dut 交互 API + 时钟辅助 + 首批仿真测试
- `Dut`：`set(name, u64)`/`get(name)`（按 manifest 宽度校验）、`sleep(n)`、`clock("clk").fork(period)`（线程化时钟激励 ≈ forkStimulus）、`finish()`、`--trace` VCD 波形落盘
- 集成测试：examples 的 adder（组合）+ counter/fifo（时序含复位序列）；从 verify.py 移植 2-3 个 golden case 作等价性证明
- 失败时打印复现命令与波形路径

### Commit 5 — Typort.toml + build/test 子命令收口
- 新 metadata 模块解析 `Typort.toml`（serde `deny_unknown_fields`，学 veryl/metadata）：`[project]` name；`[test]` simulator="verilator"、waveform_format；`[test.verilator]` compile_args/simulate_args/tool 路径；CLI 参数可覆盖配置
- `typort build`：读配置 → emit 到 target 目录 + 生成 filelist(.f)（veryl 模式，解耦 build 与 sim）
- `typort test`：读配置 → 编译并运行声明的仿真；sim 库读同一配置
- 依赖增量：serde 加 `derive` feature、新增 `toml` crate

## 后续（记录在案，本次不做）
iverilog 第二 runner（验证抽象）、LSP 自定义请求 `typort-hdl/runSimulation`（沿 builtinContent 先例）、verify.py 全量语料迁移、yosys 等综合工具接入、verilator 输出错误位置→源位置映射

## 实现注意
- 动手第一步：探测 `verilator --version`/`make`/`g++` 可用性（verify.py 证明直接调用路径可行）
- prelude 改动走 `clone_prelude_state` 缓存路径，注意 load_prelude 计时不回退（基准见 docs/opt-verilog.md）
- 每步完成后跑 `cargo test`（test profile 已 opt-level=2）再 commit