# Stevia

Stevia is a reusable SystemVerilog RTL block library. The goal is to provide
small, composable, synthesis-friendly hardware building blocks with enough
automation around them that they can be reused with confidence.

The library is intentionally conservative. RTL should be easy to instantiate in
a wide range of projects, easy for open-source tools to parse, and easy to
verify in isolation. The main deliverable is the RTL under `rtl/`; everything
else in this repository exists to check that RTL before pull requests are merged
or releases are cut.

Stevia is early in its modernization. The current active RTL surface is focused
on utility blocks under `rtl/util`, including counters, arbiters, buffering,
FIFO, one-hot conversion, and leading-zero count blocks. Earlier exploratory
RTL and tests live under `legacy/` so they can be recovered or rewritten without
being treated as release-quality blocks.

## Quick Start

Install the pinned repo-local tools and Python environment:

```sh
scripts/install_tools.sh
```

Run the full local check suite:

```sh
make all
```

Or run individual checks:

```sh
make lint
make test
make formal
make synth
```

Generated tool installs, virtual environments, logs, simulation builds, and
result files are ignored by git. Check artifacts are written under each flow's
local `outputs/` directory, such as `lint/outputs/`, `test/outputs/`,
`formal/outputs/`, and `synth/outputs/`. Clean generated outputs with:

```sh
make clean
```

## Use Patterns

The top-level targets run the same checks used by CI. They are useful when you
want to check the active RTL surface as a whole:

```sh
make lint
make test
make formal
make synth
make all
```

Focused lint runs are available for design iteration. By default, lint uses
`rtl/filelist.f` and writes logs under `lint/outputs/_all/`. Passing `FILE` or
`MODULE` creates a scoped filelist and writes logs under a module or file scope
such as `lint/outputs/stv_lzc/`:

```sh
make lint FILE=rtl/util/stv_lzc.sv
make lint MODULE=stv_lzc
```

Individual lint tools can also be selected:

```sh
make lint TOOL=slang
make lint MODULE=stv_lzc TOOL=verible
make lint FILE=rtl/util/stv_lzc.sv TOOL=verilator
```

The supported lint tools are `slang`, `verible`, and `verilator`.

Simulation can optionally dump VCD waveforms. Wave-enabled runs write each
parameterized test's results and waveform into a module/configuration directory
under `test/outputs/<module>/`:

```sh
make test WAVES=1
gtkwave test/outputs/stv_sync_fifo/stv_sync_fifo_d2/stv_sync_fifo_d2.vcd
```

## Repository Layout

`rtl/` contains the synthesizable SystemVerilog source. `rtl/filelist.f` is the
tool-facing source list used by lint and simulation. Only modules listed there
are part of the active library surface.

`legacy/` contains pre-modernization RTL and tests that are intentionally
excluded from the default checks.

`test/` contains cocotb tests arranged to mirror the active RTL hierarchy. For
example, utility RTL under `rtl/util/` is tested under `test/util/`.

`formal/` contains SymbiYosys harnesses for modules where formal checks are
practical. Each target owns its `.sby` file and wrapper properties.

`synth/` contains Yosys synthesis smoke checks. These checks are meant to catch
unsupported syntax, unsynthesizable constructs, and basic elaboration problems.

`lint/` contains lint configuration and the lint Makefile.

Each flow owns an ignored `outputs/` directory for generated logs, simulation
builds, formal work directories, and synthesis reports. These directories may
be deleted at any time.

`scripts/` contains helper scripts for repeatable tool setup and filelist
processing.

## Coding Requirements

All RTL should follow these project rules:

1. Do not use SystemVerilog interfaces.
2. Use asynchronous active-low resets named `arst_n`.
3. Use parameters and localparams instead of preprocessor defines for module
   configuration.
4. Keep reusable blocks self-contained and listed in `rtl/filelist.f`.
5. Prefer simple ready/valid ports for streaming data.
6. Avoid tool-specific RTL unless it is isolated, documented, and covered by
   the lint/synthesis flow.
7. Use plain packed data ports with width parameters in reusable primitives;
   keep parameterized payload types in wrappers or integration code.

## Recommended RTL Practices

Write modules as reusable library components, not as one-off subsystem glue.
Interfaces should be explicit ports, with stable naming and parameterization.
For portable library primitives, prefer `WIDTH` parameters and packed
`logic [WIDTH-1:0]` data ports over `parameter type` payloads. Packed structs
can still connect directly to these vector ports from wrapper or integration
code:

```systemverilog
typedef struct packed {
  logic [7:0] len;
  logic [2:0] size;
} axi_len_size_t;

axi_len_size_t fifo_din;
axi_len_size_t fifo_dout;

stv_sync_fifo #(
  .WIDTH($bits(axi_len_size_t)),
  .DEPTH(8)
) u_fifo (
  .clk,
  .arst_n,
  .clear,
  .din_valid,
  .din_ready,
  .din(fifo_din),
  .dout_valid,
  .dout_ready,
  .dout(fifo_dout),
  .empty,
  .full,
  .count
);
```

This keeps core blocks friendly to Verilator, Yosys, formal tools, and older
flows while preserving typed readability at the edges. Avoid passing large
monolithic structs through a primitive when the block only needs a few fields;
prefer a narrow packed payload type near the use site.

Keep reset behavior deliberate. Control/state registers should reset through
`arst_n`. Datapath storage that does not need a reset, such as FIFO memories or
pipeline payload registers, may be left unreset when the valid/control state
makes the data irrelevant.

Use `always_comb` for combinational logic and `always_ff` for sequential logic.
Give combinational outputs and next-state signals safe defaults before branching.
This keeps latch inference accidental rather than mysterious.

Assertions should document block-level contracts. For ready/valid blocks, useful
properties include valid stability under backpressure, data stability under
backpressure, no grant without request, one-hot grants, count bounds, and reset
state. Assertions intended for simulation can live under `STV_ASSERT_ON`; formal
harnesses should keep assumptions and proof-specific properties in `formal/`
unless the property is a reusable design contract.

Prefer small modules with clear ownership. A block should be easy to lint,
simulate, prove, and synthesize on its own before it becomes a dependency of a
larger block.

## Check Flow

The top-level `Makefile` is the common local and CI entry point. GitHub Actions
runs the same targets in `.github/workflows/rtl-ci.yml`.

### Lint

```sh
make lint
```

Lint runs three complementary tools:

`scripts/check_rtl_portability.py` checks project portability rules that are
important for the active RTL surface, including the ban on SystemVerilog
interfaces and `parameter type` payloads in reusable primitives.

`slang --lint-only -Weverything -Werror` checks SystemVerilog parsing,
elaboration, type correctness, constant evaluation, and a broad set of semantic
warnings.

`verible-verilog-lint` checks style rules, formatting-sensitive issues, naming
rules, and syntax patterns that are easier to enforce at source level. Project
rules live in `lint/stevia.rules.verible_lint`.

`verilator --lint-only` checks Verilator compatibility and catches simulation
and synthesis-adjacent issues such as width mismatches, unreachable code,
unsupported constructs, and accidental multi-top behavior.

### Simulation

```sh
make test
```

Simulation uses cocotb 2 with Verilator. The default test suite is currently
the tests under `test/`, which are intentionally small and fast enough for
every pull request. Current tests cover the active utility blocks across a small
set of representative widths, depths, modes, and directed/random transactions.

As the library grows, tests should be added near the RTL hierarchy they cover.
Generated simulation artifacts stay under `test/outputs/<module>/<config>/`,
so source-like test organization and run-output cleanup remain separate.

### Formal

```sh
make formal
```

Formal checks use SymbiYosys. `stv_lzc` is proved by induction against an
independent reference model for all input values at the configured width.
`stv_buffer` is checked across the supported `FLOW`, `SKID`, and
`OPT_AREA_TIMING` combinations with bounded ready/valid properties, including
ordering, capacity, fall-through behavior, and skid-buffer ready behavior.
`stv_sync_fifo` uses a similar bounded model for representative `FLOW` and
`SKID` modes, checking ordering, count/empty/full metadata, full behavior,
fall-through, and skid-ready behavior.
Formal output is written under the target directory, for example
`formal/outputs/stv_lzc/` or `formal/outputs/stv_buffer_f1_s1_oat0/`.

Formal is best used where the state space and contract are crisp: encoders,
arbiters, counters, FIFOs with bounded parameters, and ready/valid protocol
properties. Good formal harnesses should separate assumptions about the
environment from assertions about the design, use unconstrained inputs where
possible, and keep proof depths/parameters small enough for CI.

### Synthesis Smoke

```sh
make synth
```

Synthesis smoke checks use Yosys to parse and synthesize the currently supported
synthesizable utility modules into generic technology-independent logic. This
is not a timing or area signoff flow. It is a portability check that catches
unsupported syntax, accidental unsynthesizable constructs, missing dependencies,
and basic elaboration issues.

The current Yosys smoke flow covers one representative configuration for each
active utility module. It writes the generated Yosys script, log, generic
synthesized Verilog netlist, and Yosys JSON netlist under
`synth/outputs/<module>/<configuration>/`:

```sh
make synth
make synth MODULE=stv_sync_fifo
make synth CONFIG=stv_lzc_w8
less synth/outputs/stv_lzc/stv_lzc_w8/yosys.log
less synth/outputs/stv_lzc/stv_lzc_w8/stv_lzc_w8.v
less synth/outputs/stv_lzc/stv_lzc_w8/stv_lzc_w8.json
```

The generic netlist uses Yosys internal cells and Boolean assignments. It is
useful for checking that RTL can be lowered into technology-independent gates,
but it does not report real silicon area or timing. Technology-specific area
and timing require a Liberty file, FPGA family, or vendor flow.

## Tool Setup

`scripts/install_tools.sh` installs repo-local tools into `.tools/bin` and
Python dependencies into `.venv`. The script pins:

- Verible `v0.0-4053-g89d4d98a`
- slang `v11.0`
- SymbiYosys `sby` commit `f57802a16613f013e84e024df50fc3f0ea74f88b`
- Python packages from `requirements-dev.txt`

The script is used by CI and can also be used by local developers. If you source
`setup.sh`, `.tools/bin` is added to `PATH`.

On Python 3.14, cocotb 2.0.1 may require its upstream version guard override
until cocotb officially declares Python 3.14 support. The install script handles
that automatically. GitHub Actions currently uses Python 3.13 to avoid the
override.

## CI And Releases

GitHub Actions runs four jobs for pull requests and release tags:

- `lint`
- `test`
- `formal`
- `synth`

These jobs should be treated as required checks before merging a pull request.
For releases, the same checks provide a minimum quality gate for the RTL source
archive. The workflow caches `.tools` and `.venv`, but those directories are
generated artifacts and should not be committed.

## Contributing New Blocks

When adding or changing RTL:

1. Add the source file to `rtl/filelist.f`.
2. Run `make lint` and address tool findings instead of suppressing them by
   default.
3. Add or update a cocotb smoke test for externally visible behavior.
4. Add SVA assertions for local protocol and safety contracts where practical.
5. Add a formal harness when the block has a compact, provable contract.
6. Make sure the block is covered by synthesis smoke, or document why it is not.
7. Run `make all` before opening a pull request.

The preferred direction is boring, portable RTL with strong checks. Clever RTL
is welcome when it earns its keep, but the surrounding proof and test evidence
should make that clear.
