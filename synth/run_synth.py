#!/usr/bin/env python3
import argparse
import os
import subprocess
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class SynthConfig:
    module: str
    name: str
    parameters: tuple[tuple[str, int], ...] = ()


CONFIGS = (
    SynthConfig(
        "stv_buffer",
        "stv_buffer_w8_f0_s0",
        (("WIDTH", 8), ("FLOW", 0), ("SKID", 0), ("OPT_AREA_TIMING", 0)),
    ),
    SynthConfig("stv_counter", "stv_counter_w8", (("WIDTH", 8), ("INIT_VAL", 0))),
    SynthConfig("stv_gray_counter", "stv_gray_counter_w5", (("WIDTH", 5), ("INIT_VAL", 0))),
    SynthConfig("stv_lzc", "stv_lzc_w8", (("WIDTH", 8),)),
    SynthConfig("stv_onehot_to_bin", "stv_onehot_to_bin_w8", (("ONEHOT_WIDTH", 8),)),
    SynthConfig("stv_priority_arbiter", "stv_priority_arbiter_n8", (("INPUTS", 8),)),
    SynthConfig("stv_round_robin_arbiter", "stv_round_robin_arbiter_n8", (("INPUTS", 8),)),
    SynthConfig(
        "stv_step_counter",
        "stv_step_counter_w8_m0",
        (("WIDTH", 8), ("INIT_VAL", 0), ("MODULO_WRAP", 0)),
    ),
    SynthConfig("stv_sync_fifo", "stv_sync_fifo_w8_d8", (("WIDTH", 8), ("DEPTH", 8))),
    SynthConfig(
        "stv_sync_fifo_outbuf",
        "stv_sync_fifo_outbuf_w8_d8",
        (("WIDTH", 8), ("DEPTH", 8)),
    ),
)


def traced_sources(filelist):
    env = os.environ.copy()
    env.setdefault("STEVIA_ROOT", str(filelist.parents[1]))
    result = subprocess.run(
        ["python3", str(filelist.parents[1] / "scripts/trace_filelist.py"), str(filelist)],
        check=True,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
    )
    return [Path(line) for line in result.stdout.splitlines() if line.strip()]


def yosys_script(config, sources, run_dir):
    lines = [
        "read_verilog -sv " + " ".join(str(source) for source in sources),
    ]
    if config.parameters:
        args = " ".join(
            f"-set {name} {value}" for name, value in config.parameters
        )
        lines.append(f"chparam {args} {config.module}")
    lines.extend(
        [
            f"synth -top {config.module}",
            "check",
            f"write_json {run_dir / (config.name + '.json')}",
            f"write_verilog -noattr {run_dir / (config.name + '.v')}",
            "",
        ]
    )
    return "\n".join(lines)


def selected_configs(module, config):
    configs = CONFIGS
    if module:
        configs = tuple(item for item in configs if item.module == module)
    if config:
        configs = tuple(item for item in configs if item.name == config)
    if not configs:
        raise SystemExit("No synthesis configurations matched the requested filters")
    return configs


def main():
    parser = argparse.ArgumentParser(description="Run Yosys smoke synthesis configs")
    parser.add_argument("--module", help="only run configs for this RTL module")
    parser.add_argument("--config", help="only run this named config")
    parser.add_argument("--outputs-dir", required=True, type=Path)
    parser.add_argument(
        "--filelist",
        default=Path(os.environ.get("STEVIA_ROOT", "..")) / "rtl/filelist.f",
        type=Path,
    )
    args = parser.parse_args()

    sources = traced_sources(args.filelist.resolve())
    for config in selected_configs(args.module, args.config):
        run_dir = args.outputs_dir / config.module / config.name
        run_dir.mkdir(parents=True, exist_ok=True)
        script_path = run_dir / "run.ys"
        script_path.write_text(yosys_script(config, sources, run_dir), encoding="utf-8")
        subprocess.run(
            ["yosys", "-q", "-l", str(run_dir / "yosys.log"), str(script_path)],
            check=True,
        )


if __name__ == "__main__":
    main()
