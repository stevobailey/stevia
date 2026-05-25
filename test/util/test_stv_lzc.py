import os
import random
from pathlib import Path

import cocotb
from cocotb.triggers import Timer
from cocotb_tools.runner import get_runner


def _env_enabled(name):
    return os.environ.get(name, "").lower() in {"1", "true", "yes", "on"}


def _ref_lzc(value, width):
    if value == 0:
        return width
    return width - value.bit_length()


def _test_values(width):
    if width <= 8:
        return range(1 << width)

    rng = random.Random(width)
    values = {0, (1 << width) - 1}
    values.update(1 << bit for bit in range(width))
    values.update(((1 << bit) - 1) for bit in range(1, width + 1))
    values.update(rng.randrange(1 << width) for _ in range(256))
    return sorted(values)


@cocotb.test()
async def directed_and_random(dut):
    width = int(dut.WIDTH.value)

    for value in _test_values(width):
        dut.din.value = value
        await Timer(1, unit="ns")

        expected = _ref_lzc(value, width)
        actual = int(dut.count.value)
        assert actual == expected, (
            f"WIDTH={width} din=0x{value:x} expected count={expected}, got {actual}"
        )


def test_stv_lzc_smoke():
    hdl_toplevel = "stv_lzc"
    runner = get_runner("verilator")
    repo_root = Path(__file__).resolve().parents[2]
    outputs_dir = Path(os.environ.get("STEVIA_OUTPUTS_DIR", repo_root / "test/outputs"))
    test_outputs_dir = outputs_dir / hdl_toplevel
    os.environ.setdefault("STEVIA_ROOT", str(repo_root))
    os.environ["PYTHONPATH"] = (
        f"{repo_root}{os.pathsep}{os.environ.get('PYTHONPATH', '')}"
    )
    waves = _env_enabled("STEVIA_WAVES") or _env_enabled("WAVES")
    test_outputs_dir.mkdir(parents=True, exist_ok=True)

    for width in [1, 2, 3, 4, 8, 17, 32]:
        config_name = f"{hdl_toplevel}_w{width}"
        run_dir = test_outputs_dir / config_name
        build_dir = run_dir / "sim_build"
        dump_vcd = run_dir / "dump.vcd"
        named_vcd = run_dir / f"{config_name}.vcd"
        run_dir.mkdir(parents=True, exist_ok=True)
        if not waves:
            dump_vcd.unlink(missing_ok=True)
            named_vcd.unlink(missing_ok=True)

        runner.build(
            hdl_toplevel=hdl_toplevel,
            build_dir=build_dir,
            build_args=["-f", str(repo_root / "rtl/filelist.f")],
            parameters={"WIDTH": width},
            always=True,
            waves=waves,
        )

        runner.test(
            hdl_toplevel=hdl_toplevel,
            test_module="test.util.test_stv_lzc",
            hdl_toplevel_lang="verilog",
            build_dir=build_dir,
            test_dir=run_dir,
            results_xml=str(run_dir / "results.xml"),
            waves=waves,
            extra_env={
                "PYTHONPATH": os.environ["PYTHONPATH"],
                "STEVIA_ROOT": str(repo_root),
            },
        )

        if dump_vcd.exists():
            dump_vcd.replace(named_vcd)
