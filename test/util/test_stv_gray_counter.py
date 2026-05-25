import os
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_tools.runner import get_runner


def _gray(value):
    return value ^ (value >> 1)


async def _reset(dut):
    dut.clear.value = 0
    dut.load.value = 0
    dut.din.value = 0
    dut.en.value = 0
    dut.down.value = 0

    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    dut.arst_n.value = 0
    await Timer(25, unit="ns")
    dut.arst_n.value = 1
    await RisingEdge(dut.clk)
    await Timer(1, unit="ns")


@cocotb.test()
async def directed_gray_sequence(dut):
    width = int(dut.WIDTH.value)
    await _reset(dut)

    dut.en.value = 1
    dut.down.value = 0
    for binary in range(8):
        await Timer(1, unit="ns")
        assert int(dut.count.value) == _gray(binary)
        assert int(dut.wrap.value) == int(binary == (1 << width) - 1)
        await RisingEdge(dut.clk)

    dut.en.value = 0
    dut.load.value = 1
    dut.din.value = _gray(1)
    await RisingEdge(dut.clk)
    await Timer(1, unit="ns")
    dut.load.value = 0
    assert int(dut.count.value) == _gray(1)

    dut.en.value = 1
    dut.down.value = 1
    await RisingEdge(dut.clk)
    await Timer(1, unit="ns")
    assert int(dut.count.value) == _gray(0)
    assert int(dut.wrap.value) == 1
    await RisingEdge(dut.clk)
    await Timer(1, unit="ns")
    assert int(dut.count.value) == _gray((1 << width) - 1)


def test_stv_gray_counter_smoke():
    hdl_toplevel = "stv_gray_counter"
    runner = get_runner("verilator")
    repo_root = Path(__file__).resolve().parents[2]
    outputs_dir = Path(os.environ.get("STEVIA_OUTPUTS_DIR", repo_root / "test/outputs"))
    os.environ.setdefault("STEVIA_ROOT", str(repo_root))
    os.environ["PYTHONPATH"] = (
        f"{repo_root}{os.pathsep}{os.environ.get('PYTHONPATH', '')}"
    )

    config_name = f"{hdl_toplevel}_w4"
    run_dir = outputs_dir / hdl_toplevel / config_name
    build_dir = run_dir / "sim_build"
    run_dir.mkdir(parents=True, exist_ok=True)

    runner.build(
        hdl_toplevel=hdl_toplevel,
        build_dir=build_dir,
        build_args=["-f", str(repo_root / "rtl/filelist.f")],
        parameters={"WIDTH": 4, "INIT_VAL": 0},
        always=True,
    )

    runner.test(
        hdl_toplevel=hdl_toplevel,
        test_module="test.util.test_stv_gray_counter",
        hdl_toplevel_lang="verilog",
        build_dir=build_dir,
        test_dir=run_dir,
        results_xml=str(run_dir / "results.xml"),
        extra_env={
            "PYTHONPATH": os.environ["PYTHONPATH"],
            "STEVIA_ROOT": str(repo_root),
        },
    )
