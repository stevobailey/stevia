import os
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_tools.runner import get_runner


async def _reset(dut):
    dut.clear.value = 0
    dut.load.value = 0
    dut.din.value = 0
    dut.en.value = 0
    dut.down.value = 0
    dut.max.value = 7
    dut.min.value = 0
    dut.step.value = 3

    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    dut.arst_n.value = 0
    await Timer(25, unit="ns")
    dut.arst_n.value = 1
    await RisingEdge(dut.clk)
    await Timer(1, unit="ns")


@cocotb.test()
async def directed_step_counting(dut):
    modulo_wrap = int(dut.MODULO_WRAP.value)
    expected_up = [0, 3, 6, 1 if modulo_wrap else 0, 4 if modulo_wrap else 3]

    await _reset(dut)
    dut.en.value = 1

    for expected in expected_up:
        await Timer(1, unit="ns")
        assert int(dut.count.value) == expected
        await RisingEdge(dut.clk)

    dut.en.value = 0
    dut.load.value = 1
    dut.din.value = 1
    await RisingEdge(dut.clk)
    await Timer(1, unit="ns")
    dut.load.value = 0
    assert int(dut.count.value) == 1

    dut.en.value = 1
    dut.down.value = 1
    await Timer(1, unit="ns")
    assert int(dut.wrap.value) == 1
    await RisingEdge(dut.clk)
    await Timer(1, unit="ns")
    assert int(dut.count.value) == (6 if modulo_wrap else 7)


def test_stv_step_counter_smoke():
    hdl_toplevel = "stv_step_counter"
    runner = get_runner("verilator")
    repo_root = Path(__file__).resolve().parents[2]
    outputs_dir = Path(os.environ.get("STEVIA_OUTPUTS_DIR", repo_root / "test/outputs"))
    os.environ.setdefault("STEVIA_ROOT", str(repo_root))
    os.environ["PYTHONPATH"] = (
        f"{repo_root}{os.pathsep}{os.environ.get('PYTHONPATH', '')}"
    )

    for modulo_wrap in [0, 1]:
        config_name = f"{hdl_toplevel}_w4_m{modulo_wrap}"
        run_dir = outputs_dir / hdl_toplevel / config_name
        build_dir = run_dir / "sim_build"
        run_dir.mkdir(parents=True, exist_ok=True)

        runner.build(
            hdl_toplevel=hdl_toplevel,
            build_dir=build_dir,
            build_args=["-f", str(repo_root / "rtl/filelist.f")],
            parameters={"WIDTH": 4, "INIT_VAL": 0, "MODULO_WRAP": modulo_wrap},
            always=True,
        )

        runner.test(
            hdl_toplevel=hdl_toplevel,
            test_module="test.util.test_stv_step_counter",
            hdl_toplevel_lang="verilog",
            build_dir=build_dir,
            test_dir=run_dir,
            results_xml=str(run_dir / "results.xml"),
            extra_env={
                "PYTHONPATH": os.environ["PYTHONPATH"],
                "STEVIA_ROOT": str(repo_root),
            },
        )
