import os
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_tools.runner import get_runner


async def _reset(dut):
    dut.req.value = 0
    dut.lock.value = 0

    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    dut.arst_n.value = 0
    await Timer(25, unit="ns")
    dut.arst_n.value = 1
    await RisingEdge(dut.clk)
    await Timer(1, unit="ns")


@cocotb.test()
async def rotates_and_locks(dut):
    inputs = int(dut.INPUTS.value)
    await _reset(dut)

    dut.req.value = (1 << inputs) - 1
    dut.lock.value = 0

    for index in range(inputs * 2):
        await Timer(1, unit="ns")
        expected = 1 << (index % inputs)
        assert int(dut.gnt.value) == expected, (
            f"cycle={index} expected gnt=0x{expected:x}, got 0x{int(dut.gnt.value):x}"
        )
        await RisingEdge(dut.clk)

    await Timer(1, unit="ns")
    locked_gnt = int(dut.gnt.value)
    dut.lock.value = 1
    for _ in range(3):
        await RisingEdge(dut.clk)
        await Timer(1, unit="ns")
        assert int(dut.gnt.value) == locked_gnt

    dut.lock.value = 0
    dut.req.value = 0
    await Timer(1, unit="ns")
    assert int(dut.gnt.value) == 0


def test_stv_round_robin_arbiter_smoke():
    hdl_toplevel = "stv_round_robin_arbiter"
    runner = get_runner("verilator")
    repo_root = Path(__file__).resolve().parents[2]
    outputs_dir = Path(os.environ.get("STEVIA_OUTPUTS_DIR", repo_root / "test/outputs"))
    os.environ.setdefault("STEVIA_ROOT", str(repo_root))
    os.environ["PYTHONPATH"] = (
        f"{repo_root}{os.pathsep}{os.environ.get('PYTHONPATH', '')}"
    )

    for inputs in [1, 4, 7]:
        config_name = f"{hdl_toplevel}_n{inputs}"
        run_dir = outputs_dir / hdl_toplevel / config_name
        build_dir = run_dir / "sim_build"
        run_dir.mkdir(parents=True, exist_ok=True)

        runner.build(
            hdl_toplevel=hdl_toplevel,
            build_dir=build_dir,
            build_args=["-f", str(repo_root / "rtl/filelist.f")],
            parameters={"INPUTS": inputs},
            always=True,
        )

        runner.test(
            hdl_toplevel=hdl_toplevel,
            test_module="test.util.test_stv_round_robin_arbiter",
            hdl_toplevel_lang="verilog",
            build_dir=build_dir,
            test_dir=run_dir,
            results_xml=str(run_dir / "results.xml"),
            extra_env={
                "PYTHONPATH": os.environ["PYTHONPATH"],
                "STEVIA_ROOT": str(repo_root),
            },
        )
