import os
import random
from collections import deque
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_tools.runner import get_runner


@cocotb.test()
async def random_ready_valid(dut):
    depth = int(dut.DEPTH.value)
    model = deque()

    dut.clear.value = 0
    dut.din_valid.value = 0
    dut.din.value = 0
    dut.dout_ready.value = 0

    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())

    dut.arst_n.value = 0
    await Timer(25, unit="ns")
    dut.arst_n.value = 1
    await RisingEdge(dut.clk)

    assert bool(dut.empty.value)
    assert not bool(dut.full.value)
    assert int(dut.count.value) == 0

    for cycle in range(500):
        din = random.randrange(256)
        din_valid = random.randrange(2)
        dout_ready = random.randrange(2)

        dut.din.value = din
        dut.din_valid.value = din_valid
        dut.dout_ready.value = dout_ready
        await Timer(1, unit="ns")

        do_push = bool(din_valid and dut.din_ready.value)
        do_pop = bool(dout_ready and dut.dout_valid.value)
        was_empty = len(model) == 0

        if do_pop and not was_empty:
            expected_dout = model.popleft()
            assert int(dut.dout.value) == expected_dout, f"dout mismatch on cycle {cycle}"

        if do_push:
            model.append(din)

        await RisingEdge(dut.clk)
        await Timer(1, unit="ns")

        assert bool(dut.empty.value) == (len(model) == 0), f"empty mismatch on cycle {cycle}"
        assert bool(dut.full.value) == (len(model) == depth), f"full mismatch on cycle {cycle}"
        assert int(dut.count.value) == len(model), f"count mismatch on cycle {cycle}"


def test_stv_sync_fifo_smoke():
    hdl_toplevel = "stv_sync_fifo"
    runner = get_runner("verilator")
    repo_root = Path(__file__).resolve().parents[2]
    os.environ.setdefault("STEVIA_ROOT", str(repo_root))
    os.environ["PYTHONPATH"] = (
        f"{repo_root}{os.pathsep}{os.environ.get('PYTHONPATH', '')}"
    )

    for depth in [2, 3, 8]:
        build_dir = repo_root / f"sim_build/{hdl_toplevel}_d{depth}"

        runner.build(
            hdl_toplevel=hdl_toplevel,
            build_dir=build_dir,
            build_args=["-f", str(repo_root / "rtl/filelist.f")],
            parameters={"DEPTH": depth},
            always=True,
        )

        runner.test(
            hdl_toplevel=hdl_toplevel,
            test_module="test.smoke.test_stv_sync_fifo",
            hdl_toplevel_lang="verilog",
            build_dir=build_dir,
            results_xml=str(repo_root / f"results_stv_sync_fifo_d{depth}.xml"),
        )
