import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_tools.runner import get_runner

from test.common.clocking import start_clock_and_reset
from test.common.ready_valid import ReadyValidScoreboard
from test.common.runner import output_dirs, runner_extra_env


async def _reset(dut):
    dut.clear.value = 0
    dut.din_valid.value = 0
    dut.din.value = 0
    dut.dout_ready.value = 0

    await start_clock_and_reset(dut)


@cocotb.test()
async def directed_single_transfer(dut):
    flow = int(dut.FLOW.value)
    scoreboard = ReadyValidScoreboard()
    await _reset(dut)

    assert not bool(dut.dout_valid.value)
    assert bool(dut.din_ready.value)

    dut.din.value = 0x5A
    dut.din_valid.value = 1
    dut.dout_ready.value = 1
    await Timer(1, unit="ns")

    if flow:
        assert bool(dut.dout_valid.value)
        assert int(dut.dout.value) == 0x5A
    else:
        assert not bool(dut.dout_valid.value)

    await scoreboard.step(dut, data=0x5A, valid=1, ready=1, cycle="single-transfer")
    if not flow:
        await scoreboard.step(dut, data=0, valid=0, ready=1, cycle="single-transfer-drain")
    assert not scoreboard


@cocotb.test()
async def directed_backpressure_and_clear(dut):
    scoreboard = ReadyValidScoreboard()
    await _reset(dut)

    await scoreboard.step(dut, data=0x11, valid=1, ready=0, cycle="fill")
    for cycle in range(3):
        await Timer(1, unit="ns")
        assert bool(dut.dout_valid.value)
        assert int(dut.dout.value) == 0x11
        await scoreboard.step(
            dut,
            data=0x22 + cycle,
            valid=1,
            ready=0,
            cycle=f"backpressure-{cycle}",
        )

    await scoreboard.step(dut, data=0x44, valid=1, ready=1, cycle="release")

    dut.clear.value = 1
    dut.din_valid.value = 0
    dut.dout_ready.value = 0
    await RisingEdge(dut.clk)
    await Timer(1, unit="ns")
    assert not bool(dut.dout_valid.value)
    dut.clear.value = 0


@cocotb.test()
async def constrained_random_ready_valid(dut):
    rng = random.Random(
        (int(dut.FLOW.value) << 2)
        | (int(dut.SKID.value) << 1)
        | int(dut.OPT_AREA_TIMING.value)
    )
    scoreboard = ReadyValidScoreboard()
    await _reset(dut)

    pending_valid = False
    pending_data = 0

    for cycle in range(400):
        if not pending_valid and rng.randrange(4) != 0:
            pending_valid = True
            pending_data = rng.randrange(256)

        dout_ready = rng.randrange(2)
        do_push, _ = await scoreboard.step(
            dut,
            data=pending_data,
            valid=int(pending_valid),
            ready=dout_ready,
            cycle=f"random-{cycle}",
        )
        if do_push:
            pending_valid = False

    pending_valid = False
    dut.din_valid.value = 0
    for _ in range(8):
        await scoreboard.step(
            dut,
            data=pending_data,
            valid=int(pending_valid),
            ready=1,
            cycle="drain",
        )


@pytest.mark.parametrize("flow", [0, 1], ids=["flow0", "flow1"])
@pytest.mark.parametrize("skid", [0, 1], ids=["skid0", "skid1"])
@pytest.mark.parametrize("opt_area_timing", [0, 1], ids=["area_timing0", "area_timing1"])
def test_stv_buffer(flow, skid, opt_area_timing):
    hdl_toplevel = "stv_buffer"
    runner = get_runner("verilator")

    config_name = f"{hdl_toplevel}_f{flow}_s{skid}_oat{opt_area_timing}"
    repo_root, run_dir, build_dir = output_dirs(__file__, hdl_toplevel, config_name)
    extra_env = runner_extra_env(repo_root)

    runner.build(
        hdl_toplevel=hdl_toplevel,
        build_dir=build_dir,
        build_args=["-f", str(repo_root / "rtl/filelist.f")],
        parameters={
            "FLOW": flow,
            "SKID": skid,
            "OPT_AREA_TIMING": opt_area_timing,
        },
        always=True,
    )

    runner.test(
        hdl_toplevel=hdl_toplevel,
        test_module="test.util.test_stv_buffer",
        hdl_toplevel_lang="verilog",
        build_dir=build_dir,
        test_dir=run_dir,
        results_xml=str(run_dir / "results.xml"),
        extra_env=extra_env,
    )
