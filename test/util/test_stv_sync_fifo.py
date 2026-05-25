import random

import cocotb
import pytest
from cocotb.triggers import Timer
from cocotb_tools.runner import get_runner

from test.common.clocking import clock_step, start_clock_and_reset
from test.common.ready_valid import ReadyValidScoreboard
from test.common.runner import output_dirs, runner_extra_env


async def _reset(dut):
    dut.clear.value = 0
    dut.din_valid.value = 0
    dut.din.value = 0
    dut.dout_ready.value = 0

    await start_clock_and_reset(dut)
    await _check_meta(dut, 0, "reset")


async def _check_meta(dut, expected_count, cycle):
    depth = int(dut.DEPTH.value)

    assert bool(dut.empty.value) == (expected_count == 0), (
        f"empty mismatch on cycle {cycle}"
    )
    assert bool(dut.full.value) == (expected_count == depth), (
        f"full mismatch on cycle {cycle}"
    )
    assert int(dut.count.value) == expected_count, f"count mismatch on cycle {cycle}"


async def _rv_step(dut, scoreboard, *, data, valid, ready, cycle):
    do_push, do_pop = await scoreboard.step(
        dut,
        data=data,
        valid=valid,
        ready=ready,
        cycle=cycle,
    )
    await _check_meta(dut, len(scoreboard), cycle)
    return do_push, do_pop


@cocotb.test()
async def directed_fill_full_and_drain(dut):
    depth = int(dut.DEPTH.value)
    skid = int(dut.SKID.value)
    scoreboard = ReadyValidScoreboard()
    await _reset(dut)

    for index in range(depth):
        await _rv_step(
            dut,
            scoreboard,
            data=0x10 + index,
            valid=1,
            ready=0,
            cycle=f"fill-{index}",
        )

    await Timer(1, unit="ns")
    assert bool(dut.full.value)
    assert not bool(dut.din_ready.value)

    dut.din.value = 0xE0
    dut.din_valid.value = 1
    dut.dout_ready.value = 1
    await Timer(1, unit="ns")
    assert bool(dut.din_ready.value) == (skid == 0)

    await _rv_step(
        dut,
        scoreboard,
        data=0xE0,
        valid=1,
        ready=1,
        cycle="full-pop-push",
    )

    while scoreboard:
        await _rv_step(
            dut,
            scoreboard,
            data=0,
            valid=0,
            ready=1,
            cycle="drain",
        )

    assert not bool(dut.dout_valid.value)


@cocotb.test()
async def directed_fallthrough_and_clear(dut):
    flow = int(dut.FLOW.value)
    scoreboard = ReadyValidScoreboard()
    await _reset(dut)

    dut.din.value = 0x5A
    dut.din_valid.value = 1
    dut.dout_ready.value = 1
    await Timer(1, unit="ns")

    if flow:
        assert bool(dut.dout_valid.value)
        assert int(dut.dout.value) == 0x5A
    else:
        assert not bool(dut.dout_valid.value)

    await _rv_step(
        dut,
        scoreboard,
        data=0x5A,
        valid=1,
        ready=1,
        cycle="fallthrough",
    )

    if not flow:
        await _rv_step(
            dut,
            scoreboard,
            data=0,
            valid=0,
            ready=1,
            cycle="drain-nonflow",
        )

    await _rv_step(
        dut,
        scoreboard,
        data=0x33,
        valid=1,
        ready=0,
        cycle="clear-fill",
    )
    assert bool(dut.dout_valid.value)

    dut.clear.value = 1
    dut.din_valid.value = 0
    dut.dout_ready.value = 0
    await clock_step(dut)
    scoreboard.clear()
    dut.clear.value = 0
    await _check_meta(dut, 0, "clear")
    assert not bool(dut.dout_valid.value)


@cocotb.test()
async def constrained_random_ready_valid(dut):
    depth = int(dut.DEPTH.value)
    flow = int(dut.FLOW.value)
    skid = int(dut.SKID.value)
    rng = random.Random((depth << 2) | (flow << 1) | skid)
    scoreboard = ReadyValidScoreboard()
    await _reset(dut)

    pending_valid = False
    pending_data = 0

    for cycle in range(500):
        if not pending_valid and rng.randrange(4) != 0:
            pending_valid = True
            pending_data = rng.randrange(256)

        do_push, _ = await _rv_step(
            dut,
            scoreboard,
            data=pending_data,
            valid=int(pending_valid),
            ready=rng.randrange(2),
            cycle=f"random-{cycle}",
        )
        if do_push:
            pending_valid = False

    while scoreboard:
        await _rv_step(
            dut,
            scoreboard,
            data=0,
            valid=0,
            ready=1,
            cycle="random-drain",
        )


@pytest.mark.parametrize("depth", [2, 3, 8], ids=["depth2", "depth3", "depth8"])
@pytest.mark.parametrize("flow", [0, 1], ids=["flow0", "flow1"])
@pytest.mark.parametrize("skid", [0, 1], ids=["skid0", "skid1"])
def test_stv_sync_fifo(depth, flow, skid):
    hdl_toplevel = "stv_sync_fifo"
    runner = get_runner("verilator")

    config_name = f"{hdl_toplevel}_d{depth}_f{flow}_s{skid}"
    repo_root, run_dir, build_dir = output_dirs(__file__, hdl_toplevel, config_name)
    extra_env = runner_extra_env(repo_root)

    runner.build(
        hdl_toplevel=hdl_toplevel,
        build_dir=build_dir,
        build_args=["-f", str(repo_root / "rtl/filelist.f")],
        parameters={
            "DEPTH": depth,
            "FLOW": flow,
            "SKID": skid,
        },
        always=True,
    )

    runner.test(
        hdl_toplevel=hdl_toplevel,
        test_module="test.util.test_stv_sync_fifo",
        hdl_toplevel_lang="verilog",
        build_dir=build_dir,
        test_dir=run_dir,
        results_xml=str(run_dir / "results.xml"),
        extra_env=extra_env,
    )
