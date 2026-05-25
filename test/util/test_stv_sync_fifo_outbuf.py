import os
import random
from collections import deque
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_tools.runner import get_runner


async def _reset(dut):
    dut.clear.value = 0
    dut.din_valid.value = 0
    dut.din.value = 0
    dut.dout_ready.value = 0

    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    dut.arst_n.value = 0
    await Timer(25, unit="ns")
    dut.arst_n.value = 1
    await RisingEdge(dut.clk)
    await Timer(1, unit="ns")


@cocotb.test()
async def random_ready_valid(dut):
    depth = int(dut.DEPTH.value)
    rng = random.Random(depth)
    model = deque()
    await _reset(dut)

    assert bool(dut.empty.value)
    assert not bool(dut.full.value)
    assert int(dut.count.value) == 0

    for cycle in range(500):
        din = rng.randrange(256)
        din_valid = rng.randrange(2)
        dout_ready = rng.randrange(2)

        dut.din.value = din
        dut.din_valid.value = din_valid
        dut.dout_ready.value = dout_ready
        await Timer(1, unit="ns")

        do_push = bool(din_valid and dut.din_ready.value)
        do_pop = bool(dout_ready and dut.dout_valid.value)

        if do_push:
            model.append(din)

        if do_pop:
            assert model, f"unexpected output on cycle {cycle}"
            expected = model.popleft()
            assert int(dut.dout.value) == expected, (
                f"cycle={cycle} expected dout=0x{expected:x}, got 0x{int(dut.dout.value):x}"
            )

        await RisingEdge(dut.clk)
        await Timer(1, unit="ns")

        assert bool(dut.empty.value) == (len(model) == 0), f"empty mismatch on cycle {cycle}"
        assert bool(dut.full.value) == (len(model) == depth), f"full mismatch on cycle {cycle}"
        assert int(dut.count.value) == len(model), f"count mismatch on cycle {cycle}"


def test_stv_sync_fifo_outbuf_smoke():
    hdl_toplevel = "stv_sync_fifo_outbuf"
    runner = get_runner("verilator")
    repo_root = Path(__file__).resolve().parents[2]
    outputs_dir = Path(os.environ.get("STEVIA_OUTPUTS_DIR", repo_root / "test/outputs"))
    os.environ.setdefault("STEVIA_ROOT", str(repo_root))
    os.environ["PYTHONPATH"] = (
        f"{repo_root}{os.pathsep}{os.environ.get('PYTHONPATH', '')}"
    )

    for depth in [3, 8]:
        config_name = f"{hdl_toplevel}_d{depth}"
        run_dir = outputs_dir / hdl_toplevel / config_name
        build_dir = run_dir / "sim_build"
        run_dir.mkdir(parents=True, exist_ok=True)

        runner.build(
            hdl_toplevel=hdl_toplevel,
            build_dir=build_dir,
            build_args=["-f", str(repo_root / "rtl/filelist.f")],
            parameters={"DEPTH": depth},
            always=True,
        )

        runner.test(
            hdl_toplevel=hdl_toplevel,
            test_module="test.util.test_stv_sync_fifo_outbuf",
            hdl_toplevel_lang="verilog",
            build_dir=build_dir,
            test_dir=run_dir,
            results_xml=str(run_dir / "results.xml"),
            extra_env={
                "PYTHONPATH": os.environ["PYTHONPATH"],
                "STEVIA_ROOT": str(repo_root),
            },
        )
