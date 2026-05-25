import os
from pathlib import Path

import cocotb
from cocotb.triggers import Timer
from cocotb_tools.runner import get_runner


def _priority_grant(req):
    return req & -req


@cocotb.test()
async def all_request_values(dut):
    inputs = int(dut.INPUTS.value)

    for req in range(1 << inputs):
        dut.req.value = req
        await Timer(1, unit="ns")

        expected = _priority_grant(req)
        assert int(dut.gnt.value) == expected, (
            f"INPUTS={inputs} req=0x{req:x} expected gnt=0x{expected:x}, "
            f"got 0x{int(dut.gnt.value):x}"
        )


def test_stv_priority_arbiter_smoke():
    hdl_toplevel = "stv_priority_arbiter"
    runner = get_runner("verilator")
    repo_root = Path(__file__).resolve().parents[2]
    outputs_dir = Path(os.environ.get("STEVIA_OUTPUTS_DIR", repo_root / "test/outputs"))
    os.environ.setdefault("STEVIA_ROOT", str(repo_root))
    os.environ["PYTHONPATH"] = (
        f"{repo_root}{os.pathsep}{os.environ.get('PYTHONPATH', '')}"
    )

    for inputs in [1, 2, 5, 8]:
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
            test_module="test.util.test_stv_priority_arbiter",
            hdl_toplevel_lang="verilog",
            build_dir=build_dir,
            test_dir=run_dir,
            results_xml=str(run_dir / "results.xml"),
            extra_env={
                "PYTHONPATH": os.environ["PYTHONPATH"],
                "STEVIA_ROOT": str(repo_root),
            },
        )
