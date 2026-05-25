import os
from pathlib import Path

import cocotb
from cocotb.triggers import Timer
from cocotb_tools.runner import get_runner


@cocotb.test()
async def onehot0_values(dut):
    width = int(dut.ONEHOT_WIDTH.value)

    for index in [None, *range(width)]:
        value = 0 if index is None else 1 << index
        expected = 0 if index is None else index

        dut.onehot.value = value
        await Timer(1, unit="ns")

        assert int(dut.bin.value) == expected, (
            f"ONEHOT_WIDTH={width} onehot=0x{value:x} expected bin={expected}, "
            f"got {int(dut.bin.value)}"
        )


def test_stv_onehot_to_bin_smoke():
    hdl_toplevel = "stv_onehot_to_bin"
    runner = get_runner("verilator")
    repo_root = Path(__file__).resolve().parents[2]
    outputs_dir = Path(os.environ.get("STEVIA_OUTPUTS_DIR", repo_root / "test/outputs"))
    os.environ.setdefault("STEVIA_ROOT", str(repo_root))
    os.environ["PYTHONPATH"] = (
        f"{repo_root}{os.pathsep}{os.environ.get('PYTHONPATH', '')}"
    )

    for width in [1, 2, 3, 4, 8, 13]:
        config_name = f"{hdl_toplevel}_w{width}"
        run_dir = outputs_dir / hdl_toplevel / config_name
        build_dir = run_dir / "sim_build"
        run_dir.mkdir(parents=True, exist_ok=True)

        runner.build(
            hdl_toplevel=hdl_toplevel,
            build_dir=build_dir,
            build_args=["-f", str(repo_root / "rtl/filelist.f")],
            parameters={"ONEHOT_WIDTH": width},
            always=True,
        )

        runner.test(
            hdl_toplevel=hdl_toplevel,
            test_module="test.util.test_stv_onehot_to_bin",
            hdl_toplevel_lang="verilog",
            build_dir=build_dir,
            test_dir=run_dir,
            results_xml=str(run_dir / "results.xml"),
            extra_env={
                "PYTHONPATH": os.environ["PYTHONPATH"],
                "STEVIA_ROOT": str(repo_root),
            },
        )
