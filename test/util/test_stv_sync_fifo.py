##############################################################################
## 
## author: Stevo Bailey (stevo.bailey@gmail.com)
##
## Synchronous FIFO test
##
##############################################################################

import cocotb
from cocotb.clock import Clock
from cocotb.runner import get_runner
from cocotb.triggers import Timer
import queue
from random import randint

@cocotb.test()
async def random(dut):

    dmax = 2**int(dut.WIDTH.value)-1
    depth = int(dut.DEPTH.value)
    
    q1 = queue.Queue(depth)

    dut.rready.value = 0
    dut.wvalid.value = 0
    dut.wdata.value = 0

    # clock and reset
    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())
    dut.arst_n.value = 0
    await Timer(20, units="ns")
    dut.arst_n.value = 1
    await Timer(25, units="ns") # sync to negedge
    
    # check initial values
    assert bool(dut.empty.value) == q1.empty(), "Empty mismatch"
    assert bool(dut.full.value) == q1.full(), "Full mismatch"
    assert dut.count.value == q1.qsize(), "Count mismatch"

    cycles = 1000
    for i in range(cycles):

        # write
        wdata = randint(0, dmax)
        wvalid = randint(0, 1)
        dut.wdata.value = wdata
        dut.wvalid.value = wvalid
        if wvalid and dut.wready.value:
            q1.put(wdata)

        # read
        rready = randint(0, 1)
        dut.rready.value = rready
        if rready and dut.rvalid.value:
            golden_rdata = q1.get()
            assert dut.rdata.value == golden_rdata, f"Data mismatch on cycle {i}"

        # step
        await Timer(10, units="ns")

        # queue properties are valid after the clock tick
        assert bool(dut.empty.value) == q1.empty(), f"Empty mismatch on cycle {i}"
        assert bool(dut.full.value) == q1.full(), f"Full mismatch on cycle {i}" 
        assert dut.count.value == q1.qsize(), f"Count mismatch on cycle {i}"

    # end
    dut.wvalid.value = 0
    dut.rready.value = 0
    await Timer(100, units="ns")

def test_stv_sync_fifo():
     
    hdl_toplevel = "stv_sync_fifo"

    runner = get_runner("verilator")
    runner.build(
        hdl_toplevel=hdl_toplevel,
        build_dir="sim_build/" + hdl_toplevel,
        build_args=["-f", "$STEVIA_ROOT/rtl/filelist.f"],
        always=True,
    )

    for width in [8, 13, 32]:
        for depth in [2, 4, 16]:
            runner.test(
                hdl_toplevel=hdl_toplevel, 
                test_module="test_" + hdl_toplevel,
                hdl_toplevel_lang = "verilog",
                parameters = {"WIDTH": width, "DEPTH": depth},
                results_xml = f"results_w{width}_d{depth}.xml"
            )

if __name__ == "__main__":
    test_stv_sync_fifo()
