##############################################################################
## 
## author: Stevo Bailey (stevo.bailey@gmail.com)
##
## Skid buffer test
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
    
    q1 = queue.Queue(2)

    dut.valid_in.value = 0
    dut.ready_in.value = 0
    dut.data_in.value = 0

    # clock and reset
    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())
    dut.arst_n.value = 0
    await Timer(20, units="ns")
    dut.arst_n.value = 1
    await Timer(25, units="ns") # sync to negedge
    
    cycles = 1000
    for i in range(cycles):

        # randomize inputs
        data_in = randint(0, dmax)
        valid_in = randint(0, 1)
        ready_in = randint(0, 1)

        # drive inputs
        dut.data_in.value = data_in
        dut.valid_in.value = valid_in
        dut.ready_in.value = ready_in

        # initiator
        if valid_in and dut.ready_out.value:
            q1.put(data_in)

        # target
        if ready_in and dut.valid_out.value:
            exp_data = q1.get()
            assert dut.data_out.value == exp_data, f"Data mismatch on cycle {i}"

        # step
        await Timer(10, units="ns")

    # end
    dut.valid_in.value = 0
    dut.ready_in.value = 0
    await Timer(100, units="ns")

@cocotb.test()
async def max(dut):

    dmax = 255
    
    q1 = queue.Queue(2)

    dut.valid_in.value = 0
    dut.ready_in.value = 0
    dut.data_in.value = 0

    # clock and reset
    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())
    dut.arst_n.value = 0
    await Timer(20, units="ns")
    dut.arst_n.value = 1
    await Timer(25, units="ns") # sync to negedge
    
    cycles = 1000
    for i in range(cycles):

        # randomize inputs
        data_in = randint(0, dmax)
        valid_in = 1
        ready_in = 1

        # drive inputs
        dut.data_in.value = data_in
        dut.valid_in.value = valid_in
        dut.ready_in.value = ready_in

        # initiator
        if valid_in and dut.ready_out.value:
            q1.put(data_in)

        # target
        if ready_in and dut.valid_out.value:
            exp_data = q1.get()
            assert dut.data_out.value == exp_data, f"Data mismatch on cycle {i}"

        assert (i == 0) or (dut.valid_out.value == 1), "Valid out is not max throughput"
        assert dut.ready_out.value == 1, "Ready out is not max throughput"

        # step
        await Timer(10, units="ns")

    # end
    dut.valid_in.value = 0
    dut.ready_in.value = 0
    await Timer(100, units="ns")

def test_stv_skid_buffer():
     
    hdl_toplevel = "stv_skid_buffer"

    runner = get_runner("verilator")
    runner.build(
        hdl_toplevel=hdl_toplevel,
        build_dir="sim_build/" + hdl_toplevel,
        build_args=["-f", "$STEVIA_ROOT/rtl/filelist.f"],
        always=True,
    )

    for width in [3, 13, 32]:
        runner.test(
            hdl_toplevel=hdl_toplevel, 
            test_module="test_" + hdl_toplevel,
            hdl_toplevel_lang = "verilog",
            parameters = {"WIDTH": width},
            results_xml = f"results_w{width}.xml"
        )

if __name__ == "__main__":
    test_stv_skid_buffer()
