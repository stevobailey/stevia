##############################################################################
##
## author: Stevo Bailey (stevo.bailey@gmail.com)
##
## Parity generator and checker test
##
##############################################################################

import cocotb
from cocotb.clock import Clock
from cocotb.runner import get_runner
from cocotb.triggers import Timer
from random import randint

def get_parity(n):
    parity = 0
    while n:
        if (n&1):
            parity ^= 1
        n >>= 1
    return parity

@cocotb.test()
async def all(dut):

    data_max = 2**int(dut.WIDTH.value)-1
    
    dut.even.value = 0
    dut.data_in.value = 0
    dut.parity_in.value = 0

    cycles = 1000
    for i in range(cycles):

        # inputs
        even = randint(0, 1)
        data_in = randint(0, data_max)
        parity_in = randint(0, 1)
        dut.even.value = even
        dut.data_in.value = data_in
        dut.parity_in.value = parity_in

        # step
        await Timer(10, units="ns")

        # outputs
        parity_out = even ^ get_parity(data_in)
        assert dut.parity_out.value == parity_out, f"Parity out mismatch on cycle {i}"
        parity_good = parity_in == parity_out
        assert dut.parity_good.value == parity_good, f"Parity good mismatch on cycle {i}"

    # end
    await Timer(10, units="ns")

def test_stv_parity():
     
    hdl_toplevel = "stv_parity"

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
    test_stv_parity()
