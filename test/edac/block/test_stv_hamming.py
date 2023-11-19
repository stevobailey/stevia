##############################################################################
## 
## author: Stevo Bailey (stevo.bailey@gmail.com)
##
## Hamming code generator and checker test
##
##############################################################################

import cocotb
from cocotb.clock import Clock
from cocotb.runner import get_runner
from cocotb.triggers import Timer
from random import randint

def is_pow2(x):
    return (x and (not(x & (x - 1))) )

def get_parity(data_width, parity_width, data):
    parity = (2**parity_width)-1
    for p in range(parity_width):
        p_bit = 1 << p
        d = 0
        for c in range(parity_width + data_width):
            c1 = c+1
            if not is_pow2(c1):
                if (p_bit & c1):
                    parity ^= ((data >> d) & 1) << p
                d += 1
    return parity 

def get_syndrome(data_width, parity_width, error):
    if error < data_width:
        c = 0
        d = -1
        for c in range(parity_width + data_width):
            c1 = c+1
            if not is_pow2(c1):
                d += 1
            if d == error:
                return c1 
    elif error < data_width + parity_width:
        c = 0
        p = -1
        for c in range(parity_width + data_width):
            c1 = c+1
            if is_pow2(c1):
                p += 1
            if p == (error - data_width):
                return c1 
    return 0

@cocotb.test()
async def random(dut):

    data_width = int(dut.WIDTH.value)
    data_max = (2**data_width)-1
    parity_width = int(dut.PWIDTH.value)
    parity_max = (2**parity_width)-1
    
    dut.data_in.value = 0
    dut.parity_in.value = 0

    cycles = 1000
    for i in range(cycles):

        # inputs
        data_in = randint(0, data_max)
        parity_in = get_parity(data_width, parity_width, data_in)
        # inject error
        error = randint(0, data_width+parity_width)
        if error < data_width:
            data_in ^= (1 << error)
        elif error < (data_width+parity_width):
            parity_in ^= (1 << (error-data_width))
        dut.data_in.value = data_in
        dut.parity_in.value = parity_in

        # step
        await Timer(10, units="ns")

        # outputs
        parity_out = get_parity(data_width, parity_width, data_in)
        assert int(dut.parity_out.value) == parity_out, f"Parity out mismatch on cycle {i}"
        syndrome = 0
        if error < (data_width+parity_width):
            syndrome = get_syndrome(data_width, parity_width, error)
        assert int(dut.syndrome.value) == syndrome, f"Syndrome mismatch on cycle {i}"

    # end
    await Timer(10, units="ns")

def test_stv_hamming():
     
    hdl_toplevel = "stv_hamming"

    runner = get_runner("verilator")
    runner.build(
        hdl_toplevel=hdl_toplevel,
        build_dir="sim_build/" + hdl_toplevel,
        build_args=["-f", "$STEVIA_ROOT/rtl/filelist.f"],
        always=True,
    )

    runner.test(
        hdl_toplevel=hdl_toplevel, 
        test_module="test_" + hdl_toplevel,
        hdl_toplevel_lang = "verilog"
    )

if __name__ == "__main__":
    test_stv_hamming()
