##############################################################################
## 
## author: Stevo Bailey (stevo.bailey@gmail.com)
##
## AES AddRoundKey test
##
##############################################################################

import cocotb
from cocotb.clock import Clock
from cocotb.runner import get_runner
from cocotb.triggers import Timer
from random import randint

@cocotb.test()
async def addroundkey(dut):

    for i in range(16):
        dut.data_in[i].value = 0
        dut.key_in[i].value = 0

    cycles = 1000 
    for i in range(cycles):

        # drive inputs
        data_in = []
        key_in = []
        for j in range(16):
            data_in.append(randint(0, 255))
            dut.data_in[j].value = data_in[j]
            key_in.append(randint(0, 255))
            dut.key_in[j].value = key_in[j]

        # step
        await Timer(10, units="ns")

        # check output
        for j in range(16):
            data_out = data_in[j] ^ key_in[j]
            assert int(dut.data_out[j].value) == data_out, f"Data mismatch on cycle {i}, byte {j}"

    # end
    for i in range(16):
        dut.data_in[i].value = 0
        dut.key_in[i].value = 0
    await Timer(100, units="ns")

def test_stv_aes_addroundkey():
     
    hdl_toplevel = "stv_aes_addroundkey"

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
    test_stv_aes_addroundkey()
