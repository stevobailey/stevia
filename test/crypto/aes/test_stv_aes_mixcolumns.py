##############################################################################
## 
## author: Stevo Bailey (stevo.bailey@gmail.com)
##
## AES MixColumns test
##
## This test only does one set of test vectors. It assumes more thorough
## testing is done in the single column test (test_stv_aes_mixcolumn).
##############################################################################

import cocotb
from cocotb.clock import Clock
from cocotb.runner import get_runner
from cocotb.triggers import Timer
from random import randint

@cocotb.test()
async def wiki(dut):

    for i in range(4):
        dut.data_in[i].value = 0

    # test vectors from Wikipedia
    test_inputs = [
        0xdb, 0x13, 0x53, 0x45,
        0xf2, 0x0a, 0x22, 0x5c,
        0x01, 0x01, 0x01, 0x01,
        0xc6, 0xc6, 0xc6, 0xc6,
    ]
    test_outputs = [
        0x8e, 0x4d, 0xa1, 0xbc,
        0x9f, 0xdc, 0x58, 0x9d,
        0x01, 0x01, 0x01, 0x01,
        0xc6, 0xc6, 0xc6, 0xc6,
    ]

    # drive inputs
    for i in range(16):
        dut.data_in[i].value = test_inputs[i]
    dut.inverse.value = 0
    dut.bypass.value = 0

    # step
    await Timer(10, units="ns")

    # check output
    for i in range(16):
        assert int(dut.data_out[i].value) == test_outputs[i], f"Data mismatch on byte {i}"

    # drive inputs
    for i in range(16):
        dut.data_in[i].value = test_outputs[i]
    dut.inverse.value = 1
    dut.bypass.value = 0

    # step
    await Timer(10, units="ns")

    # check output
    for i in range(16):
        assert int(dut.data_out[i].value) == test_inputs[i], f"Data mismatch on byte {i}, inverse"

    # drive inputs
    for i in range(16):
        dut.data_in[i].value = test_inputs[i]
    dut.inverse.value = 0
    dut.bypass.value = 1

    # step
    await Timer(10, units="ns")

    # check output
    for i in range(16):
        assert int(dut.data_out[i].value) == test_inputs[i], f"Data mismatch on byte {i}, bypass"

    # end
    for i in range(16):
        dut.data_in[i].value = 0
    dut.inverse.value = 0
    await Timer(100, units="ns")

def test_stv_aes_mixcolumns():
     
    hdl_toplevel = "stv_aes_mixcolumns"

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
    test_stv_aes_mixcolumns()
