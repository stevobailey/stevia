##############################################################################
## 
## author: Stevo Bailey (stevo.bailey@gmail.com)
##
## AES ShiftRows test
##
##############################################################################

import cocotb
from cocotb.clock import Clock
from cocotb.runner import get_runner
from cocotb.triggers import Timer
from random import randint

def get_row_col(i):
    return (i%4, i//4)

def get_idx(row, col):
    return col*4+row

@cocotb.test()
async def forward(dut):

    for i in range(16):
        dut.data_in[i].value = 0

    cycles = 1000 
    for i in range(cycles):

        # drive inputs
        data_in = []
        for j in range(16):
            data_in.append(randint(0, 255))
            dut.data_in[j].value = data_in[j]
        dut.inverse.value = 0

        # step
        await Timer(10, units="ns")

        # calculated expected output
        data_out = [0]*16
        for j in range(16):
            row, col = get_row_col(j)
            in_row = row
            shift = row
            in_col = (col + shift)%4
            data_out[get_idx(row, col)] = data_in[get_idx(in_row, in_col)]
            
        # check output
        for j in range(16):
            assert int(dut.data_out[j].value) == data_out[j], f"Data mismatch on cycle {i}, byte {j}"

    # end
    for i in range(16):
        dut.data_in[i].value = 0
    await Timer(100, units="ns")

@cocotb.test()
async def inverse(dut):

    for i in range(16):
        dut.data_in[i].value = 0

    cycles = 1000 
    for i in range(cycles):

        # drive inputs
        data_in = []
        for j in range(16):
            data_in.append(randint(0, 255))
            dut.data_in[j].value = data_in[j]
        dut.inverse.value = 1

        # step
        await Timer(10, units="ns")

        # calculated expected output
        data_out = [0]*16
        for j in range(16):
            row, col = get_row_col(j)
            in_row = row
            shift = -1*row
            in_col = (col + shift)%4
            data_out[get_idx(row, col)] = data_in[get_idx(in_row, in_col)]
            
        # check output
        for j in range(16):
            assert int(dut.data_out[j].value) == data_out[j], f"Data mismatch on cycle {i}, byte {j}"

    # end
    for i in range(16):
        dut.data_in[i].value = 0
    dut.inverse.value = 0
    await Timer(100, units="ns")


def test_stv_aes_shiftrows():
     
    hdl_toplevel = "stv_aes_shiftrows"

    runner = get_runner("verilator")
    runner.build(
        hdl_toplevel=hdl_toplevel,
        build_dir="sim_build/" + hdl_toplevel,
        build_args=["-f", "$STEVIA_ROOT/rtl/filelist.f", "--trace-fst"],
        always=True,
    )

    runner.test(
        hdl_toplevel=hdl_toplevel, 
        test_module="test_" + hdl_toplevel,
        hdl_toplevel_lang = "verilog"
    )

if __name__ == "__main__":
    test_stv_aes_shiftrows()
