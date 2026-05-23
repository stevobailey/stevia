##############################################################################
## 
## author: Stevo Bailey (stevo.bailey@gmail.com)
##
## AES data generator test
##
##############################################################################

import cocotb
from cocotb.clock import Clock
from cocotb.runner import get_runner
from cocotb.triggers import Timer
from random import randint

# https://medium.com/wearesinch/building-aes-128-from-the-ground-up-with-python-8122af44ebf9
def expand_key(key, rounds):

    rcon = [[1, 0, 0, 0]]

    for _ in range(1, rounds):
        rcon.append([rcon[-1][0]*2, 0, 0, 0])
        if rcon[-1][0] > 0x80:
            rcon[-1][0] ^= 0x11b

    key_grid = break_in_grids_of_16(key)[0]

    for round in range(rounds):
        last_column = [row[-1] for row in key_grid]
        last_column_rotate_step = rotate_row_left(last_column)
        last_column_sbox_step = [lookup(b) for b in last_column_rotate_step]
        last_column_rcon_step = [last_column_sbox_step[i]
                                 ^ rcon[round][i] for i in range(len(last_column_rotate_step))]

        for r in range(4):
            key_grid[r] += bytes([last_column_rcon_step[r]
                                  ^ key_grid[r][round*4]])

        # Three more columns to go
        for i in range(len(key_grid)):
            for j in range(1, 4):
                key_grid[i] += bytes([key_grid[i][round*4+j]
                                      ^ key_grid[i][round*4+j+3]])

    return key_grid

@cocotb.test()
async def forward(dut):

    # initialize inputs
    dut.keylen.value = 0
    dut.inverse.value = 0
    dut.data_valid_in.value = 0
    dut.key_valid_in.value = 0
    dut.data_ready_in.value = 0
    for i in range(16):
        dut.data_in[i].value = 0
        dut.key_in[i].value = 0

    # clock and reset
    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())
    dut.arst_n.value = 0
    await Timer(20, units="ns")
    dut.arst_n.value = 1
    await Timer(25, units="ns") # sync to negedge

    cycles = 1000 
    for i in range(cycles):
        pass


def test_stv_aes_datagen():
     
    hdl_toplevel = "stv_aes_datagen"

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
    test_stv_aes_datagen()

