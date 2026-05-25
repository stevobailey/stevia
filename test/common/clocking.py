import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer


async def start_clock_and_reset(
    dut,
    *,
    clock="clk",
    reset="arst_n",
    period_ns=10,
    reset_time_ns=25,
    settle_ns=1,
):
    cocotb.start_soon(Clock(getattr(dut, clock), period_ns, unit="ns").start())
    getattr(dut, reset).value = 0
    await Timer(reset_time_ns, unit="ns")
    getattr(dut, reset).value = 1
    await RisingEdge(getattr(dut, clock))
    await Timer(settle_ns, unit="ns")


async def clock_step(dut, *, clock="clk", settle_ns=1):
    await RisingEdge(getattr(dut, clock))
    await Timer(settle_ns, unit="ns")
