from collections import deque

from cocotb.triggers import Timer

from test.common.clocking import clock_step


class ReadyValidScoreboard:
    def __init__(self):
        self.expected = deque()

    async def step(
        self,
        dut,
        *,
        data,
        valid,
        ready,
        data_in="din",
        valid_in="din_valid",
        ready_in="din_ready",
        data_out="dout",
        valid_out="dout_valid",
        ready_out="dout_ready",
        cycle=None,
    ):
        getattr(dut, data_in).value = data
        getattr(dut, valid_in).value = valid
        getattr(dut, ready_out).value = ready
        await Timer(1, unit="ns")

        do_push = bool(valid and getattr(dut, ready_in).value)
        do_pop = bool(ready and getattr(dut, valid_out).value)
        was_empty = len(self.expected) == 0

        if do_pop:
            if self.expected:
                expected_data = self.expected.popleft()
            else:
                assert do_push, f"unexpected output on cycle {cycle}"
                expected_data = data
            assert int(getattr(dut, data_out).value) == expected_data, (
                f"cycle={cycle} expected {data_out}=0x{expected_data:x}, "
                f"got 0x{int(getattr(dut, data_out).value):x}"
            )

        if do_push and not (do_pop and was_empty):
            self.expected.append(data)

        await clock_step(dut)
        return do_push, do_pop

    def __bool__(self):
        return bool(self.expected)

    def __len__(self):
        return len(self.expected)

    def clear(self):
        self.expected.clear()
