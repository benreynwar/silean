import cocotb
from cocotb.clock import Clock
from utils import next_drive_phase


@cocotb.test()
async def captures_input_only_on_rising_edges(dut) -> None:
    data_in = getattr(dut, "in")

    data_in.value = 0
    cocotb.start_soon(Clock(dut.clock, 10, unit="ns").start())

    # Establish a known state without assuming the register's initial value.
    await next_drive_phase(dut.clock)
    assert dut.out.value == 0

    for value in [1, 0, 1, 1, 0]:
        previous = int(dut.out.value)
        data_in.value = value
        assert int(dut.out.value) == previous

        await next_drive_phase(dut.clock)
        assert int(dut.out.value) == value
