import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge


async def clock_cycle(clock) -> None:
    await RisingEdge(clock)
    await FallingEdge(clock)


def set_address(dut, stem: str, address: int) -> None:
    getattr(dut, f"{stem}_0").value = address & 1
    getattr(dut, f"{stem}_1").value = (address >> 1) & 1


@cocotb.test()
async def reads_current_entry_and_writes_one_selected_entry(dut) -> None:
    cocotb.start_soon(Clock(dut.clock, 10, unit="ns").start())

    dut.write_enable.value = 1
    set_address(dut, "read_address", 0)

    # Initialize every entry without assuming power-up register values.
    initial = [0, 0, 0, 0]
    for address, value in enumerate(initial):
        set_address(dut, "write_address", address)
        dut.write_value.value = value
        await clock_cycle(dut.clock)

    # Raw selector bits [1, 0] name address 1 under the LSB-first convention.
    dut.write_address_0.value = 1
    dut.write_address_1.value = 0
    dut.write_value.value = 1
    await clock_cycle(dut.clock)

    expected_values = [0, 1, 0, 0]

    dut.write_enable.value = 0
    for address, expected in enumerate(expected_values):
        set_address(dut, "read_address", address)
        await FallingEdge(dut.clock)
        assert int(dut.read_value.value) == expected

    # A same-address read observes the old value before the active edge.
    set_address(dut, "read_address", 1)
    set_address(dut, "write_address", 1)
    dut.write_value.value = 0
    dut.write_enable.value = 1
    await ReadOnly()
    assert int(dut.read_value.value) == 1

    await clock_cycle(dut.clock)
    assert int(dut.read_value.value) == 0

    # Other entries retain their values.
    dut.write_enable.value = 0
    set_address(dut, "read_address", 2)
    await FallingEdge(dut.clock)
    assert int(dut.read_value.value) == 0
