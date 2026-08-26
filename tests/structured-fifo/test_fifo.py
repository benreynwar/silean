import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge


INPUT_FIELDS = (
    "input_data_a_0",
    "input_data_a_1",
    "input_data_a_2",
    "input_data_b_c",
    "input_data_b_d_0_e",
    "input_data_b_d_0_f",
    "input_data_b_d_1_e",
    "input_data_b_d_1_f",
)

OUTPUT_FIELDS = tuple(name.replace("input_", "output_", 1) for name in INPUT_FIELDS)


async def next_drive_phase(clock) -> None:
    await RisingEdge(clock)
    await FallingEdge(clock)


def drive_payload(dut, values: tuple[int, ...]) -> None:
    assert len(values) == len(INPUT_FIELDS)
    for name, value in zip(INPUT_FIELDS, values, strict=True):
        getattr(dut, name).value = value


def read_payload(dut) -> tuple[int, ...]:
    return tuple(int(getattr(dut, name).value) for name in OUTPUT_FIELDS)


@cocotb.test()
async def stores_structured_payload_with_backpressure(dut) -> None:
    empty = (0, 0, 0, 0, 0, 0, 0, 0)
    first = (1, 0, 1, 1, 0, 1, 1, 0)
    ignored = (0, 1, 0, 0, 1, 0, 0, 1)
    replacement = (1, 1, 0, 1, 1, 1, 0, 0)

    dut.input_valid.value = 0
    dut.output_ready.value = 1
    drive_payload(dut, empty)
    cocotb.start_soon(Clock(dut.clock, 10, unit="ns").start())

    # Force the FIFO empty without assuming anything about register power-up.
    await next_drive_phase(dut.clock)
    assert dut.output_valid.value == 0
    assert dut.input_ready.value == 1

    # Capture a complete structured payload while the consumer is blocked.
    dut.input_valid.value = 1
    dut.output_ready.value = 0
    drive_payload(dut, first)
    await next_drive_phase(dut.clock)
    assert dut.output_valid.value == 1
    assert dut.input_ready.value == 0
    assert read_payload(dut) == first

    # Backpressure holds every payload field and ignores the input bus.
    dut.input_valid.value = 0
    drive_payload(dut, ignored)
    await next_drive_phase(dut.clock)
    assert dut.output_valid.value == 1
    assert read_payload(dut) == first

    # A simultaneous dequeue/enqueue replaces the stored payload atomically.
    dut.input_valid.value = 1
    dut.output_ready.value = 1
    drive_payload(dut, replacement)
    await next_drive_phase(dut.clock)
    assert dut.output_valid.value == 1
    assert dut.input_ready.value == 1
    assert read_payload(dut) == replacement

    # Dequeue without replacement leaves the FIFO empty.
    dut.input_valid.value = 0
    await next_drive_phase(dut.clock)
    assert dut.output_valid.value == 0
    assert dut.input_ready.value == 1
