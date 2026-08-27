import random
from collections import deque

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge


SEED = 0x51EA2
RANDOM_CYCLES = 256
CAPACITY = 4

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


def drive_payload(dut, payload: tuple[int, ...]) -> None:
    assert len(payload) == len(INPUT_FIELDS)
    for name, value in zip(INPUT_FIELDS, payload, strict=True):
        getattr(dut, name).value = value


def read_payload(dut) -> tuple[int, ...]:
    return tuple(int(getattr(dut, name).value) for name in OUTPUT_FIELDS)


def random_payload(rng: random.Random) -> tuple[int, ...]:
    return tuple(rng.randrange(2) for _ in INPUT_FIELDS)


async def finish_cycle(clock) -> None:
    await RisingEdge(clock)
    await FallingEdge(clock)


@cocotb.test()
async def random_stream_preserves_order_and_flushes(dut) -> None:
    rng = random.Random(SEED)
    expected = deque()
    accepted_inputs = 0
    accepted_outputs = 0
    saw_input_backpressure = False
    saw_output_backpressure = False

    dut.input_valid.value = 0
    dut.output_ready.value = 0
    dut.reset.value = 1
    drive_payload(dut, (0,) * len(INPUT_FIELDS))
    cocotb.start_soon(Clock(dut.clock, 10, unit="ns").start())

    # Synchronous reset establishes the empty state at this rising edge.
    await finish_cycle(dut.clock)
    dut.reset.value = 0
    assert int(dut.output_valid.value) == 0
    assert int(dut.input_ready.value) == 1

    for _ in range(RANDOM_CYCLES):
        input_valid = rng.randrange(2)
        output_ready = rng.randrange(2)
        payload = random_payload(rng)

        dut.input_valid.value = input_valid
        dut.output_ready.value = output_ready
        drive_payload(dut, payload)
        await ReadOnly()

        input_ready = int(dut.input_ready.value)
        output_valid = int(dut.output_valid.value)
        saw_input_backpressure |= bool(input_valid and not input_ready)
        saw_output_backpressure |= bool(output_valid and not output_ready)

        if output_valid and output_ready:
            assert expected, "FIFO produced an item that was never accepted"
            assert read_payload(dut) == expected.popleft()
            accepted_outputs += 1

        if input_valid and input_ready:
            expected.append(payload)
            accepted_inputs += 1

        assert len(expected) <= CAPACITY
        await finish_cycle(dut.clock)

    # Stop producing and make downstream progress unconditional. Capacity plus
    # one observation cycle is a sufficient bound for draining this FIFO.
    dut.input_valid.value = 0
    dut.output_ready.value = 1
    for _ in range(CAPACITY + 1):
        await ReadOnly()
        if int(dut.output_valid.value):
            assert expected, "FIFO produced an item that was never accepted"
            assert read_payload(dut) == expected.popleft()
            accepted_outputs += 1
        await finish_cycle(dut.clock)

    await ReadOnly()
    assert not expected, "not all accepted inputs were flushed"
    assert accepted_outputs == accepted_inputs
    assert int(dut.output_valid.value) == 0
    assert saw_input_backpressure
    assert saw_output_backpressure
