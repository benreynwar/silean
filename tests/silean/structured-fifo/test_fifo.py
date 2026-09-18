import random
from collections import deque

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ReadOnly
from utils import drive_payload, next_drive_phase, random_payload, read_payload


SEED = 0x51EA1
RANDOM_CYCLES = 256
CAPACITY = 1

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


@cocotb.test()
async def random_stream_preserves_order_and_flushes(dut) -> None:
    rng = random.Random(SEED)
    expected = deque()
    accepted_payloads = []
    produced_payloads = []
    saw_input_backpressure = False
    saw_output_backpressure = False

    dut.input_valid.value = 0
    dut.output_ready.value = 0
    dut.reset.value = 1
    drive_payload(dut, INPUT_FIELDS, (0,) * len(INPUT_FIELDS))
    cocotb.start_soon(Clock(dut.clock, 10, unit="ns").start())

    # Synchronous reset establishes the empty state at this rising edge.
    await next_drive_phase(dut.clock)
    dut.reset.value = 0
    assert int(dut.output_valid.value) == 0
    assert int(dut.input_ready.value) == 1

    for _ in range(RANDOM_CYCLES):
        input_valid = rng.randrange(2)
        output_ready = rng.randrange(2)
        payload = random_payload(rng, INPUT_FIELDS)

        dut.input_valid.value = input_valid
        dut.output_ready.value = output_ready
        drive_payload(dut, INPUT_FIELDS, payload)
        await ReadOnly()

        input_ready = int(dut.input_ready.value)
        output_valid = int(dut.output_valid.value)
        saw_input_backpressure |= bool(input_valid and not input_ready)
        saw_output_backpressure |= bool(output_valid and not output_ready)

        # This FIFO is combinationally fall-through. When it is empty, a newly
        # accepted input may also be produced in this same cycle, so enqueue it
        # in the reference model before checking the output transfer.
        if input_valid and input_ready:
            expected.append(payload)
            accepted_payloads.append(payload)

        if output_valid and output_ready:
            assert expected, "FIFO produced an item that was never accepted"
            produced = read_payload(dut, OUTPUT_FIELDS)
            assert produced == expected.popleft()
            produced_payloads.append(produced)

        assert len(expected) <= CAPACITY
        await next_drive_phase(dut.clock)

    # Stop producing and hold ready high for the FIFO capacity. Every queued
    # payload must be transferred during this drain interval.
    dut.input_valid.value = 0
    dut.output_ready.value = 1
    for _ in range(CAPACITY):
        await ReadOnly()
        if int(dut.output_valid.value):
            assert expected, "FIFO produced an item that was never accepted"
            produced = read_payload(dut, OUTPUT_FIELDS)
            assert produced == expected.popleft()
            produced_payloads.append(produced)
        await next_drive_phase(dut.clock)

    await ReadOnly()
    assert not expected, "not all accepted inputs were flushed"
    assert produced_payloads == accepted_payloads
    assert int(dut.output_valid.value) == 0
    assert saw_input_backpressure
    assert saw_output_backpressure
