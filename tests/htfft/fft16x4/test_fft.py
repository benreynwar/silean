import cmath
import math
import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge


FFT_SIZE = 16
LANES = 4
FRAME_LENGTH = FFT_SIZE // LANES
INPUT_WIDTH = 12
OUTPUT_WIDTH = INPUT_WIDTH + 4
FRACTIONAL_BITS = 8
LATENCY = 33
FRAME_COUNT = 24

# Coarse certified bounds for Q2.8 generated twiddles and the three Q8
# arithmetic rounding sites in each butterfly layer.
TWIDDLE_ERROR_BOUND = math.sqrt(2) / 128
ARITHMETIC_ERROR_BOUND = 3 * math.sqrt(2) / 256


def decoded_capacity(width: int) -> float:
    return ((1 << (width - 1)) - 1) / (1 << FRACTIONAL_BITS)


def safe_input_magnitude() -> float:
    """Conservative specialization of Configuration.safeInputMagnitude."""
    budget = decoded_capacity(OUTPUT_WIDTH)
    quantum = 1 / (1 << FRACTIONAL_BITS)
    for stage in reversed(range(FFT_SIZE.bit_length() - 1)):
        data_capacity = decoded_capacity(INPUT_WIDTH + stage)
        output_capacity = decoded_capacity(INPUT_WIDTH + stage + 1)
        budget = min(
            data_capacity,
            (data_capacity - quantum) / (1 + TWIDDLE_ERROR_BOUND),
            (output_capacity - quantum) / (2 + TWIDDLE_ERROR_BOUND),
            (budget - ARITHMETIC_ERROR_BOUND) /
                (2 + TWIDDLE_ERROR_BOUND),
        )
    return budget


SAFE_INPUT_MAGNITUDE = safe_input_magnitude()


def wrap_signed(value: int, width: int) -> int:
    unsigned = value & ((1 << width) - 1)
    if unsigned >= 1 << (width - 1):
        return unsigned - (1 << width)
    return unsigned


def random_complex(rng: random.Random) -> tuple[int, int]:
    while True:
        real = wrap_signed(rng.getrandbits(INPUT_WIDTH), INPUT_WIDTH)
        imag = wrap_signed(rng.getrandbits(INPUT_WIDTH), INPUT_WIDTH)
        magnitude = math.hypot(real, imag) / (1 << FRACTIONAL_BITS)
        if magnitude <= SAFE_INPUT_MAGNITUDE:
            return real, imag


def exact_dft(values: list[tuple[int, int]]) -> list[complex]:
    decoded = [complex(real, imag) / (1 << FRACTIONAL_BITS) for real, imag in values]
    return [
        sum(
            value * cmath.exp(-2j * math.pi * output * index / FFT_SIZE)
            for index, value in enumerate(decoded)
        )
        for output in range(FFT_SIZE)
    ]


def propagated_error_bound(values: list[tuple[int, int]]) -> float:
    magnitude = max(
        abs(complex(real, imag) / (1 << FRACTIONAL_BITS))
        for real, imag in values
    )
    error = 0.0
    for _ in range(4):
        error = (
            (2 + TWIDDLE_ERROR_BOUND) * error
            + magnitude * TWIDDLE_ERROR_BOUND
            + ARITHMETIC_ERROR_BOUND
        )
        magnitude *= 2
    return error


def set_bit(dut, name: str, value: int) -> None:
    getattr(dut, name).value = value


def get_bit(dut, name: str) -> int:
    value = getattr(dut, name).value
    assert value.is_resolvable, f"{name} is {value}"
    return int(value)


def drive_complex(dut, port: str, lane: int, value: tuple[int, int]) -> None:
    real, imag = value
    real &= (1 << INPUT_WIDTH) - 1
    imag &= (1 << INPUT_WIDTH) - 1
    for bit in range(INPUT_WIDTH):
        set_bit(dut, f"{port}_{lane}_{bit}", (imag >> bit) & 1)
        set_bit(dut, f"{port}_{lane}_{INPUT_WIDTH + bit}", (real >> bit) & 1)


def read_complex(dut, port: str, lane: int) -> tuple[int, int]:
    imag = sum(
        get_bit(dut, f"{port}_{lane}_{bit}") << bit
        for bit in range(OUTPUT_WIDTH)
    )
    real = sum(
        get_bit(dut, f"{port}_{lane}_{OUTPUT_WIDTH + bit}") << bit
        for bit in range(OUTPUT_WIDTH)
    )
    return wrap_signed(real, OUTPUT_WIDTH), wrap_signed(imag, OUTPUT_WIDTH)


def make_schedule(rng: random.Random):
    cycles: list[tuple[int, list[tuple[int, int]]]] = []
    expected: dict[int, tuple[list[complex], float]] = {}
    gaps = [0, 1, 2] + [rng.choice((0, 1, 2)) for _ in range(FRAME_COUNT - 3)]

    for frame_index in range(FRAME_COUNT):
        values = [
            random_complex(rng)
            for _ in range(FFT_SIZE)
        ]
        start = len(cycles)
        result = exact_dft(values)
        error_bound = propagated_error_bound(values)
        for cycle in range(FRAME_LENGTH):
            first = 1 if cycle == 0 else 0
            cycles.append((first, values[cycle * LANES : (cycle + 1) * LANES]))
            expected[start + LATENCY + cycle] = (
                result[cycle * LANES : (cycle + 1) * LANES],
                error_bound,
            )
        cycles.extend((0, [(0, 0)] * LANES) for _ in range(gaps[frame_index]))

    return cycles, expected


def drive_cycle(dut, cycle: tuple[int, list[tuple[int, int]]]) -> None:
    first, values = cycle
    dut.i_first.value = first
    for lane, value in enumerate(values):
        drive_complex(dut, "i_data", lane, value)


@cocotb.test()
async def random_frames_match_fixed_point_fft(dut) -> None:
    rng = random.Random(0x16F4)
    schedule, expected = make_schedule(rng)
    zero_cycle = (0, [(0, 0)] * LANES)
    input_first = [cycle[0] for cycle in schedule]

    dut.clock.value = 0
    drive_cycle(dut, schedule[0])
    cocotb.start_soon(
        Clock(dut.clock, 2, unit="ns").start(start_high=False)
    )

    final_output_cycle = max(expected) + 1
    for rising_number in range(1, final_output_cycle + 1):
        await RisingEdge(dut.clock)
        await ReadOnly()

        logical_output_cycle = rising_number
        source_cycle = logical_output_cycle - LATENCY
        if source_cycle >= 0:
            expected_first = (
                input_first[source_cycle] if source_cycle < len(input_first) else 0
            )
            assert int(dut.o_first.value) == expected_first, (
                f"o_first mismatch at output cycle {logical_output_cycle}; "
                f"source cycle {source_cycle}"
            )

        if logical_output_cycle in expected:
            expected_values, error_bound = expected[logical_output_cycle]
            raw_actual = [read_complex(dut, "o_data", lane) for lane in range(LANES)]
            actual = [
                complex(real, imag) / (1 << FRACTIONAL_BITS)
                for real, imag in raw_actual
            ]
            for lane, (observed, exact) in enumerate(zip(actual, expected_values)):
                error = abs(observed - exact)
                assert error <= error_bound + 1e-12, (
                    f"FFT error at cycle {logical_output_cycle}, lane {lane}: "
                    f"{error} > {error_bound}"
                )

        await FallingEdge(dut.clock)
        next_input_cycle = rising_number
        drive_cycle(
            dut,
            schedule[next_input_cycle]
            if next_input_cycle < len(schedule)
            else zero_cycle,
        )
