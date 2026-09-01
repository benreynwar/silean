from collections.abc import Sequence
import random

from cocotb.triggers import FallingEdge, RisingEdge


async def next_drive_phase(clock) -> None:
    """Advance across the active edge and stop at the next falling-edge drive phase."""
    await RisingEdge(clock)
    await FallingEdge(clock)


def random_payload(rng: random.Random, fields: Sequence[str]) -> tuple[int, ...]:
    return tuple(rng.randrange(2) for _ in fields)


def drive_payload(
    dut, fields: Sequence[str], payload: Sequence[int]
) -> None:
    assert len(payload) == len(fields)
    for name, value in zip(fields, payload, strict=True):
        getattr(dut, name).value = value


def read_payload(dut, fields: Sequence[str]) -> tuple[int, ...]:
    return tuple(int(getattr(dut, name).value) for name in fields)
