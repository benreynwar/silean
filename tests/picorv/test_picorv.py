import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, Timer
from utils import next_drive_phase


def drive_bus(dut, stem: str, width: int, value: int) -> None:
    for index in range(width):
        getattr(dut, f"{stem}_{index}").value = (value >> index) & 1


def read_bus(dut, stem: str, width: int) -> int:
    return sum(int(getattr(dut, f"{stem}_{index}").value) << index
               for index in range(width))


@cocotb.test()
async def executes_a_small_program_and_traps(dut) -> None:
    """Exercise fetch, decode, register writeback, store, and EBREAK trap."""
    program = {
        0x0000: 0x00500093,  # addi x1, x0, 5
        0x0004: 0x00308113,  # addi x2, x1, 3
        0x0008: 0x02202023,  # sw x2, 32(x0)
        0x000C: 0x00100073,  # ebreak (configured as a trap)
        # A fetch may be prefetched before EBREAK enters the trap phase.
        0x0010: 0x00000013,  # nop
    }

    cocotb.start_soon(Clock(dut.clock, 10, unit="ns").start())
    dut.resetn.value = 0
    dut.mem_ready.value = 0
    drive_bus(dut, "mem_rdata", 32, 0)
    await next_drive_phase(dut.clock)
    await next_drive_phase(dut.clock)
    assert int(dut.trap.value) == 0

    dut.resetn.value = 1
    fetched = []
    stores = []
    pending = None

    for _ in range(300):
        await FallingEdge(dut.clock)
        dut.mem_ready.value = 0

        if int(dut.mem_valid.value):
            address = read_bus(dut, "mem_addr", 32)
            instruction = int(dut.mem_instr.value)
            strobes = read_bus(dut, "mem_wstrb", 4)
            # `mem_wdata` is a source don't-care on reads and may legitimately
            # contain X in simulation. Observe it only for a write request.
            write_data = read_bus(dut, "mem_wdata", 32) if strobes else None
            snapshot = (
                instruction,
                address,
                write_data,
                strobes,
            )

            # Stall each transaction for one complete cycle. On the second
            # observation the registered request must be unchanged.
            if pending is None:
                pending = snapshot
                continue
            assert snapshot == pending, "request changed while mem_ready was low"
            pending = None

            if snapshot[0]:
                assert snapshot[3] == 0
                assert address in program, f"unexpected fetch address 0x{address:08x}"
                fetched.append(address)
                drive_bus(dut, "mem_rdata", 32, program[address])
            else:
                stores.append((address, snapshot[2], snapshot[3]))
                drive_bus(dut, "mem_rdata", 32, 0)
            dut.mem_ready.value = 1

        await Timer(1, unit="ns")
        if int(dut.trap.value):
            break
    else:
        raise AssertionError(f"core did not trap; accepted fetches were {fetched}")

    # The store makes the two preceding register writes observable at the
    # hardware boundary. Fetching one sequential word beyond EBREAK is
    # permitted because the source overlaps prefetch.
    assert fetched[:4] == [0x0000, 0x0004, 0x0008, 0x000C]
    assert stores == [(0x20, 8, 0xF)]


@cocotb.test()
async def illegal_instruction_traps(dut) -> None:
    """Check the configured CATCH_ILLINSN path independently of EBREAK."""
    cocotb.start_soon(Clock(dut.clock, 10, unit="ns").start())
    dut.resetn.value = 0
    dut.mem_ready.value = 0
    drive_bus(dut, "mem_rdata", 32, 0)
    await next_drive_phase(dut.clock)
    await next_drive_phase(dut.clock)
    dut.resetn.value = 1

    accepted = []
    pending_address = None
    for _ in range(80):
        await FallingEdge(dut.clock)
        dut.mem_ready.value = 0

        if int(dut.mem_valid.value):
            assert int(dut.mem_instr.value) == 1
            assert read_bus(dut, "mem_wstrb", 4) == 0
            address = read_bus(dut, "mem_addr", 32)
            if pending_address is None:
                pending_address = address
                continue
            assert address == pending_address
            accepted.append(address)
            # Address zero returns an invalid all-zero word. A speculative
            # sequential fetch, if visible, receives a harmless NOP.
            drive_bus(dut, "mem_rdata", 32,
                      0x00000000 if address == 0 else 0x00000013)
            dut.mem_ready.value = 1
            pending_address = None

        await Timer(1, unit="ns")
        if int(dut.trap.value):
            break
    else:
        raise AssertionError(f"illegal instruction did not trap; fetches were {accepted}")

    assert accepted[0] == 0
