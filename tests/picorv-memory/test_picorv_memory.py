import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer
from utils import next_drive_phase


def drive_bus(dut, stem: str, width: int, value: int) -> None:
    for index in range(width):
        getattr(dut, f"{stem}_{index}").value = (value >> index) & 1


def read_bus(dut, stem: str, width: int) -> int:
    return sum(int(getattr(dut, f"{stem}_{index}").value) << index
               for index in range(width))


def drive_idle(dut) -> None:
    dut.resetn.value = 1
    dut.trap.value = 0
    dut.mem_do_prefetch.value = 0
    dut.mem_do_rinst.value = 0
    dut.mem_do_rdata.value = 0
    dut.mem_do_wdata.value = 0
    dut.mem_ready.value = 0
    drive_bus(dut, "next_pc", 32, 0)
    drive_bus(dut, "reg_op1", 32, 0)
    drive_bus(dut, "reg_op2", 32, 0)
    drive_bus(dut, "mem_wordsize", 2, 0)
    drive_bus(dut, "mem_rdata", 32, 0)


@cocotb.test()
async def memory_protocol_paths_match_the_checked_contract(dut) -> None:
    cocotb.start_soon(Clock(dut.clock, 10, unit="ns").start())

    # Establish the source reset state.
    drive_idle(dut)
    dut.resetn.value = 0
    await next_drive_phase(dut.clock)
    await next_drive_phase(dut.clock)
    assert int(dut.mem_valid.value) == 0

    # An instruction command first appears on look-ahead, then becomes the
    # registered request on the following edge. The address is word-aligned.
    drive_idle(dut)
    dut.mem_do_rinst.value = 1
    drive_bus(dut, "next_pc", 32, 0x1003)
    await Timer(1, unit="ns")
    assert int(dut.mem_la_read.value) == 1
    assert read_bus(dut, "mem_la_addr", 32) == 0x1000
    assert int(dut.mem_valid.value) == 0
    await next_drive_phase(dut.clock)
    assert int(dut.mem_valid.value) == 1
    assert int(dut.mem_instr.value) == 1
    assert read_bus(dut, "mem_addr", 32) == 0x1000

    # A stalled request retains all registered request fields.
    await next_drive_phase(dut.clock)
    assert int(dut.mem_valid.value) == 1
    assert int(dut.mem_instr.value) == 1
    assert read_bus(dut, "mem_addr", 32) == 0x1000

    # Completion is combinational on the accepting cycle, and non-latched
    # response mode bypasses the live read data before capturing it at edge.
    dut.mem_ready.value = 1
    drive_bus(dut, "mem_rdata", 32, 0x00510093)
    await Timer(1, unit="ns")
    assert int(dut.mem_done.value) == 1
    assert read_bus(dut, "mem_rdata_latched", 32) == 0x00510093
    await next_drive_phase(dut.clock)
    assert int(dut.mem_valid.value) == 0
    assert read_bus(dut, "mem_rdata_q", 32) == 0x00510093

    # Byte read selection is a combinational view of address low bits and the
    # live memory response.
    drive_idle(dut)
    drive_bus(dut, "reg_op1", 32, 0x2002)
    drive_bus(dut, "mem_wordsize", 2, 2)
    drive_bus(dut, "mem_rdata", 32, 0x44332211)
    await Timer(1, unit="ns")
    assert read_bus(dut, "mem_rdata_word", 32) == 0x33

    # A byte write duplicates the byte across all lanes and selects only the
    # addressed strobe. The request remains registered until accepted.
    dut.mem_do_wdata.value = 1
    drive_bus(dut, "reg_op2", 32, 0xAA)
    await Timer(1, unit="ns")
    assert int(dut.mem_la_write.value) == 1
    assert read_bus(dut, "mem_la_addr", 32) == 0x2000
    assert read_bus(dut, "mem_la_wdata", 32) == 0xAAAAAAAA
    assert read_bus(dut, "mem_la_wstrb", 4) == 0x4
    await next_drive_phase(dut.clock)
    assert int(dut.mem_valid.value) == 1
    assert read_bus(dut, "mem_wstrb", 4) == 0x4
    dut.mem_ready.value = 1
    await Timer(1, unit="ns")
    assert int(dut.mem_done.value) == 1
    await next_drive_phase(dut.clock)
    assert int(dut.mem_valid.value) == 0

    # A pure prefetch transfer does not complete the instruction command. It
    # moves into phase 3; a later rinst consumes it without another transfer.
    drive_idle(dut)
    dut.mem_do_prefetch.value = 1
    drive_bus(dut, "next_pc", 32, 0x3000)
    await next_drive_phase(dut.clock)
    assert int(dut.mem_valid.value) == 1
    dut.mem_ready.value = 1
    drive_bus(dut, "mem_rdata", 32, 0xDEADBEEF)
    await Timer(1, unit="ns")
    assert int(dut.mem_done.value) == 0
    await next_drive_phase(dut.clock)
    assert int(dut.mem_valid.value) == 0
    drive_idle(dut)
    dut.mem_do_rinst.value = 1
    await Timer(1, unit="ns")
    assert int(dut.mem_done.value) == 1
    await next_drive_phase(dut.clock)
    drive_idle(dut)
    await Timer(1, unit="ns")
    assert int(dut.mem_done.value) == 0

    # Reset suppresses completion and clears the request, but the source's
    # separate response-capture process still records a simultaneous transfer.
    dut.mem_do_rinst.value = 1
    drive_bus(dut, "next_pc", 32, 0x4000)
    await next_drive_phase(dut.clock)
    assert int(dut.mem_valid.value) == 1
    dut.resetn.value = 0
    dut.mem_ready.value = 1
    drive_bus(dut, "mem_rdata", 32, 0xA5A55A5A)
    await Timer(1, unit="ns")
    assert int(dut.mem_done.value) == 0
    await next_drive_phase(dut.clock)
    assert int(dut.mem_valid.value) == 0
    assert read_bus(dut, "mem_rdata_q", 32) == 0xA5A55A5A
