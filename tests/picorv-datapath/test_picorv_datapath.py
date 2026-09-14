import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly
from utils import next_drive_phase


SCALAR_INPUTS = (
    "latched_store", "latched_stalu", "latched_branch", "latched_is_lu",
    "latched_is_lh", "latched_is_lb", "mem_do_prefetch", "mem_do_rdata",
    "mem_do_wdata", "decoder_trigger", "instr_lui", "instr_jal",
    "instr_trap", "instr_sub", "instr_beq", "instr_bne", "instr_bge",
    "instr_bgeu", "instr_xori", "instr_xor", "instr_ori", "instr_or",
    "instr_andi", "instr_and", "instr_slli", "instr_srli", "instr_srai",
    "instr_sll", "instr_srl", "instr_sra", "is_lui_auipc_jal",
    "is_lb_lh_lw_lbu_lhu", "is_slli_srli_srai",
    "is_jalr_addi_slti_sltiu_xori_ori_andi",
    "is_lui_auipc_jal_jalr_addi_add_sub", "is_slti_blt_slt",
    "is_sltiu_bltu_sltu", "is_compare", "mem_done",
)


def drive_bus(dut, stem: str, width: int, value: int) -> None:
    for index in range(width):
        getattr(dut, f"{stem}_{index}").value = (value >> index) & 1


def read_bus(dut, stem: str, width: int) -> int:
    return sum(int(getattr(dut, f"{stem}_{index}").value) << index
               for index in range(width))


def drive_idle(dut) -> None:
    dut.resetn.value = 1
    for name in SCALAR_INPUTS:
        getattr(dut, name).value = 0
    drive_bus(dut, "cpu_state", 8, 0)
    drive_bus(dut, "decoded_imm", 32, 0)
    drive_bus(dut, "decoded_imm_j", 32, 0)
    drive_bus(dut, "decoded_rs2", 5, 0)
    drive_bus(dut, "cpuregs_rs1", 32, 0)
    drive_bus(dut, "cpuregs_rs2", 32, 0)
    drive_bus(dut, "mem_rdata_word", 32, 0)


@cocotb.test()
async def stateful_datapath_paths_match_the_checked_contract(dut) -> None:
    cocotb.start_soon(Clock(dut.clock, 10, unit="ns").start())

    # Establish a known state through the datapath's synchronous reset input.
    drive_idle(dut)
    dut.resetn.value = 0
    await next_drive_phase(dut.clock)
    await next_drive_phase(dut.clock)
    assert read_bus(dut, "reg_pc", 32) == 0

    # Two fetch edges expose the registered PC progression 0 -> 4.
    drive_idle(dut)
    drive_bus(dut, "cpu_state", 8, 0x40)
    dut.decoder_trigger.value = 1
    await next_drive_phase(dut.clock)
    assert read_bus(dut, "reg_pc", 32) == 0
    assert read_bus(dut, "next_pc", 32) == 4
    await next_drive_phase(dut.clock)
    assert read_bus(dut, "reg_pc", 32) == 4
    assert read_bus(dut, "next_pc", 32) == 8

    # The ordinary ld_rs1 path captures two register operands and the low five
    # bits of rs2 as the iterative shift count.
    drive_idle(dut)
    drive_bus(dut, "cpu_state", 8, 0x20)
    drive_bus(dut, "cpuregs_rs1", 32, 3)
    drive_bus(dut, "cpuregs_rs2", 32, 5)
    await next_drive_phase(dut.clock)
    assert read_bus(dut, "reg_op1", 32) == 3
    assert read_bus(dut, "reg_op2", 32) == 5
    assert read_bus(dut, "reg_sh", 5) == 5

    # ALU capture is registered. Fetch writeback with stalu then exposes the
    # captured sum, rather than recomputing from later operands.
    drive_idle(dut)
    dut.is_lui_auipc_jal_jalr_addi_add_sub.value = 1
    await next_drive_phase(dut.clock)
    drive_idle(dut)
    drive_bus(dut, "cpu_state", 8, 0x40)
    dut.latched_store.value = 1
    dut.latched_stalu.value = 1
    await ReadOnly()
    assert read_bus(dut, "cpuregs_wrdata", 32) == 8
    await FallingEdge(dut.clock)

    # A completed signed-byte load sign-extends into reg_out; ordinary fetch
    # writeback exposes that stored load result.
    drive_idle(dut)
    drive_bus(dut, "cpu_state", 8, 0x01)
    dut.mem_do_rdata.value = 1
    dut.mem_done.value = 1
    dut.latched_is_lb.value = 1
    drive_bus(dut, "mem_rdata_word", 32, 0x80)
    await next_drive_phase(dut.clock)
    drive_idle(dut)
    drive_bus(dut, "cpu_state", 8, 0x40)
    dut.latched_store.value = 1
    await ReadOnly()
    assert read_bus(dut, "cpuregs_wrdata", 32) == 0xFFFFFF80
    await FallingEdge(dut.clock)

    # Reload shift operands, then exercise the 4+1 iterative decomposition of
    # a five-bit logical-left shift and its final result capture edge.
    drive_idle(dut)
    drive_bus(dut, "cpu_state", 8, 0x20)
    drive_bus(dut, "cpuregs_rs1", 32, 1)
    drive_bus(dut, "cpuregs_rs2", 32, 5)
    await next_drive_phase(dut.clock)
    drive_idle(dut)
    drive_bus(dut, "cpu_state", 8, 0x04)
    dut.instr_sll.value = 1
    await next_drive_phase(dut.clock)
    assert read_bus(dut, "reg_op1", 32) == 16
    assert read_bus(dut, "reg_sh", 5) == 1
    await next_drive_phase(dut.clock)
    assert read_bus(dut, "reg_op1", 32) == 32
    assert read_bus(dut, "reg_sh", 5) == 0
    await next_drive_phase(dut.clock)
    drive_idle(dut)
    drive_bus(dut, "cpu_state", 8, 0x40)
    dut.latched_store.value = 1
    await FallingEdge(dut.clock)
    assert read_bus(dut, "cpuregs_wrdata", 32) == 32
