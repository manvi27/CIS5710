`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../divider_unsigned_pipelined.sv"
`endif

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
  // synthesis translate_on
endmodule

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] x_rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] x_rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
    localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here

  assign regs[0] = 32'd0;
  assign x_rs1_data = regs[rs1];
  assign x_rs2_data = regs[rs2];
  always_ff @(posedge clk) begin
    
    if(1'b1 == rst) begin
      for(int i = 1;i < NumRegs; i = i+1) begin
        regs[i] <= 32'd0; 
      end
    end 

    if(we && (|rd) == 1'b1 ) begin
      regs[rd] <= rd_data;
    end
  end

endmodule

/**
 * This enum is used to classify each cycle as it comes through the Writeback stage, identifying
 * if a valid insn is present or, if it is a stall cycle instead, the reason for the stall. The
 * enum values are mutually exclusive: only one should be set for any given cycle. These values
 * are compared against the trace-*.json files to ensure that the datapath is running with the
 * correct timing.
 *
 * You will need to set these values at various places within your pipeline, and propagate them
 * through the stages until they reach Writeback where they can be checked.
 */
typedef enum {
  /** invalid value, this should never appear after the initial reset sequence completes */
  CYCLE_INVALID = 0,
  /** a stall cycle that arose from the initial reset signal */
  CYCLE_RESET = 1,
  /** not a stall cycle, a valid insn is in Writeback */
  CYCLE_NO_STALL = 2,
  /** a stall cycle that arose from a taken branch/jump */
  CYCLE_TAKEN_BRANCH = 4,

  // the values below are only needed in HW5B

  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence.i insn */
  CYCLE_FENCEI = 32
} cycle_status_e;

typedef struct packed {
  logic insn_lui;
  logic insn_auipc;
  logic insn_jal;
  logic insn_jalr;

  logic insn_beq;
  logic insn_bne;
  logic insn_blt;
  logic insn_bge;
  logic insn_bltu;
  logic insn_bgeu;

  logic insn_lb;
  logic insn_lh;
  logic insn_lw;
  logic insn_lbu;
  logic insn_lhu;

  logic insn_sb;
  logic insn_sh;
  logic insn_sw;

  logic insn_addi;
  logic insn_slti;
  logic insn_sltiu;
  logic insn_xori;
  logic insn_ori;
  logic insn_andi;

  logic insn_slli;
  logic insn_srli;
  logic insn_srai;

  logic insn_add;
  logic insn_sub ;
  logic insn_sll ;
  logic insn_slt;
  logic insn_sltu ;
  logic insn_xor ;
  logic insn_srl;
  logic insn_sra;
  logic insn_or;
  logic insn_and;

  logic insn_mul;
  logic insn_mulh;
  logic insn_mulhsu;
  logic insn_mulhu;
  logic insn_div;
  logic insn_divu;
  logic insn_rem;
  logic insn_remu;

  logic insn_ecall;
  logic insn_fence;
} insn_set;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [4:0] rd_no;
  logic [4:0] rs1_no;
  logic [`REG_SIZE] rs1_data_temp;
  logic [4:0] rs2_no;
  logic [`REG_SIZE] rs2_data_temp;
  logic [6:0] insn7bit;
  logic [2:0] insn3bit;
  logic [`REG_SIZE] addr_to_dmem;
  logic [3:0] store_we_to_dmem;
  logic [`REG_SIZE] store_data_to_dmem;
  logic [`REG_SIZE] insn_imem;
  logic [`REG_SIZE] imm_i_sext_X;
  logic [`OPCODE_SIZE] insn_opcode;
  insn_set exe_control;
} stage_decode_t;

/** state at the start of Execute stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [4:0] rd_no;
  logic [`REG_SIZE] rd_val;
  logic [4:0] rs1_no;
  logic [`REG_SIZE] rs1_data_temp;
  logic [4:0] rs2_no;
  logic [`REG_SIZE] rs2_data_temp;
  logic [`REG_SIZE] addr_to_dmem;
  logic [3:0] store_we_to_dmem;
  logic [`REG_SIZE] store_data_to_dmem;
  logic [`REG_SIZE] insn_imem;
  logic [`REG_SIZE] imm_i_sext_X;
  logic [`OPCODE_SIZE] insn_opcode;
  insn_set exe_control;
} stage_execute_t;

/** state at the start of Memory stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [4:0] rd_no;
  logic [`REG_SIZE] rd_val;
  logic [4:0] rs1_no;
  logic [`REG_SIZE] rs1_data_temp;
  logic [4:0] rs2_no;
  logic [`REG_SIZE] rs2_data_temp;
  logic [`REG_SIZE] addr_to_dmem;
  logic [3:0] store_we_to_dmem;
  logic [`REG_SIZE] store_data_to_dmem;
  logic [`OPCODE_SIZE] insn_opcode;
  logic halt_sig;
  logic branch_taken;
  logic [`REG_SIZE] pcNext;
  insn_set mem_control;
} stage_memory_t;

/** state at the start of Write stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [4:0] rd_no;
  logic [`REG_SIZE] rd_val;
  logic [4:0] rs1_no;
  logic [`REG_SIZE] rs1_data_temp;
  logic [4:0] rs2_no;
  logic [`REG_SIZE] rs2_data_temp;
  logic [`OPCODE_SIZE] insn_opcode;
  logic halt_sig;
  logic [3:0] store_we_to_dmem;
  logic [`REG_SIZE] store_data_to_dmem;
} stage_write_t;


module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;//0x03
  localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;//0x23
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;//0x63
  localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;//0x67
  localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;//0x0f
  localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;//0x6f

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;//0x13
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;//0x33
  localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;//0x73

  localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;//0x17
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;//0x37

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] pcCurr;
  logic [`REG_SIZE] pcNext;
  wire [`REG_SIZE] instr;
  cycle_status_e cycleStatus;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      pcCurr <= 32'd0;
      cycleStatus <= CYCLE_NO_STALL;
    end else begin
      cycleStatus <= CYCLE_NO_STALL;
      if (branch_taken) begin
        pcCurr <= pcNext; 
      end else begin
        pcCurr <= pcCurr + 4;
      end
    end
  end
  // send PC to imem
  assign pc_to_imem = pcCurr;
  assign instr = insn_from_imem;
  
  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (instr),
      .disasm(f_disasm)
  );

  wire [6:0] insn7bit;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn3bit;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;
  wire [12:0] imm_b_temp;
  logic [`REG_SIZE] imm_b_sext_temp;
  wire [11:0] imm_i;
  wire [11:0] imm_s;
  wire [12:0] imm_b;
  wire [20:0] imm_j;
  wire [19:0] imm_u;

  logic [`REG_SIZE] imm_i_sext;
  logic [`REG_SIZE] imm_i_ext;
  logic [`REG_SIZE] imm_s_sext;
  logic [`REG_SIZE] imm_b_sext;
  logic [`REG_SIZE] imm_j_sext;
  logic [`REG_SIZE] imm_u_ext;
  logic [`REG_SIZE] imm_i_sext_X;

  insn_set insnSetX;
  logic [`REG_SIZE] rs1_data_temp;
  logic [`REG_SIZE] rs2_data_temp;
  logic [`REG_SIZE] rs1_mux_data;
  logic [`REG_SIZE] rs2_mux_data;

  logic illegal_insn;
  logic [4:0] rd; 
  logic [`REG_SIZE] rd_data;
  logic [4:0] rs1;
  logic [4:0] rs2;
  logic we;
  logic add_cin;
  logic [`REG_SIZE] add_sum;
  logic [`REG_SIZE] add_a, add_b;
  logic halt_sig;
  logic halt_sig_temp;
  logic [3:0] store_we_to_dmem_temp;
  logic [63:0] product;
  logic [31:0] product_signed;
  logic [63:0] product_final;
  logic [31:0] dividend;
  logic [31:0] divisor;
  logic [31:0] remainder;
  logic [31:0] quotient;
  logic branch_taken;
  logic [`REG_SIZE] rd_temp;
  logic [`OPCODE_SIZE] insn_opcode_x;
  logic [4:0] m_rd_no;
  logic [4:0] w_rd_no;
  logic [4:0] x_rs1_no;
  logic [4:0] x_rs2_no;
  logic [`REG_SIZE] x_rs1_data;
  logic [`REG_SIZE] x_rs2_data;
  logic [3:0] mux_val_mx_wx;
  logic zero_check, div_rs1, div_rs2;

  assign {insn7bit,
          insn_rs2,
          insn_rs1,
          insn3bit,
          insn_rd,
          insn_opcode} = insn_from_imem;

  assign {imm_b_temp[12],
          imm_b_temp[10:5]} = insn7bit,
        {imm_b_temp[4:1],
        imm_b_temp[11]} = insn_rd,
        imm_b_temp[0] = 1'b0;

  assign imm_b_sext_temp = {{19{imm_b_temp[12]}}, imm_b_temp[12:0]};


  RegFile rf(.rd(stateW.rd_no),
            .rd_data(stateW.rd_val),
            .rs1(stateD.rs1_no),
            .x_rs1_data(rs1_data_temp), 
            .rs2(stateD.rs2_no),
            .x_rs2_data(rs2_data_temp),
            .clk(clk),
            .we(we),
            .rst(rst));

  cla alu (.a(add_a),
          .b(add_b),
          .cin(add_cin),
          .sum(add_sum));

  divider_unsigned_pipelined div(.clk(clk),
                                .rst(rst),
                                .i_dividend(dividend),
                                .i_divisor(divisor),
                                .o_quotient(quotient),
                                .o_remainder(remainder));

  /****************/
  /* DECODE STAGE */
  /****************/

  stage_decode_t stateD;
  always_ff @(posedge clk) begin
    if (rst) begin
      stateD <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        rd_no: 0,
        rs1_no: 0,
        rs1_data_temp: 0,
        rs2_no: 0,
        rs2_data_temp: 0,
        insn7bit: 0,
        insn3bit: 0,
        addr_to_dmem: 0,
        store_we_to_dmem: 0,
        store_data_to_dmem: 0,
        insn_imem: 0,
        imm_i_sext_X: 0,
        insn_opcode: 0,
        exe_control: '{default:0}
      };
    end else begin
      begin
        if (branch_taken) begin
          stateD <= 0;
          stateD.cycle_status <= CYCLE_TAKEN_BRANCH;
        end else begin
          stateD <= '{
          pc: pcCurr,
          insn: instr,
          cycle_status: cycleStatus,
          rd_no: insn_opcode == OpcodeBranch ? 0 : insn_rd,
          rs1_no: insn_opcode == OpcodeLui ? 0: insn_rs1,
          rs1_data_temp: rs1_data_temp,
          rs2_no: ((insn_opcode == OpcodeRegImm) || (insn_opcode == OpcodeLui)) ? 0: insn_rs2,
          rs2_data_temp: rs2_data_temp,
          insn7bit: insn_opcode == OpcodeLui ? 0: insn7bit,
          insn3bit: insn_opcode == OpcodeLui ? 0: insn3bit,
          addr_to_dmem: 0,
          store_we_to_dmem: 0,
          store_data_to_dmem: 0,
          insn_imem: insn_from_imem,
          imm_i_sext_X: 0,
          insn_opcode: insn_opcode,
          exe_control: '{default:0}
        };
        end 
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (stateD.insn),
      .disasm(d_disasm)
  );

  assign imm_i = stateD.insn_imem[31:20];
  wire [ 4:0] imm_shamt = stateD.insn_imem[24:20];

  assign imm_s[11:5] = stateD.insn7bit, imm_s[4:0] = stateD.insn_imem[11:7];

  assign {imm_b[12], imm_b[10:5]} = stateD.insn7bit, {imm_b[4:1], imm_b[11]} = stateD.insn_imem[11:7], imm_b[0] = 1'b0;

  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {stateD.insn_imem[31:12], 1'b0};
  
  assign imm_u = stateD.insn_imem[31:12];

  logic [1:0] mux_val_wd;
  logic [4:0] wd_rd_no;
  assign wd_rd_no = stateW.rd_no;

  assign imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  assign imm_i_ext = {{20{1'b0}}, imm_i[11:0]};
  assign imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  assign imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  assign imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};
  assign imm_u_ext = {{12{1'b0}},imm_u[19:0]};

  assign insnSetX.insn_lui = stateD.insn_opcode == OpcodeLui;
  assign insnSetX.insn_auipc = stateD.insn_opcode == OpcodeAuipc;
  assign insnSetX.insn_jal = stateD.insn_opcode == OpcodeJal;
  assign insnSetX.insn_jalr = stateD.insn_opcode == OpcodeJalr;

  assign insnSetX.insn_beq = stateD.insn_opcode == OpcodeBranch && stateD.insn_imem[14:12] == 3'b000;
  assign insnSetX.insn_bne = stateD.insn_opcode == OpcodeBranch && stateD.insn_imem[14:12] == 3'b001;
  assign insnSetX.insn_blt = stateD.insn_opcode == OpcodeBranch && stateD.insn_imem[14:12] == 3'b100;
  assign insnSetX.insn_bge = stateD.insn_opcode == OpcodeBranch && stateD.insn_imem[14:12] == 3'b101;
  assign insnSetX.insn_bltu = stateD.insn_opcode == OpcodeBranch && stateD.insn_imem[14:12] == 3'b110;
  assign insnSetX.insn_bgeu = stateD.insn_opcode == OpcodeBranch && stateD.insn_imem[14:12] == 3'b111;

  assign insnSetX.insn_lb = stateD.insn_opcode == OpcodeLoad && stateD.insn_imem[14:12] == 3'b000;
  assign insnSetX.insn_lh = stateD.insn_opcode == OpcodeLoad && stateD.insn_imem[14:12] == 3'b001;
  assign insnSetX.insn_lw = stateD.insn_opcode == OpcodeLoad && stateD.insn_imem[14:12] == 3'b010;
  assign insnSetX.insn_lbu = stateD.insn_opcode == OpcodeLoad && stateD.insn_imem[14:12] == 3'b100;
  assign insnSetX.insn_lhu = stateD.insn_opcode == OpcodeLoad && stateD.insn_imem[14:12] == 3'b101;

  assign insnSetX.insn_sb = stateD.insn_opcode == OpcodeStore && stateD.insn_imem[14:12] == 3'b000;
  assign insnSetX.insn_sh = stateD.insn_opcode == OpcodeStore && stateD.insn_imem[14:12] == 3'b001;
  assign insnSetX.insn_sw = stateD.insn_opcode == OpcodeStore && stateD.insn_imem[14:12] == 3'b010;

  assign insnSetX.insn_addi = stateD.insn_opcode == OpcodeRegImm && stateD.insn_imem[14:12] == 3'b000;
  assign insnSetX.insn_slti = stateD.insn_opcode == OpcodeRegImm && stateD.insn_imem[14:12] == 3'b010;
  assign insnSetX.insn_sltiu = stateD.insn_opcode == OpcodeRegImm && stateD.insn_imem[14:12] == 3'b011;
  assign insnSetX.insn_xori = stateD.insn_opcode == OpcodeRegImm && stateD.insn_imem[14:12] == 3'b100;
  assign insnSetX.insn_ori = stateD.insn_opcode == OpcodeRegImm && stateD.insn_imem[14:12] == 3'b110;
  assign insnSetX.insn_andi = stateD.insn_opcode == OpcodeRegImm && stateD.insn_imem[14:12] == 3'b111;

  assign insnSetX.insn_slli = stateD.insn_opcode == OpcodeRegImm && stateD.insn_imem[14:12] == 3'b001 && stateD.insn_imem[31:25] == 7'd0;
  assign insnSetX.insn_srli = stateD.insn_opcode == OpcodeRegImm && stateD.insn_imem[14:12] == 3'b101 && stateD.insn_imem[31:25] == 7'd0;
  assign insnSetX.insn_srai = stateD.insn_opcode == OpcodeRegImm && stateD.insn_imem[14:12] == 3'b101 && stateD.insn_imem[31:25] == 7'b0100000;

  assign insnSetX.insn_add = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[14:12] == 3'b000 && stateD.insn_imem[31:25] == 7'd0;
  assign insnSetX.insn_sub  = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[14:12] == 3'b000 && stateD.insn_imem[31:25] == 7'b0100000;
  assign insnSetX.insn_sll = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[14:12] == 3'b001 && stateD.insn_imem[31:25] == 7'd0;
  assign insnSetX.insn_slt = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[14:12] == 3'b010 && stateD.insn_imem[31:25] == 7'd0;
  assign insnSetX.insn_sltu = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[14:12] == 3'b011 && stateD.insn_imem[31:25] == 7'd0;
  assign insnSetX.insn_xor = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[14:12] == 3'b100 && stateD.insn_imem[31:25] == 7'd0;
  assign insnSetX.insn_srl = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[14:12] == 3'b101 && stateD.insn_imem[31:25] == 7'd0;
  assign insnSetX.insn_sra  = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[14:12] == 3'b101 && stateD.insn_imem[31:25] == 7'b0100000;
  assign insnSetX.insn_or = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[14:12] == 3'b110 && stateD.insn_imem[31:25] == 7'd0;
  assign insnSetX.insn_and = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[14:12] == 3'b111 && stateD.insn_imem[31:25] == 7'd0;

  assign insnSetX.insn_mul    = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[31:25] == 7'd1 && stateD.insn_imem[14:12] == 3'b000;
  assign insnSetX.insn_mulh   = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[31:25] == 7'd1 && stateD.insn_imem[14:12] == 3'b001;
  assign insnSetX.insn_mulhsu = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[31:25] == 7'd1 && stateD.insn_imem[14:12] == 3'b010;
  assign insnSetX.insn_mulhu  = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[31:25] == 7'd1 && stateD.insn_imem[14:12] == 3'b011;
  assign insnSetX.insn_div    = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[31:25] == 7'd1 && stateD.insn_imem[14:12] == 3'b100;
  assign insnSetX.insn_divu   = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[31:25] == 7'd1 && stateD.insn_imem[14:12] == 3'b101;
  assign insnSetX.insn_rem    = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[31:25] == 7'd1 && stateD.insn_imem[14:12] == 3'b110;
  assign insnSetX.insn_remu   = stateD.insn_opcode == OpcodeRegReg && stateD.insn_imem[31:25] == 7'd1 && stateD.insn_imem[14:12] == 3'b111;

  assign insnSetX.insn_ecall = stateD.insn_opcode == OpcodeEnviron && stateD.insn_imem[31:7] == 25'd0;
  assign insnSetX.insn_fence = stateD.insn_opcode == OpcodeMiscMem;

  always_comb begin
    if (insnSetX.insn_jalr ||
        insnSetX.insn_addi ||
        insnSetX.insn_slti ||
        insnSetX.insn_sltiu ||
        insnSetX.insn_xori ||
        insnSetX.insn_ori ||
        insnSetX.insn_andi ||
        (stateD.insn_opcode == OpcodeLoad)) begin
      imm_i_sext_X = imm_i_sext;
    end
    else if (insnSetX.insn_slli ||
             insnSetX.insn_srli ||
             insnSetX.insn_srai) begin
      imm_i_sext_X = imm_i_ext;
    end
    else if (stateD.insn_opcode == OpcodeStore) begin
      imm_i_sext_X = imm_s_sext;
    end
    else if (stateD.insn_opcode == OpcodeBranch) begin
      imm_i_sext_X = imm_b_sext;
    end
    else if (stateD.insn_opcode == OpcodeJal) begin
      imm_i_sext_X = imm_j_sext;
    end
    else if ((stateD.insn_opcode == OpcodeLui) ||
             (stateD.insn_opcode == OpcodeAuipc)) begin
      imm_i_sext_X = imm_u_ext;
    end

    rs1_mux_data = rs1_data_temp;
    rs2_mux_data = rs2_data_temp;

    mux_val_wd = 2'b0;

    if (wd_rd_no != 0) begin
      case (wd_rd_no)
        stateD.rs1_no: begin
            mux_val_wd = 2'b01;
            rs1_mux_data = stateW.rd_val;
        end
        stateD.rs2_no: begin
            mux_val_wd = 2'b10;
            rs2_mux_data = stateW.rd_val;
        end
        default: begin
            // No action needed
        end
      endcase
    end

    tempStateX = '{
      pc: stateD.pc,
      insn: stateD.insn,
      cycle_status: stateD.cycle_status,
      rd_no: stateD.rd_no,
      rd_val: 0,
      rs1_no: stateD.rs1_no,
      rs1_data_temp: rs1_mux_data,
      rs2_no: stateD.rs2_no,
      rs2_data_temp: rs2_mux_data,
      addr_to_dmem: stateD.addr_to_dmem,
      store_we_to_dmem: stateD.store_we_to_dmem,
      store_data_to_dmem: stateD.store_data_to_dmem,
      insn_imem: stateD.insn_imem,
      imm_i_sext_X: imm_i_sext_X,
      insn_opcode: stateD.insn_opcode,
      exe_control: insnSetX
    };
  end

  /****************/
  /* EXECUTE STAGE */
  /****************/
  stage_execute_t stateX;
  stage_execute_t tempStateX;

  always_ff @(posedge clk) begin
    if (rst) begin
      stateX <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        rd_no: 0,
        rd_val: 0,
        rs1_no: 0,
        rs1_data_temp: 0,
        rs2_no: 0,
        rs2_data_temp: 0,
        addr_to_dmem: 0,
        store_we_to_dmem: 0,
        store_data_to_dmem: 0,
        insn_imem: 0,
        imm_i_sext_X: 0,
        insn_opcode: 0,
        exe_control: '{default:0}
      };
    end else begin
      begin
        if (branch_taken) begin
            stateX <= 0;
            stateX.cycle_status <= CYCLE_TAKEN_BRANCH;
        end else begin
            stateX <= tempStateX;
        end 
      end
    end
  end

  wire [255:0] e_disasm;
  Disasm #(
      .PREFIX("E")
  ) disasm_1execute (
      .insn  (stateX.insn),
      .disasm(e_disasm)
  );
  logic [31:0] addr_to_dmem_temp;
  assign m_rd_no = stateM.rd_no;
  assign w_rd_no = stateW.rd_no;
  assign x_rs1_no = stateX.rs1_no;
  assign x_rs2_no = stateX.rs2_no;
  assign insn_opcode_x = stateX.insn_opcode;

  always_latch begin
    x_rs1_data = stateX.rs1_data_temp;
    x_rs2_data = stateX.rs2_data_temp;

    mux_val_mx_wx = 0;
  
    if (m_rd_no != 0 || w_rd_no != 0) begin
      if (m_rd_no != 0) begin
        if (m_rd_no == x_rs1_no && m_rd_no != x_rs2_no) begin
          mux_val_mx_wx = 1;
          x_rs1_data = (stateM.insn_opcode == OpcodeLoad)?rd_val_temp:stateM.rd_val;
        end
        if (m_rd_no == x_rs2_no && m_rd_no != x_rs1_no) begin
          mux_val_mx_wx = 2;
          x_rs2_data = (stateM.insn_opcode == OpcodeLoad)?rd_val_temp:stateM.rd_val;
        end
        if (m_rd_no == x_rs1_no && m_rd_no == x_rs2_no) begin
            mux_val_mx_wx = 3;
          x_rs1_data = stateM.rd_val;
          x_rs2_data = stateM.rd_val;
        end
      end
      if (w_rd_no != 0 && w_rd_no != m_rd_no) begin
        if (w_rd_no == x_rs1_no && w_rd_no != x_rs2_no) begin
          mux_val_mx_wx = 4;
          x_rs1_data = stateW.rd_val;
        end
        if (w_rd_no == x_rs2_no && w_rd_no != x_rs1_no) begin
          mux_val_mx_wx = 5;
          x_rs2_data = stateW.rd_val;
        end
        if (w_rd_no == x_rs1_no && w_rd_no == x_rs2_no) begin
            mux_val_mx_wx = 6;
          x_rs1_data = stateW.rd_val;
          x_rs2_data = stateW.rd_val;
        end
        if (m_rd_no != 0 && w_rd_no != 0 && m_rd_no != w_rd_no) begin
          if (m_rd_no == x_rs1_no && w_rd_no == x_rs2_no && x_rs1_no != x_rs2_no) begin
            mux_val_mx_wx = 7;
            x_rs1_data = stateM.rd_val;
            x_rs2_data = stateW.rd_val;
          end
          if (m_rd_no == x_rs2_no && w_rd_no == x_rs1_no && x_rs1_no != x_rs2_no) begin
            mux_val_mx_wx = 8;
            x_rs2_data = stateM.rd_val;
            x_rs1_data = stateW.rd_val;
          end
        end
      end
    end

    add_cin = 1'b0;
    pcNext = 0;
    rd_temp = 32'd0;
    divisor = 32'b0;
    dividend = 32'b0;
    halt_sig_temp = 1'b0;
    branch_taken = 1'b0;
    illegal_insn = 1'b0;
    product = 64'b0;
    product_signed = 32'b0;
    product_final = 64'b0;
    add_a = $signed(x_rs1_data);
    add_b = $signed(x_rs2_data);

    case (insn_opcode_x)
      OpcodeMiscMem: begin
        if(stateX.exe_control.insn_fence) begin 
          //we = 1'b0;
        end else begin
          illegal_insn = 1'b1;
        end 
      end
      
      OpcodeEnviron: begin
            if(stateX.exe_control.insn_ecall) begin
              halt_sig_temp = 1'b1;
            end
        end

      OpcodeLui: begin
        if(stateX.rd_no == 5'b0)
          rd_temp = 32'b0;
        else begin
          rd_temp = {stateX.insn_imem[31:12], 12'd0};
        end
      end

      OpcodeJal: begin
        if (stateX.exe_control.insn_jal) begin
          rd_temp = stateX.pc + 32'd4;
          pcNext = stateX.pc + stateX.imm_i_sext_X;
          branch_taken = 1'b1;
        end 
        else begin 
          branch_taken = 1'b0;
        end
      end

      OpcodeJalr: begin
        if (stateX.exe_control.insn_jalr) begin 
          rd_temp = stateX.pc + 32'd4;
          pcNext = (($signed(x_rs1_data) + $signed(stateX.imm_i_sext_X)) & 32'hFFFFFFFE);
          branch_taken = 1'b1;
        end 
        else begin 
          branch_taken = 1'b0;
        end
      end 

      OpcodeBranch: begin
        if(stateX.exe_control.insn_beq) begin 
          if(x_rs1_data == x_rs2_data) begin 
            pcNext = stateX.pc + stateX.imm_i_sext_X;
            branch_taken = 1'b1;
          end
          else begin 
            branch_taken = 1'b0;
          end 
        end else
        if(stateX.exe_control.insn_bne)begin
          if (x_rs1_data != x_rs2_data) begin
            pcNext = stateX.pc + stateX.imm_i_sext_X;
            branch_taken = 1'b1;
            end
          else begin 
            branch_taken = 1'b0;
          end 
        end  
        else if(stateX.exe_control.insn_blt)begin 
          if($signed(x_rs1_data) < $signed(x_rs2_data)) begin
            pcNext = stateX.pc + stateX.imm_i_sext_X;
            branch_taken = 1'b1;
          end 
          else begin 
            branch_taken = 1'b0;
          end
        end
        else if(stateX.exe_control.insn_bge)begin 
          if($signed(x_rs1_data) >= $signed(x_rs2_data)) begin
            pcNext = stateX.pc + stateX.imm_i_sext_X;
            branch_taken = 1'b1;
          end
          else begin 
            branch_taken = 1'b0;
          end 
        end 
        else if(stateX.exe_control.insn_bltu)begin 
          if($signed(x_rs1_data) < $unsigned(x_rs2_data)) begin
            pcNext = stateX.pc + stateX.imm_i_sext_X;
            branch_taken = 1'b1;
          end
          else begin 
            branch_taken = 1'b0;
          end
        end
        else if(stateX.exe_control.insn_bgeu)begin 
          if($signed(x_rs1_data) >= $unsigned(x_rs2_data)) begin
            pcNext = stateX.pc + stateX.imm_i_sext_X;
            branch_taken = 1'b1;
          end
          else begin 
            branch_taken = 1'b0;
          end
        end      
      end 

      OpcodeRegImm: begin 
        if(stateX.exe_control.insn_addi) begin 
          add_cin = 1'b0;
          // we = 1'b1;
          add_a = x_rs1_data;
          add_b = stateX.imm_i_sext_X;
          rd_temp = add_sum;
        end
        else if (stateX.exe_control.insn_slti) begin 
          //     we = 1'b1; 
          rd_temp = ($signed(stateX.imm_i_sext_X) > $signed(x_rs1_data)) ? 32'b1 : 32'b0;
        end
        else if(stateX.exe_control.insn_sltiu) begin
          //     we = 1'b1;
          rd_temp = ($signed(x_rs1_data) < $unsigned(stateX.imm_i_sext_X)) ? 32'b1 : 32'b0;
        end  
        else if(stateX.exe_control.insn_xori) begin 
          //     we = 1'b1;
          rd_temp = $signed(x_rs1_data) ^ stateX.imm_i_sext_X;
        end 
        else if(stateX.exe_control.insn_ori) begin
          //     we = 1'b1;
          rd_temp = $signed(x_rs1_data) | stateX.imm_i_sext_X;
        end
        else if(stateX.exe_control.insn_andi) begin
          //     we = 1'b1;
          rd_temp = $signed(x_rs1_data) & stateX.imm_i_sext_X;
        end
        else if(stateX.exe_control.insn_slli) begin
          //     we = 1'b1;
          rd_temp = (x_rs1_data << (stateX.imm_i_sext_X[4:0]));
        end
        else if(stateX.exe_control.insn_srli) begin
          //     we = 1'b1;
          rd_temp = (x_rs1_data >> (stateX.imm_i_sext_X[4:0]));
        end
        else if(stateX.exe_control.insn_srai) begin
          //     we = 1'b1;
          rd_temp = ($signed(x_rs1_data) >>> (stateX.imm_i_sext_X[4:0]));
        end
        else begin 
          illegal_insn = 1'b1;
        end 
      end

      OpcodeRegReg: begin
        if(stateX.exe_control.insn_add) begin 
          add_cin = 1'b0;
          // we = 1'b1;
          add_a = x_rs1_data;
          add_b = x_rs2_data;
          rd_temp = add_sum;
        end
        else if(stateX.exe_control.insn_sub) begin 
          add_cin = 1'b1;
          // we = 1'b1;
          add_a = x_rs1_data;
          add_b = ~x_rs2_data;
          rd_temp = add_sum;
        end
        else if(stateX.exe_control.insn_sll) begin 
          // we = 1'b1;
          rd_temp = x_rs1_data << x_rs2_data[4:0];
        end
        else if(stateX.exe_control.insn_slt) begin  
          //   we = 1'b1;
          rd_temp = $signed(x_rs1_data) < $signed(x_rs2_data) ? 32'b1 : 32'b0;
        end
        else if(stateX.exe_control.insn_sltu) begin 
          //   we = 1'b1;
          rd_temp = (x_rs1_data < $unsigned(x_rs2_data))? 32'b1:32'b0;
        end
        else if(stateX.exe_control.insn_xor) begin 
          //   we = 1'b1;
          rd_temp = x_rs1_data ^ x_rs2_data;
        end
        else if(stateX.exe_control.insn_srl) begin 
          //   we = 1'b1;
          rd_temp = x_rs1_data >> (x_rs2_data[4:0]);
        end
        else if(stateX.exe_control.insn_sra) begin 
          //   we = 1'b1;
          rd_temp = $signed(x_rs1_data) >>> (x_rs2_data[4:0]);
        end
        else if(stateX.exe_control.insn_or) begin 
          //   we = 1'b1;
          rd_temp = x_rs1_data | x_rs2_data;
        end
        else if(stateX.exe_control.insn_and) begin 
          //   we = 1'b1;
          rd_temp = x_rs1_data & x_rs2_data;
        end
        else if(stateX.exe_control.insn_mul) begin 
          product = x_rs1_data * x_rs2_data;
          rd_temp = product[31:0];
        end 
        else if(stateX.exe_control.insn_mulh) begin 
          product = ($signed(x_rs1_data) * $signed(x_rs2_data));
          rd_temp = product[63:32];
        end  
        else if(stateX.exe_control.insn_mulhsu) begin
          if (x_rs1_data[31] == 1'b1) begin
            product_signed = ~(x_rs1_data) + 32'b1;
          end else begin
            product_signed = x_rs1_data;
          end

          product = product_signed * x_rs2_data;

          if (x_rs1_data[31] == 1'b1) begin
            product_final = ~product + 64'b1;
          end else begin
            product_final = product;
          end
          rd_temp = product_final[63:32];             
        end
        else if(stateX.exe_control.insn_mulhu)begin 
          product = ($unsigned(x_rs1_data) *  $unsigned(x_rs2_data));
          rd_temp = product[63:32];
        end
        else if(stateX.exe_control.insn_div)begin 
          
          dividend = x_rs1_data[31] ? (~x_rs1_data + 1) : x_rs1_data;
          divisor = x_rs2_data[31] ? (~x_rs2_data + 1) : x_rs2_data;
          rd_temp = (x_rs1_data == 0 | x_rs2_data == 0) ? $signed(32'hFFFFFFFF) : ((div_rs1 != div_rs2) ? (~quotient + 1) : quotient); 

        end
        else if(stateX.exe_control.insn_divu)begin 
          dividend = $unsigned(x_rs1_data);
          divisor = $unsigned(x_rs2_data);
          rd_temp = (x_rs1_data == 0 | x_rs2_data == 0) ? $signed(32'hFFFFFFFF) : quotient;
        end
       
        else if (stateX.exe_control.insn_rem)begin 
          dividend = x_rs1_data[31] ? (~x_rs1_data + 1) : x_rs1_data;
          divisor = x_rs2_data[31] ? (~x_rs2_data + 1) : x_rs2_data;
          rd_temp = (x_rs1_data == 0 | x_rs2_data == 0) ? x_rs1_data[31] ? (~x_rs1_data + 1) : x_rs1_data :
                                                                            (x_rs1_data[31] == 1'b1)?(~remainder + 1):(remainder);
        end 
        else if(stateX.exe_control.insn_remu)begin
          dividend = $unsigned(x_rs1_data);
          divisor =  $unsigned(x_rs2_data);
          rd_temp = remainder;
        end  
        else begin 
          illegal_insn = 1'b1;
        end
      end

      OpcodeStore: begin
        addr_to_dmem_temp =  ((stateM.insn_opcode == OpcodeLoad)&&
                             (stateX.rs1_no == stateM.rd_no))?(rd_val_temp + stateX.imm_i_sext_X):(stateX.rs1_data_temp+stateX.imm_i_sext_X);
      end

      OpcodeLoad: begin
        addr_to_dmem_temp = stateX.rs1_data_temp + stateX.imm_i_sext_X;
      end

      default: begin
        illegal_insn = 1'b1;
      end 
    endcase
  end

      // Rest of the code remains unchanged
  // end


  /****************/
  /* MEMORY STAGE */
  /****************/
  stage_memory_t stateM;
  logic [31:0] rd_val_temp;//Temporary variable to store the value to be written to the register file in memory stage
  logic [31:0]stateM_store_data_to_dmem;
  logic [3:0]stateM_store_we_to_dmem; 
  assign addr_to_dmem = stateM.addr_to_dmem&32'hFFFFFFFC;

  always_ff @(posedge clk) begin
    if (rst) begin
      stateM <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        rd_no: 0,
        rd_val: 0,
        rs1_no: 0,
        rs1_data_temp: 0,
        rs2_no: 0,
        rs2_data_temp: 0,
        addr_to_dmem: 0,
        store_we_to_dmem: 0,
        store_data_to_dmem: 0,
        insn_opcode: 0,
        halt_sig: 0,
        branch_taken: 0,
        pcNext: 0,
        mem_control: '{default:0}
      };
    end else begin
      begin
          stateM <= '{
            pc: stateX.pc,
            insn: stateX.insn,
            cycle_status: stateX.cycle_status,
            rd_no: stateX.rd_no,
            rd_val: rd_temp,
            rs1_no: stateX.rs1_no,
            rs1_data_temp:x_rs1_data,
            rs2_no: stateX.rs2_no,
            rs2_data_temp: ((stateW.insn_opcode == OpcodeLoad) && //WM bypass
                            (stateM.insn_opcode == OpcodeStore)&&
                            (stateW.rd_no == stateM.rs2_no))?stateW.rd_val:x_rs2_data,
            addr_to_dmem: ((stateM.insn_opcode == OpcodeLoad)||
                           (stateM.insn_opcode == OpcodeStore))?addr_to_dmem_temp:stateX.addr_to_dmem,
            store_we_to_dmem: stateX.store_we_to_dmem,
            store_data_to_dmem: stateX.store_data_to_dmem,
            insn_opcode: stateX.insn_opcode,
            halt_sig: halt_sig_temp,
            branch_taken: branch_taken,
            pcNext: pcNext,
            mem_control: stateX.exe_control
          };
      end
    end
    
  end
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_1memory (
      .insn  (stateM.insn),
      .disasm(m_disasm)
  );

  always_latch begin
  
    if(stateM.insn_opcode == OpcodeLoad) begin
      if(stateM.mem_control.insn_lb) begin
        if(stateM.addr_to_dmem[1:0] == 2'b00)
          rd_val_temp = 32'(signed'(load_data_from_dmem[7:0]));
        else if(stateM.addr_to_dmem[1:0] == 2'b01)
          rd_val_temp =32'(signed'( load_data_from_dmem[15:8]));
        else if(stateM.addr_to_dmem[1:0] == 2'b10)
          rd_val_temp = 32'(signed'(load_data_from_dmem[23:16]));
        else if(stateM.addr_to_dmem[1:0] == 2'b11)
          rd_val_temp = 32'(signed'(load_data_from_dmem[31:24]));
      end
      else if(stateM.mem_control.insn_lbu) begin
        if(stateM.addr_to_dmem[1:0] == 2'b00)
          rd_val_temp = 32'(unsigned'(load_data_from_dmem[7:0]));
        else if(stateM.addr_to_dmem[1:0] == 2'b01)
          rd_val_temp = 32'(unsigned'(load_data_from_dmem[15:8]));
        else if(stateM.addr_to_dmem[1:0] == 2'b10)
          rd_val_temp = 32'(unsigned'(load_data_from_dmem[23:16]));
        else if(stateM.addr_to_dmem[1:0] == 2'b11)
          rd_val_temp = 32'(unsigned'(load_data_from_dmem[31:24]));
      end
      else if(stateM.mem_control.insn_lh) begin
        if(stateM.addr_to_dmem[1:0] == 2'b00)
          rd_val_temp = 32'(signed'(load_data_from_dmem[15:0]));
        else if(stateM.addr_to_dmem[1:0] == 2'b10)
          rd_val_temp = 32'(signed'(load_data_from_dmem[31:16]));
      end
      else if(stateM.mem_control.insn_lhu) begin
        if(stateM.addr_to_dmem[1:0] == 2'b00)
          rd_val_temp = 32'(unsigned'(load_data_from_dmem[15:0]));
        else if(stateM.addr_to_dmem[1:0] == 2'b10)
          rd_val_temp = 32'(unsigned'(load_data_from_dmem[31:16]));
      end
      else if(stateM.mem_control.insn_lw) begin
        rd_val_temp = load_data_from_dmem;
      end
    end

    else if(stateM.insn_opcode == OpcodeStore) begin
      if(stateM.mem_control.insn_sb) begin
        if(stateM.addr_to_dmem[1:0] == 2'b00) begin
          stateM_store_data_to_dmem[7:0] =  ((stateW.insn_opcode == OpcodeLoad)&&(stateW.rd_no == stateM.rs2_no))?rd_val_temp[7:0]:stateM.rs2_data_temp[7:0];
          stateM_store_we_to_dmem = 4'b0001;
        end
        else if(stateM.addr_to_dmem[1:0] == 2'b01) begin
          stateM_store_data_to_dmem[15:8] =  ((stateW.insn_opcode == OpcodeLoad)&&(stateW.rd_no == stateM.rs2_no))?rd_val_temp[7:0]:stateM.rs2_data_temp[7:0];
          stateM_store_we_to_dmem = 4'b0010;
        end
        else if(stateM.addr_to_dmem[1:0] == 2'b10) begin
          stateM_store_data_to_dmem[23:16] =  ((stateW.insn_opcode == OpcodeLoad)&&(stateW.rd_no == stateM.rs2_no))?rd_val_temp[7:0]:stateM.rs2_data_temp[7:0];
          stateM_store_we_to_dmem = 4'b0100;
        end
        else if(stateM.addr_to_dmem[1:0] == 2'b11) begin
          stateM_store_data_to_dmem[31:24] = ((stateW.insn_opcode == OpcodeLoad)&&(stateW.rd_no == stateM.rs2_no))?rd_val_temp[7:0]:stateM.rs2_data_temp[7:0];
          stateM_store_we_to_dmem = 4'b1000;
        end

      end
      else if(stateM.mem_control.insn_sh) begin
        if(stateM.addr_to_dmem[1:0] == 2'b00) begin
          stateM_store_data_to_dmem[15:0] =  ((stateW.insn_opcode == OpcodeLoad)&&(stateW.rd_no == stateM.rs2_no))?rd_val_temp[15:0]:stateM.rs2_data_temp[15:0];
          stateM_store_we_to_dmem = 4'b0011;
        end
        else if(stateM.addr_to_dmem[1:0] == 2'b10) begin
          stateM_store_data_to_dmem[31:16] =  ((stateW.insn_opcode == OpcodeLoad)&&(stateW.rd_no == stateM.rs2_no))?rd_val_temp[15:0]:stateM.rs2_data_temp[15:0];
          stateM_store_we_to_dmem = 4'b1100;
        end
      end
      else if(stateM.mem_control.insn_sw) begin
        stateM_store_data_to_dmem =  ((stateW.insn_opcode == OpcodeLoad)&&(stateW.rd_no == stateM.rs2_no))?rd_val_temp:stateM.rs2_data_temp;
        stateM_store_we_to_dmem = 4'b1111;
      end
    end
  end
  

  /****************/
  /* WRITEBACK STAGE */
  /****************/

  stage_write_t stateW;
  always_ff @(posedge clk) begin
    if (rst) begin
      stateW <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        rd_no: 0,
        rd_val: 0,
        rs1_no: 0,
        rs1_data_temp: 0,
        rs2_no: 0,
        rs2_data_temp: 0,
        insn_opcode: 0,
        halt_sig: 0,
        store_data_to_dmem:'{default:0},
        store_we_to_dmem:'{default:0}
      };
    end else begin
      begin
        stateW <= '{
          pc: stateM.pc,
          insn: stateM.insn,
          cycle_status: stateM.cycle_status,
          rd_no: stateM.rd_no,
          rd_val: (stateM.insn_opcode == OpcodeLoad)?rd_val_temp:stateM.rd_val,
          rs1_no: stateM.rs1_no,
          rs1_data_temp: stateM.rs1_data_temp,
          rs2_no: stateM.rs2_no,
          rs2_data_temp: stateM.rs2_data_temp,
          insn_opcode: stateM.insn_opcode,
          halt_sig: stateM.halt_sig,
          store_data_to_dmem: stateM_store_data_to_dmem,
          store_we_to_dmem: stateM_store_we_to_dmem
        };
      end
    end
  end

  wire [255:0] wb_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_1writeback (
      .insn  (stateW.insn),
      .disasm(wb_disasm)
  );
  assign store_data_to_dmem = stateW.store_data_to_dmem;
  assign store_we_to_dmem = stateW.store_we_to_dmem;
  assign we = (stateW.insn_opcode == OpcodeBranch ||
                  stateW.insn_opcode == OpcodeStore) ||
                  (stateW.rd_no == 0)? 1'b0 : 1'b1;//If not store or branch or rd_no is 0, we = 1
  assign halt = stateW.halt_sig;

  assign trace_writeback_cycle_status = stateW.cycle_status;
  assign trace_writeback_pc = stateW.pc;
  assign trace_writeback_insn = stateW.insn;
endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem[NUM_WORDS];

  initial begin
    $readmemh("mem_initial_contents.hex", mem, 0);
  end

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input  wire  clk,
    input  wire  rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
