`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`include "../hw2a/divider_unsigned.sv"
`include "../hw2b/cla.sv"

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];
  integer i;

  // TODO: your code here
  assign regs[0] = 32'd0; // x0 is always zero
  assign rs1_data = regs[rs1]; // 1st read port
  assign rs2_data = regs[rs2]; // 2nd read port

  always_ff @(posedge clk) begin
    if (rst == 1'b1) begin
      for (i=0; i < NumRegs; i++) begin
        regs[i] <= 32'd0;
      end
    end else begin
      if ((we==1'b1) && (rd != 5'd0)) begin // if read and write happen at once
        regs[rd] <= rd_data;
      end
    end
  end
endmodule

module DatapathSingleCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output wire [`REG_SIZE] addr_to_dmem,
    input logic [`REG_SIZE] load_data_from_dmem,
    output wire [`REG_SIZE] store_data_to_dmem,
    output wire [3:0] store_we_to_dmem
);

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [ 4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;

  // edited: user added
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;
  localparam bit [`OPCODE_SIZE] OpI = 7'b0010011;
  localparam bit [`OPCODE_SIZE] OpR = 7'b0110011;
  localparam bit [`OPCODE_SIZE] OpU = 7'b01_101_11;
  localparam bit [`OPCODE_SIZE] Opecall = 7'b1110011;

  wire insn_lui = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal = insn_opcode == OpJal;
  wire insn_jalr = insn_opcode == OpJalr;

  wire insn_beq = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;

  wire insn_add = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_sll = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_slt = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010 && insn_from_imem[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011 && insn_from_imem[31:25] == 7'd0;
  wire insn_xor = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100 && insn_from_imem[31:25] == 7'd0;
  wire insn_srl = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_or = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110 && insn_from_imem[31:25] == 7'd0;
  wire insn_and = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111 && insn_from_imem[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  // synthesis translate_off
  // this code is only for simulation, not synthesis
  `include "RvDisassembler.sv"
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn_from_imem);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic...
  wire [(8*32)-1:0] disasm_wire;
  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_disasm
    assign disasm_wire[(((i+1))*8)-1:((i)*8)] = disasm_string[31-i];
  end
  // synthesis translate_on

  // program counter
  logic [`REG_SIZE] pcNext, pcCurrent;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      pcCurrent <= pcNext;
    end
  end
  assign pc_to_imem = pcCurrent;

  // cycle/insn_from_imem counters
  logic [`REG_SIZE] cycles_current, num_insns_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_insns_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst) begin
        num_insns_current <= num_insns_current + 1;
      end
    end
  end

  logic illegal_insn;

  // extra wires for rs1_data and rs1_data
  logic [`REG_SIZE] rs1_data_temp;
  logic [`REG_SIZE] rs2_data_temp;
  logic we_lui;
  logic [`REG_SIZE] rd_data;
  logic [`REG_SIZE]  alu_a, alu_b;
  logic alu_cin;
  logic [`REG_SIZE] alu_sum;
  logic [`REG_SIZE] pc_inc;
  logic [63:0] mult_res;
  logic [31:0] mult_res_signed;
  logic [63:0] mult_res_store;

  logic [31:0] i_dividend_temp;
  logic [31:0] i_divisor_temp;
  logic [31:0] o_remainder_temp;
  logic [31:0] o_quotient_temp;
  logic [31:0] address_bits;
  logic temp_rs1;
  logic temp_rs2;
  logic is_zero;

  logic branch_taken;

  RegFile rf(.rd(insn_rd), .rd_data(rd_data), .rs1(insn_rs1), .rs1_data(rs1_data_temp), 
    .rs2(insn_rs2), .rs2_data(rs2_data_temp), .clk(clk), .we(we_lui) , .rst(rst));

  cla alu (.a(alu_a), .b(alu_b), .cin(alu_cin), .sum(alu_sum));

  divider_unsigned div(.i_dividend(i_dividend_temp),
    .i_divisor(i_divisor_temp), .o_quotient(o_quotient_temp),
    .o_remainder(o_remainder_temp));

  always_comb begin
  // always_ff @(posedge clk) begin
  // Using always ff doesn't work where there are subsequent 
  // instructions to be run. 

    illegal_insn = 1'b0;
    halt = 1'b0;  // edited: most of one riscv tests are failing if this line is removed
    we_lui = 1'b0;
    alu_cin = 1'b0;
    branch_taken = 1'b0;
    address_bits = 32'h0;
    store_we_to_dmem = 4'b0000;

    if (insn_fence == 1'b1) begin

    end

    // More than 4 cases give me some error.
    if (insn_bne == 1'b1) begin
      pc_inc = (rs1_data_temp != rs2_data_temp) ? imm_b_sext: 32'd4;
    end else if (insn_beq == 1'b1) begin
      pc_inc = (rs1_data_temp == rs2_data_temp) ? imm_b_sext : 32'd4;
    end else if (insn_blt == 1'b1) begin
      pc_inc = ($signed(rs1_data_temp) < $signed(rs2_data_temp)) ? imm_b_sext : 32'd4;
    end else if (insn_bge == 1'b1) begin
      pc_inc = ($signed(rs1_data_temp) >= $signed(rs2_data_temp)) ? imm_b_sext : 32'd4;
    end else if (insn_bltu == 1'b1) begin
      pc_inc = ($signed(rs1_data_temp) < $unsigned(rs2_data_temp)) ? imm_b_sext : 32'd4;
    end else if (insn_bgeu == 1'b1) begin
      pc_inc = ($signed(rs1_data_temp) >= $unsigned(rs2_data_temp)) ? imm_b_sext : 32'd4;
    end else begin
      pc_inc = 32'd4;
    end

    if (insn_ecall == 1'b1) begin
      halt = 1'b1;
    end

    if (insn_jal == 1'b1) begin
      we_lui = 1'b1;
      rd_data = pcCurrent + 32'd4;
      pc_inc = imm_j_sext;
      pcNext = pcCurrent + pc_inc;
      branch_taken = 1'b1;
    end else if (insn_jalr == 1'b1) begin
      we_lui = 1'b1;
      rd_data = pcCurrent + 32'd4;
      pc_inc = (rs1_data_temp + imm_i_sext) & 32'hFFFFFFFE;
      pcNext = pcCurrent + pc_inc;
      branch_taken = 1'b1;
    end

    // only works here not sure why
    // can't put it inside the case.
    if (insn_auipc == 1'b1) begin  
        we_lui = 1'b1;
        rd_data = pcCurrent + {insn_from_imem[31:12], 12'd0};
    end

    if (insn_lb | insn_lh | insn_lbu | insn_lhu | insn_lw) begin
      address_bits = (rs1_data_temp + imm_i_sext);
      addr_to_dmem = (address_bits) & 32'hFFFF_FFFC;
    end else if (insn_sb | insn_sw | insn_sh) begin
      address_bits = (rs1_data_temp + imm_s_sext);
      addr_to_dmem = (address_bits) & 32'hFFFF_FFFC;
    end

    // Not sure why it doesn't work inside the case statement.
    // mostly because the opcode is different even if the 
    // the statement is I type.
    if (insn_lb == 1'b1) begin
      we_lui = 1'b1;
      if (address_bits[1:0] == 2'b00) begin
        rd_data = {{24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]};
      end else if (address_bits[1:0] == 2'b01) begin
        rd_data = {{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
      end else if (address_bits[1:0] == 2'b10) begin
        rd_data = {{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
      end else begin
        rd_data = {{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
      end
    end else if (insn_lh == 1'b1) begin
      we_lui = 1'b1;
      if (address_bits[1:0] == 2'b00) begin
        rd_data = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
      end else begin
        rd_data = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
      end
    end else if (insn_lw == 1'b1) begin
        we_lui = 1'b1;
        rd_data = load_data_from_dmem[31:0];
    end else if (insn_lbu == 1'b1) begin
      we_lui = 1'b1;
      if (address_bits[1:0] == 2'b00) begin
        rd_data = {{24{1'b0}}, load_data_from_dmem[7:0]};
      end else if (address_bits[1:0] == 2'b01) begin
        rd_data = {{24{1'b0}}, load_data_from_dmem[15:8]};
      end else if (address_bits[1:0] == 2'b10) begin
        rd_data = {{24{1'b0}}, load_data_from_dmem[23:16]};
      end else begin
        rd_data = {{24{1'b0}}, load_data_from_dmem[31:24]};
      end
    end else if (insn_lhu == 1'b1) begin
      we_lui = 1'b1;
      if (address_bits[1:0] == 2'b00) begin
        rd_data = {{16{1'b0}}, load_data_from_dmem[15:0]};
      end else begin
        rd_data = {{16{1'b0}}, load_data_from_dmem[31:16]};
      end
    end

    if (insn_sb == 1'b1) begin
      we_lui = 1'b0;
      if (address_bits[1:0] == 2'b00) begin
        store_we_to_dmem = 4'b0001;
        store_data_to_dmem[7:0] = rs2_data_temp[7:0];
      end else if (address_bits[1:0] == 2'b01) begin
        store_we_to_dmem = 4'b0010;
        store_data_to_dmem[15:8] = rs2_data_temp[7:0];
      end else if (address_bits[1:0] == 2'b10) begin
        store_we_to_dmem = 4'b0100;
        store_data_to_dmem [23:16]= rs2_data_temp[7:0];
      end else begin
        store_we_to_dmem = 4'b1000;
        store_data_to_dmem[31:24] = rs2_data_temp[7:0];
      end
    end else if (insn_sh == 1'b1) begin
      we_lui = 1'b0;
      if (address_bits[1:0] == 2'b00) begin
        store_we_to_dmem = 4'b0011;
        store_data_to_dmem [15:0]= rs2_data_temp[15:0];
       end else begin
        store_we_to_dmem = 4'b1100;
        store_data_to_dmem [31:16] = rs2_data_temp[15:0];
       end
    end else if (insn_sw == 1'b1) begin
      we_lui = 1'b0;
      store_we_to_dmem = 4'b1111;
      store_data_to_dmem = rs2_data_temp;
    end

    case (insn_opcode)
      OpU : begin
        we_lui = 1'b1;

        if (insn_lui == 1'b1) begin
          if (insn_rd == 5'b0) begin
            rd_data = 32'b0;
          end else begin
            rd_data = {insn_from_imem[31:12], 12'd0};
          end
        end

      end

      OpI : begin
        we_lui = 1'b1;
      
        if (insn_addi == 1'b1) begin  // Addi
          alu_cin = 1'b0;
          alu_a = rs1_data_temp;
          alu_b = imm_i_sext;
          rd_data = alu_sum;
        end 
        
        if (insn_slti == 1'b1) begin  //slti have doubt if I have use sign
          rd_data = $signed(rs1_data_temp) < $signed(imm_i_sext) ? 32'b1 : 32'b0;
        end else if (insn_sltiu == 1'b1) begin
          //we_lui = 1'b1;  // write signal is working properly. if not set properly fails test
          rd_data = $signed(rs1_data_temp) < $unsigned(imm_i_sext) ? 32'b1 : 32'b0;
        end

        if (insn_xori == 1'b1) begin  // xori
          //we_lui = 1'b1;
          rd_data = $signed(rs1_data_temp) ^ imm_i_sext;
        end

        if (insn_ori == 1'b1) begin  // ori
          //we_lui = 1'b1;
          rd_data = $signed(rs1_data_temp) | imm_i_sext;
        end

        if (insn_andi == 1'b1) begin  // andi
          //we_lui = 1'b1;
          rd_data = $signed(rs1_data_temp) & imm_i_sext;
        end

        if (insn_slli == 1'b1) begin  // slli not sure about using shamt
          //we_lui = 1'b1;
          rd_data = rs1_data_temp << imm_shamt;
        end else if (insn_srli == 1'b1) begin
          //we_lui = 1'b1;
          rd_data = rs1_data_temp >> imm_shamt;
        end
        
        if (insn_srai == 1'b1) begin
          //we_lui = 1'b1;
          rd_data = $signed(rs1_data_temp) >>> imm_shamt;
        end
      end

      OpR : begin
        we_lui = 1'b1;

        if (insn_add == 1'b1) begin
          alu_cin = 1'b0;
          //we_lui = 1'b1;
          alu_a = rs1_data_temp;
          alu_b = rs2_data_temp;
          rd_data = alu_sum;
        end

        if (insn_sub == 1'b1) begin
          //we_lui = 1'b1;
          //rd_data = rs1_data_temp - rs2_data_temp;
          alu_cin = 1'b1;
          //we_lui = 1'b1;
          alu_a = rs1_data_temp;
          alu_b = ~rs2_data_temp;
          rd_data = alu_sum;
        end

        if (insn_sll == 1'b1) begin
          //we_lui = 1'b1;
          rd_data = rs1_data_temp << rs2_data_temp[4:0];
        end

        if (insn_slt == 1'b1) begin
          //we_lui = 1'b1;
          rd_data = $signed(rs1_data_temp) < $signed(rs2_data_temp) ? 32'b1 : 32'b0;
        end else if (insn_sltu == 1'b1) begin
          //we_lui = 1'b1;
          rd_data = rs1_data_temp < $unsigned(rs2_data_temp) ? 32'b1 : 32'b0;
        end

        if (insn_xor == 1'b1) begin
          //we_lui = 1'b1;
          rd_data = rs1_data_temp ^ rs2_data_temp;
        end

        if (insn_srl == 1'b1) begin
          //we_lui = 1'b1;
          rd_data = rs1_data_temp >> (rs2_data_temp[4:0]);
        end
        
        if (insn_sra == 1'b1) begin
          //we_lui = 1'b1;
          rd_data = $signed(rs1_data_temp) >>> rs2_data_temp[4:0];
        end

        if (insn_or == 1'b1) begin
          //we_lui = 1'b1;
          rd_data = rs1_data_temp | rs2_data_temp;
        end

        if (insn_and == 1'b1) begin
          //we_lui = 1'b1;
          rd_data = rs1_data_temp & rs2_data_temp;
        end

        if (insn_mul == 1'b1) begin
          mult_res = rs1_data_temp * rs2_data_temp;
          rd_data = mult_res[31:0];
        end else if (insn_mulh == 1'b1) begin
          mult_res = $signed(rs1_data_temp) * $signed(rs2_data_temp);
          rd_data = mult_res[63:32];
        end else if (insn_mulhsu == 1'b1) begin
          if (rs1_data_temp[31] == 1'b1) begin
            mult_res_signed = ~(rs1_data_temp) + 32'b1;
          end else begin
            mult_res_signed = rs1_data_temp;
          end

          mult_res = mult_res_signed * rs2_data_temp;

          if (rs1_data_temp[31] == 1'b1) begin
            mult_res_store = ~mult_res + 64'b1;
          end else begin
            mult_res_store = mult_res;
          end
          rd_data = mult_res_store[63:32];
        end else if (insn_mulhu == 1'b1) begin
          mult_res = $unsigned(rs1_data_temp) * $unsigned(rs2_data_temp);
          rd_data = mult_res[63:32];
        end

        if (insn_div == 1'b1) begin
          temp_rs1 = rs1_data_temp[31];
          temp_rs2 = rs2_data_temp[31]; // it's better if I do this inside the module
          is_zero = (rs1_data_temp == 0) | (rs2_data_temp == 0)  ;
          i_dividend_temp = rs1_data_temp[31] ? (~rs1_data_temp + 1) : rs1_data_temp;
          i_divisor_temp = rs2_data_temp[31] ? (~rs2_data_temp + 1) : rs2_data_temp;
          // need check for zero condition
          rd_data = is_zero ? $signed(32'hFFFFFFFF) : ((temp_rs1 != temp_rs2) ? (~o_quotient_temp + 1) : o_quotient_temp); 
        end else if (insn_divu == 1'b1) begin
          i_dividend_temp = $unsigned(rs1_data_temp);
          i_divisor_temp = $unsigned(rs2_data_temp);
          rd_data = o_quotient_temp;
        end else if (insn_rem == 1'b1) begin
          temp_rs1 = rs1_data_temp[31];
          temp_rs2 = rs2_data_temp[31]; // it's better if I do this inside the module
          is_zero = (rs1_data_temp == 0) | (rs2_data_temp == 0)  ;
          i_dividend_temp = rs1_data_temp[31] ? (~rs1_data_temp + 1) : rs1_data_temp;
          i_divisor_temp = rs2_data_temp[31] ? (~rs2_data_temp + 1) : rs2_data_temp;
          // Determine if adjustment for signs is necessary
          if (!is_zero && (temp_rs1 == 1'b1)) begin
              // Adjust remainder sign to dividend
              rd_data = ~o_remainder_temp + 1;
          end else begin
              rd_data = o_remainder_temp;
          end
        end else if (insn_remu == 1'b1) begin
          i_dividend_temp = $unsigned(rs1_data_temp);
          i_divisor_temp = $unsigned(rs2_data_temp);
          rd_data = o_remainder_temp;
        end

      end

      default: begin
        illegal_insn = 1'b1;
      end
    endcase

    if (branch_taken == 1'b0) begin
      pcNext = pcCurrent + pc_inc;
    end
  
  end

  //pcNext = pcCurrent + 32'd4; doesn't work here

endmodule

/* A memory module that supports 1-cycle reads and writes, with one read-only port
 * and one read+write port.
 */
module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. See RiscvProcessor for clock details.
    input wire clock_mem,

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

  always @(posedge clock_mem) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clock_mem) begin
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

/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

        ____
 proc: |    |______
           ____
 mem:  ___|    |___
*/
module RiscvProcessor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) mem (
      .rst      (rst),
      .clock_mem (clock_mem),
      // imem is read-only
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      // dmem is read-write
      .addr_to_dmem(mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem  (mem_data_we)
  );

  DatapathSingleCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );

endmodule
