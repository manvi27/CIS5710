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

  // TODO: your code here

  assign regs[0] = 32'd0;
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];
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

  logic [31:0] add_bits;

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;
  logic [`REG_SIZE] rs1_data, rs2_data, rd_data;
  logic we;
//instance for regfile in datapath
  RegFile rf(
    .clk(clk), .rst(rst),  .we(we), .rd(insn_rd), .rd_data(rd_data),
    .rs1(insn_rs1), .rs2(insn_rs2), .rs1_data(rs1_data),  .rs2_data(rs2_data)
  );
  //instance for divider in datapath
  logic [31:0] dividend, divisor, remainder, quotient;
  logic zero_check, rs1, rs2;
  divider_unsigned divu(
    .i_dividend(dividend), .i_divisor(divisor), .o_remainder(remainder), .o_quotient(quotient)
  );
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
  logic [`REG_SIZE] pcNext, pcCurrent, pcTemp;
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
  // logic [`REG_SIZE] rs1_data;
  // logic [`REG_SIZE] rs2_data;
  // logic we;
  // logic [`REG_SIZE] rd_data;
  logic [`REG_SIZE]  add_a, add_b;
  logic add_cin;
  logic [`REG_SIZE] add_sum;

  logic [63:0] product;
  logic [31:0] product_signed;
  logic [63:0] product_final;
  logic [31:0] addr;
  logic branch;
  // RegFile rf(.rd(insn_rd), .rd_data(rd_data), .rs1(insn_rs1), .rs1_data(rs1_data), 
  //   .rs2(insn_rs2), .rs2_data(rs2_data), .clk(clk), .we(we) , .rst(rst));

  cla add (.a(add_a), .b(add_b), .cin(add_cin), .sum(add_sum));

    always_comb begin
    illegal_insn = 1'b0;
    halt = 1'b0;
    we = 1'b0;
    add_cin = 1'b0;
    branch = 1'b0;
    addr = 32'h0;
    store_we_to_dmem = 4'b0000;

    if (insn_fence == 1'b1) begin
      // halt = 1'b1;
      illegal_insn = 1'b0;
      we = 1'b0;
    end

    if (insn_bne == 1'b1) begin
      pcTemp = (rs1_data != rs2_data) ? imm_b_sext: 32'd4;
    end else if (insn_beq == 1'b1) begin
      pcTemp = (rs1_data == rs2_data) ? imm_b_sext : 32'd4;
    end else if (insn_blt == 1'b1) begin
      pcTemp = ($signed(rs1_data) < $signed(rs2_data)) ? imm_b_sext : 32'd4;
    end else if (insn_bge == 1'b1) begin
      pcTemp = ($signed(rs1_data) >= $signed(rs2_data)) ? imm_b_sext : 32'd4;
    end else if (insn_bltu == 1'b1) begin
      pcTemp = ($signed(rs1_data) < $unsigned(rs2_data)) ? imm_b_sext : 32'd4;
    end else if (insn_bgeu == 1'b1) begin
      pcTemp = ($signed(rs1_data) >= $unsigned(rs2_data)) ? imm_b_sext : 32'd4;
    end else begin
      pcTemp = 32'd4;
    end

    if (insn_ecall == 1'b1) begin
      halt = 1'b1;
      illegal_insn = 1'b0;
      we = 1'b0;
    end
  
    else if(OpStore == insn_opcode) begin
      halt = 1'b0;
      illegal_insn = 1'b0;
      add_bits = (rs1_data + imm_s_sext);
      addr_to_dmem = add_bits & 32'hFFFFFFFC;
      we = 1'b0;
      if(insn_sb) begin
        if(add_bits[1:0] == 2'b00) begin
          store_data_to_dmem[7:0] = rs2_data[7:0];
          store_we_to_dmem = 4'b0001;
        end
        else if(add_bits[1:0] == 2'b01) begin
          store_data_to_dmem[15:8] = rs2_data[7:0];
          store_we_to_dmem = 4'b0010;
        end
        else if(add_bits[1:0] == 2'b10) begin
          store_data_to_dmem[23:16] = rs2_data[7:0];
          store_we_to_dmem = 4'b0100;
        end
        else if(add_bits[1:0] == 2'b11) begin
          store_data_to_dmem[31:24] = rs2_data[7:0];
          store_we_to_dmem = 4'b1000;
        end
      end
      else if(insn_sh) begin
        if(add_bits[1:0] == 2'b00) begin
          store_data_to_dmem[15:0] = rs2_data[15:0];
          store_we_to_dmem = 4'b0011;
        end
        else if(add_bits[1:0] == 2'b10) begin
          store_data_to_dmem[31:16] = rs2_data[15:0];
          store_we_to_dmem = 4'b1100;
        end
      end
      else if(insn_sw) begin
        store_data_to_dmem = rs2_data;
        store_we_to_dmem = 4'b1111;
      end
    end
    else if(OpLoad == insn_opcode)
    begin
      addr = (rs1_data + imm_i_sext);
      addr_to_dmem = (addr)&32'hFFFFFFFC;
      we = 1'b1;
      halt = 1'b0;
      illegal_insn = 1'b0;
      if(insn_lb == 1'b1)
      begin
        if(addr[1:0] == 2'b00) begin
          rd_data = 32'(signed'(load_data_from_dmem[7:0]));
        end
        else if(addr[1:0] == 2'b01) begin
          rd_data = 32'(signed'(load_data_from_dmem[15:8]));
        end
        else if(addr[1:0] == 2'b10) begin
          rd_data = 32'(signed'(load_data_from_dmem[23:16]));
        end
        else if(addr[1:0] == 2'b11) begin
          rd_data = 32'(signed'(load_data_from_dmem[31:24]));
        end
      end
      else if(insn_lbu == 1'b1)
      begin
       if(addr[1:0] == 2'b00) begin
          rd_data = 32'(unsigned'(load_data_from_dmem[7:0]));
        end
        else if(addr[1:0] == 2'b01) begin
          rd_data = 32'(unsigned'(load_data_from_dmem[15:8]));
        end
        else if(addr[1:0] == 2'b10) begin
          rd_data = 32'(unsigned'(load_data_from_dmem[23:16]));
        end
        else if(addr[1:0] == 2'b11) begin
          rd_data = 32'(unsigned'(load_data_from_dmem[31:24]));
        end
      end
      else if(insn_lh == 1'b1)
      begin
        if(addr[1:0] == 2'b00) begin
          rd_data = 32'(signed'(load_data_from_dmem[15:0]));
        end
        else if(addr[1:0] == 2'b10) begin
          rd_data = 32'(signed'(load_data_from_dmem[31:16]));
        end
      end
      else if(insn_lhu == 1'b1)
      begin
        if(addr[1:0] == 2'b00) begin
          rd_data = 32'(unsigned'(load_data_from_dmem[15:0]));
        end
        else if(addr[1:0] == 2'b10) begin
          rd_data = 32'(unsigned'(load_data_from_dmem[31:16]));
        end
      end
      else if(insn_lw == 1'b1)
      begin
        rd_data = load_data_from_dmem;
      end
    end

    else if(insn_jal == 1'b1)
    begin
      we = 1'b1;
      halt = 1'b0;
      pcTemp = imm_j_sext;
      rd_data = pcCurrent + 4;
    end
    if(insn_jalr == 1'b1)
    begin
      we = 1'b1;
      halt = 1'b0;
      rd_data = pcCurrent + 4;
      pcTemp = rs1_data +imm_i_sext - pcCurrent;
    end
    if(insn_auipc)
    begin
      we = 1'b1;
      halt = 1'b0;
      rd_data = pcCurrent + {insn_from_imem[31:12],12'd0};
    end
    case (insn_opcode)
      OpLui : begin
        we = 1'b1;
        rd_data[31:12] = insn_from_imem[31:12];
        rd_data[11:0] = 12'd0;
      end

      OpRegImm : begin
        if (insn_addi == 1'b1) begin
          add_cin = 1'b0;
          we = 1'b1;
          add_a = rs1_data;
          add_b = imm_i_sext;
          rd_data = add_sum;
        end 
        
        if (insn_slti == 1'b1) begin
          we = 1'b1; 
          rd_data = $signed(rs1_data) < $signed(imm_i_sext) ? 32'b1 : 32'b0;
        end else if (insn_sltiu == 1'b1) begin
          we = 1'b1; 
          rd_data = $signed(rs1_data) < $unsigned(imm_i_sext) ? 32'b1 : 32'b0;
        end

        if (insn_xori == 1'b1) begin
          we = 1'b1;
          rd_data =  (rs1_data ^ 32'(signed'(imm_i)));
        end

        if (insn_ori == 1'b1) begin
          we = 1'b1;
          rd_data = (rs1_data | 32'(signed'(imm_i)));
        end

        if (insn_andi == 1'b1) begin
          we = 1'b1;
          rd_data =  (rs1_data & 32'(signed'(imm_i)));
        end

        if (insn_slli == 1'b1) begin 
          we = 1'b1;
          rd_data = (rs1_data << 32'(signed'(imm_i)));
        end else if (insn_srli == 1'b1) begin
          we = 1'b1;
          rd_data = (rs1_data >> 32'(signed'(imm_i)));
        end
        
        if (insn_srai == 1'b1) begin
          we = 1'b1;
          rd_data = $signed(rs1_data) >>> imm_shamt;
        end
      end

      OpRegReg : begin
        we = 1'b1;

        if (insn_add == 1'b1) begin
          add_cin = 1'b0;
          we = 1'b1;
          add_a = rs1_data;
          add_b = rs2_data;
          rd_data = add_sum;
        end

        if (insn_sub == 1'b1) begin
          add_cin = 1'b1;
          we = 1'b1;
          add_a = rs1_data;
          add_b = ~rs2_data;
          rd_data = add_sum;
        end

        if (insn_sll == 1'b1) begin
          we = 1'b1;
          rd_data = rs1_data << rs2_data[4:0];
        end

        if (insn_slt == 1'b1) begin
          we = 1'b1;
          rd_data = $signed(rs1_data) < $signed(rs2_data) ? 32'b1 : 32'b0;
        end else if (insn_sltu == 1'b1) begin
          we = 1'b1;
          rd_data = rs1_data < $unsigned(rs2_data) ? 32'b1 : 32'b0;
        end

        if (insn_xor == 1'b1) begin
          we = 1'b1;
          rd_data = rs1_data ^ rs2_data;
        end

        if (insn_srl == 1'b1) begin
          we = 1'b1;
          rd_data = rs1_data >> (rs2_data[4:0]);
        end
        
        if (insn_sra == 1'b1) begin
          we = 1'b1;
          rd_data = $signed(rs1_data) >>> rs2_data[4:0];
        end

        if (insn_or == 1'b1) begin
          we = 1'b1;
          rd_data = rs1_data | rs2_data;
        end

        if (insn_and == 1'b1) begin
          we = 1'b1;
          rd_data = rs1_data & rs2_data;
        end

        if (insn_mul == 1'b1) begin
          product = rs1_data * rs2_data;
          rd_data = product[31:0];
        end else if (insn_mulh == 1'b1) begin
          product = $signed(rs1_data) * $signed(rs2_data);
          rd_data = product[63:32];
        end else if (insn_mulhsu == 1'b1) begin
          if (rs1_data[31] == 1'b1) begin
            product_signed = ~(rs1_data) + 32'b1;
          end else begin
            product_signed = rs1_data;
          end

          product = product_signed * rs2_data;

          if (rs1_data[31] == 1'b1) begin
            product_final = ~product + 64'b1;
          end else begin
            product_final = product;
          end
          rd_data = product_final[63:32];
        end else if (insn_mulhu == 1'b1) begin
          product = $unsigned(rs1_data) * $unsigned(rs2_data);
          rd_data = product[63:32];
        end

        if (insn_div == 1'b1) begin
          rs1 = rs1_data[31];
          rs2 = rs2_data[31];
          zero_check = (rs1_data == 0) | (rs2_data == 0)  ;
          dividend = rs1_data[31] ? (~rs1_data + 1) : rs1_data;
          divisor = rs2_data[31] ? (~rs2_data + 1) : rs2_data;
          rd_data = zero_check ? $signed(32'hFFFFFFFF) : ((rs1 != rs2) ? (~quotient + 1) : quotient); 
        end else if (insn_divu == 1'b1) begin
          zero_check = (rs1_data == 0) | (rs2_data == 0)  ;
          dividend = $unsigned(rs1_data);
          divisor = $unsigned(rs2_data);
          rd_data = zero_check ? $signed(32'hFFFFFFFF) : quotient;
        end else if (insn_rem == 1'b1) begin
          rs1 = rs1_data[31];
          rs2 = rs2_data[31];
          zero_check = (rs1_data == 0) | (rs2_data == 0)  ;
          dividend = rs1_data[31] ? (~rs1_data + 1) : rs1_data;
          divisor = rs2_data[31] ? (~rs2_data + 1) : rs2_data;
          if (!zero_check ) begin
              rd_data = (rs1 == 1'b1)?(~remainder + 1):(remainder);
          end 
          else begin
              rd_data = rs1_data[31] ? (~rs1_data + 1) : rs1_data;
          end
        end else if (insn_remu == 1'b1) begin
          dividend = $unsigned(rs1_data);
          divisor = $unsigned(rs2_data);
          zero_check = (rs1_data == 0) | (rs2_data == 0)  ;
          rd_data = (zero_check)?$unsigned(rs1_data):remainder;
        end

      end

      default: begin
        illegal_insn = 1'b1;
      end
    endcase

    if (branch == 1'b0) begin
      pcNext = pcCurrent + pcTemp;
    end
  
  end
  
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

    // the vadde at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the vadde at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the vadde to be written to addr_to_dmem, controlled by store_we_to_dmem
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
      // dmem is "read-first": read returns vadde before the write
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

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_vadde, mem_data_to_write;
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
      .load_data_from_dmem(mem_data_loaded_vadde),
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
      .load_data_from_dmem(mem_data_loaded_vadde),
      .halt(halt)
  );

endmodule
