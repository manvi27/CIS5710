`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
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
  // TODO: copy your RegFile code here
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

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

/** NB: ARESETn is active-low, i.e., reset when this input is ZERO */
interface axi_clkrst_if (
    input wire ACLK,
    input wire ARESETn
);
endinterface

interface axi_if #(
      parameter int ADDR_WIDTH = 32
    , parameter int DATA_WIDTH = 32
);
  logic                      ARVALID;
  logic                      ARREADY;
  logic [    ADDR_WIDTH-1:0] ARADDR;
  logic [               2:0] ARPROT;

  logic                      RVALID;
  logic                      RREADY;
  logic [    DATA_WIDTH-1:0] RDATA;
  logic [               1:0] RRESP;

  logic                      AWVALID;
  logic                      AWREADY;
  logic [    ADDR_WIDTH-1:0] AWADDR;
  logic [               2:0] AWPROT;

  logic                      WVALID;
  logic                      WREADY;
  logic [    DATA_WIDTH-1:0] WDATA;
  logic [(DATA_WIDTH/8)-1:0] WSTRB;

  logic                      BVALID;
  logic                      BREADY;
  logic [               1:0] BRESP;

  modport manager(
      input ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP,
      output ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY
  );
  modport subord(
      input ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY,
      output ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP
  );
endinterface

// module MemoryAxiLite #(
//     parameter int NUM_WORDS  = 32,
//     parameter int ADDR_WIDTH = 32,
//     parameter int DATA_WIDTH = 32
// ) (
//     axi_clkrst_if axi,
//     axi_if.subord insn,
//     axi_if.subord data
// );

//   // memory is an array of 4B words
//   logic [DATA_WIDTH-1:0] mem_array[NUM_WORDS];
//   localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
//   localparam int AddrLsb = 2;
//   // [BR]RESP codes, from Section A 3.4.4 of AXI4 spec
//   localparam bit [1:0] ResponseOkay = 2'b00;
//   // localparam bit [1:0] ResponseSubordinateError = 2'b10;
//   // localparam bit [1:0] ResponseDecodeError = 2'b11;

// `ifndef FORMAL
//   always_comb begin
//     // memory addresses should always be 4B-aligned
//     assert (!insn.ARVALID || insn.ARADDR[1:0] == 2'b00);
//     assert (!data.ARVALID || data.ARADDR[1:0] == 2'b00);
//     assert (!data.AWVALID || data.AWADDR[1:0] == 2'b00);
//     // we don't use the protection bits
//     assert (insn.ARPROT == 3'd0);
//     assert (data.ARPROT == 3'd0);
//     assert (data.AWPROT == 3'd0);
//     assert (AddrMsb <= ADDR_WIDTH);
//   end
// `endif

//   // TODO: changes will be needed throughout this module

//   always_ff @(posedge axi.ACLK) begin
//     if (!axi.ARESETn) begin
//       // start out ready to accept incoming reads
//       insn.ARREADY <= 1;
//       data.ARREADY <= 1;
//       // start out ready to accept an incoming write
//       data.AWREADY <= 1;
//       data.WREADY <= 1;

//     end else begin     
//       if(data.ARVALID) begin
//         data.RVALID <= 1;
//         data.RDATA <= mem_array[data.ARADDR[AddrMsb:AddrLsb]][DATA_WIDTH-1:0];
//         data.RRESP <= ResponseOkay;
//       end
//       if(data.AWVALID && data.WVALID) begin
//         data.BVALID <= 1;
//         // for(int i = 0; i < DATA_WIDTH/8; i = i+1) begin
//           if(data.WSTRB[0] == 1'b1) begin
//             mem_array[data.AWADDR[AddrMsb:AddrLsb]][7:0] <= data.WDATA[7:0];
//           end
//           if(data.WSTRB[1] == 1'b1) begin
//             mem_array[data.AWADDR[AddrMsb:AddrLsb]][15:8] <= data.WDATA[15:8];
//           end
//           if(data.WSTRB[2] == 1'b1) begin
//             mem_array[data.AWADDR[AddrMsb:AddrLsb]][23:16] <= data.WDATA[23:16];
//           end
//           if(data.WSTRB[3] == 1'b1) begin
//             mem_array[data.AWADDR[AddrMsb:AddrLsb]][31:24] <= data.WDATA[31:24];
//           end
//         // end
        
//         // mem_array[data.AWADDR[AddrMsb:AddrLsb]][DATA_WIDTH-1:0] <= data.WDATA;
//         data.BRESP <= ResponseOkay;
//       end
//       if(insn.ARVALID) begin
//         insn.RVALID <= 1;
//         insn.RDATA <= mem_array[insn.ARADDR[AddrMsb:AddrLsb]][DATA_WIDTH-1:0];
//         data.RRESP <= ResponseOkay;
//       end
//       if(insn.AWVALID && insn.WVALID) begin
//         insn.BVALID <= 1;
//         mem_array[data.AWADDR[AddrMsb:AddrLsb]][DATA_WIDTH-1:0] <= insn.WDATA;
//         insn.BRESP <= ResponseOkay;
//       end
//     end
//   end

// endmodule

module MemoryAxiLite #(
    parameter int NUM_WORDS  = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    axi_clkrst_if axi,
    axi_if.subord insn,
    axi_if.subord data
);

  // memory is an array of 4B words
  logic [DATA_WIDTH-1:0] mem_array[NUM_WORDS];
  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  // [BR]RESP codes, from Section A 3.4.4 of AXI4 spec
  // localparam bit [1:0] ResponseOkay = 2'b00;
  // localparam bit [1:0] ResponseSubordinateError = 2'b10;
  // localparam bit [1:0] ResponseDecodeError = 2'b11;

`ifndef FORMAL
  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (!insn.ARVALID || insn.ARADDR[1:0] == 2'b00);
    assert (!data.ARVALID || data.ARADDR[1:0] == 2'b00);
    assert (!data.AWVALID || data.AWADDR[1:0] == 2'b00);
    // we don't use the protection bits
    assert (insn.ARPROT == 3'd0);
    assert (data.ARPROT == 3'd0);
    assert (data.AWPROT == 3'd0);
  end
`endif

  // TODO: changes will be needed throughout this module
  // Registers for AXI4Lite Signals
  // Insn Address Signal
  reg [ADDR_WIDTH-1 : 0] 	reg_insn_araddr;
	reg  	reg_insn_arready;
  reg  	reg_insn_arvalid;

  // Insn Read Signals
  reg [DATA_WIDTH-1 : 0] 	reg_insn_rdata;
	reg [1 : 0] 	reg_insn_rresp;
	reg  	reg_insn_rvalid;

  // Data Address Signal
  reg [ADDR_WIDTH-1 : 0] 	reg_data_araddr;
	reg  	reg_data_arready;
  reg  	reg_data_arvalid;

  // Data Read Signals
  reg [DATA_WIDTH-1 : 0] 	reg_data_rdata;
	reg [1 : 0] 	reg_data_rresp;
	reg  	reg_data_rvalid;

  // Data Write Signals
	reg [ADDR_WIDTH-1: 0] 	reg_data_awaddr;
	reg  	reg_data_awready;
	reg  	reg_data_wready;
	reg [1 : 0] reg_data_bresp;
	reg  	reg_data_bvalid;

  wire reg_check;
	reg	 awrite_en;


	// Mapping output to registers
	assign insn.ARREADY	= reg_insn_arready;
	assign insn.RDATA	= reg_insn_rdata;
	assign insn.RRESP	= reg_insn_rresp;
	assign insn.RVALID	= reg_insn_rvalid;

  assign data.ARREADY	= reg_data_arready;
	assign data.RDATA	= reg_data_rdata;
	assign data.RRESP	= reg_data_rresp;
	assign data.RVALID	= reg_data_rvalid;

  assign data.AWREADY	= reg_data_awready;
	assign data.WREADY	= reg_data_wready;
	assign data.BRESP	= reg_data_bresp;
	assign data.BVALID	= reg_data_bvalid;

  /**** Insn Read Handling ****/

  always_ff @(posedge axi.ACLK) begin
    if (!axi.ARESETn) begin
	      reg_insn_arready <= 1'b1;
	      reg_insn_araddr  <= 32'b0;
    end else begin
          // Read Request Condition
          if (insn.ARVALID) begin
	          // Valid read address asserted
	          reg_insn_arready <= 1'b1;
	          // Store address for later use.
	          reg_insn_araddr <= insn.ARADDR;
	        end else begin
	          reg_insn_arready <= 1'b0;
	        end
    end
  end

  // Handle Address Valid Signal Generation 
	always_ff @(posedge axi.ACLK) begin
    if (!axi.ARESETn) begin
	      reg_insn_rvalid <= 0;
	      reg_insn_rresp  <= 0;
        reg_insn_rdata  <= 0;
	  end else begin
        // Condition for RVALID assertion
	      if (reg_insn_arready && insn.ARVALID) begin
	          // Asserted RVALID. 
	          reg_insn_rvalid <= 1'b1;
            reg_insn_rdata <= mem_array[insn.ARADDR[AddrMsb:AddrLsb]]; 
            // Give OK Response
	          reg_insn_rresp  <= 2'b0;
	      end else if (insn.RREADY) begin
	          // Master accepts the read data.
	          reg_insn_rvalid <= 1'b0;
	      end                
	  end
	end

  /**** Data Read Handling ****/
  // Handle Address Ready Signal Generation 
  always_ff @(posedge axi.ACLK) begin
    if (!axi.ARESETn) begin
	      reg_data_arready <= 1'b1;
	      reg_data_araddr  <= 32'b0;
    end else begin
          if (data.ARVALID) begin
	          reg_data_arready <= 1'b1;
	        end else begin
            reg_data_arready <= 1'b1;
	        end
    end
  end

  // Handle Address Valid Signal Generation 
	always_ff @(posedge axi.ACLK) begin
    if (!axi.ARESETn) begin
	      reg_data_rvalid <= 0;
	      reg_data_rresp  <= 0;
        reg_data_rdata  <= 0;
	  end else begin
        if (reg_data_arready && data.ARVALID) begin
	          reg_data_rvalid <= 1'b1;
            reg_data_rdata <= mem_array[data.ARADDR[AddrMsb:AddrLsb]];
	          reg_data_rresp  <= 2'b0;
        end else if (data.RREADY) begin
	          reg_data_rvalid <= 1'b0;
	      end                
	  end
	end    

  /**** Data Write Handling: Only for Data ****/
  always_ff @(posedge axi.ACLK) begin
	  if (!axi.ARESETn) begin
	    reg_data_awready <= 1'b1;
	    awrite_en <= 1'b1;
      reg_data_wready <= 1'b1;
	  end else begin    
      if (data.AWVALID && data.WVALID) begin
          reg_data_awready <= 1'b1;
          awrite_en <= 1'b0;
          reg_data_wready <= 1'b1;

      end else if (data.BREADY && reg_data_bvalid) begin
          awrite_en <= 1'b1;
          reg_data_awready <= 1'b0;
          reg_data_wready <= 1'b0;
      end else begin
          reg_data_awready <= 1'b0;
          reg_data_wready <= 1'b0;
      end
	  end 
	end   

	assign reg_check = data.WVALID && data.AWVALID;

	always_ff @(posedge axi.ACLK) begin
	  if (!axi.ARESETn) begin
	  end else begin
      if (reg_check) begin
        if (data.WSTRB[0]) begin
          mem_array[data.AWADDR[AddrMsb:AddrLsb]][7:0] <= data.WDATA[7:0];
        end
        if (data.WSTRB[1]) begin
          mem_array[data.AWADDR[AddrMsb:AddrLsb]][15:8] <= data.WDATA[15:8];
        end
        if (data.WSTRB[2]) begin
          mem_array[data.AWADDR[AddrMsb:AddrLsb]][23:16] <= data.WDATA[23:16];
        end
        if (data.WSTRB[3]) begin
          mem_array[data.AWADDR[AddrMsb:AddrLsb]][31:24] <= data.WDATA[31:24];
        end
      end
	  end
	end    

	always_ff @(posedge axi.ACLK) begin
	  if (!axi.ARESETn) begin
	      reg_data_bvalid  <= 0;
	      reg_data_bresp   <= 2'b0;
	  end else begin    
	      //if (reg_data_awready && data.AWVALID && ~reg_data_bvalid && reg_data_wready && data.WVALID) begin
        if (reg_data_awready && data.AWVALID && reg_data_wready && data.WVALID) begin
          reg_data_bvalid <= 1'b1;
          reg_data_bresp  <= 2'b0;
	      end else begin
          if (data.BREADY) begin
            reg_data_bvalid <= 1'b0; 
          end  
	      end
	    end
	end 

endmodule

/** This is used for testing MemoryAxiLite in simulation, since Verilator doesn't allow
SV interfaces in top-level modules. We expose all of the AXIL signals here so that tests
can interact with them. */
module MemAxiLiteTester #(
    parameter int NUM_WORDS  = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input wire ACLK,
    input wire ARESETn,

    input  wire                   I_ARVALID,
    output logic                  I_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] I_ARADDR,
    input  wire  [           2:0] I_ARPROT,
    output logic                  I_RVALID,
    input  wire                   I_RREADY,
    output logic [ADDR_WIDTH-1:0] I_RDATA,
    output logic [           1:0] I_RRESP,

    input  wire                       I_AWVALID,
    output logic                      I_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] I_AWADDR,
    input  wire  [               2:0] I_AWPROT,
    input  wire                       I_WVALID,
    output logic                      I_WREADY,
    input  wire  [    DATA_WIDTH-1:0] I_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] I_WSTRB,
    output logic                      I_BVALID,
    input  wire                       I_BREADY,
    output logic [               1:0] I_BRESP,

    input  wire                   D_ARVALID,
    output logic                  D_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] D_ARADDR,
    input  wire  [           2:0] D_ARPROT,
    output logic                  D_RVALID,
    input  wire                   D_RREADY,
    output logic [ADDR_WIDTH-1:0] D_RDATA,
    output logic [           1:0] D_RRESP,

    input  wire                       D_AWVALID,
    output logic                      D_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] D_AWADDR,
    input  wire  [               2:0] D_AWPROT,
    input  wire                       D_WVALID,
    output logic                      D_WREADY,
    input  wire  [    DATA_WIDTH-1:0] D_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] D_WSTRB,
    output logic                      D_BVALID,
    input  wire                       D_BREADY,
    output logic [               1:0] D_BRESP
);

  axi_clkrst_if axi (.*);
  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) insn ();
  assign insn.manager.ARVALID = I_ARVALID;
  assign I_ARREADY = insn.manager.ARREADY;
  assign insn.manager.ARADDR = I_ARADDR;
  assign insn.manager.ARPROT = I_ARPROT;
  assign I_RVALID = insn.manager.RVALID;
  assign insn.manager.RREADY = I_RREADY;
  assign I_RRESP = insn.manager.RRESP;
  assign I_RDATA = insn.manager.RDATA;

  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) data ();
  assign data.manager.ARVALID = D_ARVALID;
  assign D_ARREADY = data.manager.ARREADY;
  assign data.manager.ARADDR = D_ARADDR;
  assign data.manager.ARPROT = D_ARPROT;
  assign D_RVALID = data.manager.RVALID;
  assign data.manager.RREADY = D_RREADY;
  assign D_RRESP = data.manager.RRESP;
  assign D_RDATA = data.manager.RDATA;

  assign data.manager.AWVALID = D_AWVALID;
  assign D_AWREADY = data.manager.AWREADY;
  assign data.manager.AWADDR = D_AWADDR;
  assign data.manager.AWPROT = D_AWPROT;
  assign data.manager.WVALID = D_WVALID;
  assign D_WREADY = data.manager.WREADY;
  assign data.manager.WDATA = D_WDATA;
  assign data.manager.WSTRB = D_WSTRB;
  assign D_BVALID = data.manager.BVALID;
  assign data.manager.BREADY = D_BREADY;
  assign D_BRESP = data.manager.BRESP;

  MemoryAxiLite #(
      .NUM_WORDS(NUM_WORDS)
  ) mem (
      .axi (axi),
      .insn(insn.subord),
      .data(data.subord)
  );
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
  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence insn */
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
  logic [`REG_SIZE] pc_D;
  logic [`INSN_SIZE] insn_D;
  cycle_status_e cycle_status_D;
  logic [4:0] rd_no_D;
  logic [4:0] rs1_no_D;
  logic [`REG_SIZE] rs1_data_temp_D;
  logic [4:0] rs2_no_D;
  logic [`REG_SIZE] rs2_data_temp_D;
  logic [6:0] insn7bit_D;
  logic [2:0] insn3bit_D;
  logic [`REG_SIZE] addr_to_dmem_D;
  logic [3:0] store_we_to_dmem_D;
  logic [`REG_SIZE] store_data_to_dmem_D;
  logic [`REG_SIZE] insn_imem_D;
  logic [`REG_SIZE] imm_i_sext_D;
  logic [`OPCODE_SIZE] insn_opcode_D;
  insn_set dec_control_D;
} stage_decode_t;

/** state at the start of Execute stage */
typedef struct packed {
    logic [`REG_SIZE] pc_X;
  logic [`INSN_SIZE] insn_X;
  cycle_status_e cycle_status_X;
  logic [4:0] rd_no_X;
  logic [`REG_SIZE] rd_val_X;
  logic [4:0] rs1_no_X;
  logic [`REG_SIZE] rs1_data_temp_X;
  logic [4:0] rs2_no_X;
  logic [`REG_SIZE] rs2_data_temp_X;
  logic [`REG_SIZE] addr_to_dmem_X;
  logic [3:0] store_we_to_dmem_X;
  logic [`REG_SIZE] store_data_to_dmem_X;
  logic [`REG_SIZE] insn_imem_X;
  logic [`REG_SIZE] imm_i_sext_X;
  logic [`OPCODE_SIZE] insn_opcode_X;
  insn_set exe_control_X;
} stage_execute_t;

/** state at the start of Memory stage */
typedef struct packed {
  logic [`REG_SIZE] pc_M;
  logic [`INSN_SIZE] insn_M;
  cycle_status_e cycle_status_M;
  logic [4:0] rd_no_M;
  logic [`REG_SIZE] rd_val_M;
  logic [4:0] rs1_no_M;
  logic [`REG_SIZE] rs1_data_temp_M;
  logic [4:0] rs2_no_M;
  logic [`REG_SIZE] rs2_data_temp_M;
  logic [`REG_SIZE] addr_to_dmem_M;
  logic [3:0] store_we_to_dmem_M;
  logic [`REG_SIZE] store_data_to_dmem_M;
  logic [`OPCODE_SIZE] insn_opcode_M;
  logic halt_sig_M;
  logic branch_taken_M;
  logic [`REG_SIZE] address_bits_M;
  logic [`REG_SIZE] pcNext_M;
  logic lw_stall_m;
  logic div_stall_m;
  logic mux_fence_m;
  insn_set mem_control_M;
} stage_memory_t;

/** state at the start of Write stage */
typedef struct packed {
    logic [`REG_SIZE] pc_W;
  logic [`INSN_SIZE] insn_W;
  cycle_status_e cycle_status_W;
  logic [4:0] rd_no_W;
  logic [`REG_SIZE] rd_val_W;
  logic [4:0] rs1_no_W;
  logic [`REG_SIZE] rs1_data_temp_W;
  logic [4:0] rs2_no_W;
  logic [`REG_SIZE] rs2_data_temp_W;
  logic [`OPCODE_SIZE] insn_opcode_W;
  logic halt_sig_W;
  logic [3:0] store_we_to_dmem_W;
  logic [`REG_SIZE] store_data_to_dmem_W;
  logic [`REG_SIZE] address_bits_wb;
  insn_set write_control_W;
} stage_write_t;

module DatapathAxilMemory (
    input wire clk,
    input wire rst,

    // Start by replacing this interface to imem...
    // output logic [`REG_SIZE] pc_to_imem,
    // input wire [`INSN_SIZE] insn_from_imem,
    // ...with this AXIL one.
    axi_if.manager imem,

    // Once imem is working, replace this interface to dmem...
    // output logic [`REG_SIZE] addr_to_dmem,
    // input wire [`REG_SIZE] load_data_from_dmem,
    // output logic [`REG_SIZE] store_data_to_dmem,
    // output logic [3:0] store_we_to_dmem,
    // ...with this AXIL one
    axi_if.manager dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // TODO: your code here
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
  logic [`REG_SIZE] fetch_pc_pass;
  logic [`REG_SIZE] fetch_insn_pass;
  cycle_status_e f_cycle_status, fetch_cycle_status_pass;

  stage_decode_t decodeBuffer;
  logic lw_stall_m;
  logic div_stall_m;
  logic mux_fence_m;
  logic branch_taken_m;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      pcCurr <= 32'd0;
      cycleStatus <= CYCLE_NO_STALL;
      imem.RREADY <= 1'b1;
    //   imem.RREADY <= 1'b0;
    end else begin
      cycleStatus <= CYCLE_NO_STALL;
      if (branch_taken) begin
        pcCurr <= pcNext; 
      end 
      else if(fenceStall || divStall || loadStall || mux_fence_m)  begin
        // pcCurr <= pcCurr + 4; 
      end
      else begin
        pcCurr <= pcCurr + 4;
        imem.ARVALID <= 1'b1;
        // imem.ARVALID <= 1'b0;
      end
    end
  end


  // send PC to imem
  assign imem.ARADDR = pcCurr;
//   assign imem.ARVALID = 1'b1;
  assign instr = imem.RDATA;

//   always_comb begin
//     if(branch_taken == 1'b1) begin
//       fetch_cycle_status_pass = CYCLE_TAKEN_BRANCH;
//       fetch_insn_pass = 32'b0;
//       fetch_pc_pass = 32'b0;
//     end else begin
//       fetch_cycle_status_pass = cycleStatus;
//       fetch_insn_pass = instr;
//       fetch_pc_pass = pcCurr;
//     end
//   end

//   always_comb begin
//     imem.ARADDR = 32'b0;
//     if (imem.ARREADY)begin
//         imem.ARADDR = pcCurr;
//     end else begin
//         // imem.ARADDR = pcCurr;
//     end
//   end 
  
  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
//   wire [255:0] f_disasm;
//   Disasm #(
//       .PREFIX("F")
//   ) disasm_0fetch (
//       .insn  (instr),
//       .disasm(f_disasm)
//   );

  wire [12:0] imm_b_temp;
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
  logic rs1d, rs2d;

//   RegFile rf(.rd(stateW.rd_no_W),
//             .rd_data(stateW.rd_val_W),
//             .rs1(stateD.rs1_no_D),
//             .x_rs1_data(rs1_data_temp), 
//             .rs2(stateD.rs2_no_D),
//             .x_rs2_data(rs2_data_temp),
//             .clk(clk),
//             .we(we),
//             .rst(rst));

  
  RegFile rf(.rd(stateW.rd_no_W),
            .rd_data(rd_val_mem_temp),
            .rs1(stateD.rs1_no_D),
            .x_rs1_data(rs1_data_temp), 
            .rs2(stateD.rs2_no_D),
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

  insn_set exe_control_temp;
  logic [4:0] rs2_val_or_not;

  logic [`REG_SIZE] decode_stall_temp;
  cycle_status_e decode_state_cycle_status;

  always_ff @(posedge clk)begin
    if (rst == 1'b1) begin
      decode_state_cycle_status <= CYCLE_RESET; 
      decode_stall_temp <= 32'b0;
    end else begin 
      if (fenceStall == 1'b1) begin 
       //stall
      end else begin
        decode_stall_temp <= (imem.RVALID == 1'b1)?imem.RDATA:32'b0;
        decode_state_cycle_status <= CYCLE_NO_STALL;
      end 
    end 
  end 

  /****************/
  /* DECODE STAGE */
  /****************/

  stage_decode_t stateD;
//   always_ff @(posedge clk) begin
//     if (rst) begin
//       stateD <= '{
//         pc_D: 0,
//         insn_D: 0,
//         cycle_status_D: CYCLE_RESET,
//         rd_no_D: 0,
//         rs1_no_D: 0,
//         rs1_data_temp_D: 0,
//         rs2_no_D: 0,
//         rs2_data_temp_D: 0,
//         insn7bit_D: 0,
//         insn3bit_D: 0,
//         addr_to_dmem_D: 0,
//         store_we_to_dmem_D: 0,
//         store_data_to_dmem_D: 0,
//         insn_imem_D: 0,
//         imm_i_sext_D: 0,
//         insn_opcode_D: 0,
//         dec_control_D: '{default:0}
//       };
//     end else begin
//       begin
//         // if (branch_taken) begin
//         //   stateD <= 0;
//         //   stateD.cycle_status_D <= CYCLE_TAKEN_BRANCH;
//         // end else begin
//         if (branch_taken == 1'b1) begin
//           stateD <= 0;
//           stateD.pc_D <= fetch_pc_pass;
//           stateD.insn_D <= fetch_insn_pass;
//           stateD.cycle_status_D <= fetch_cycle_status_pass;
//         end if (loadStall || divStall || fenceStall) begin
//         //   stateD <= 0;
//         //   stateD.pc <= fetch_pc_pass;
//         //   decode_stateDstate.insn <= fetch_insn_pass;
//         //   stateD.cycle_status_D <= fetch_cycle_status_pass;
//         //end if (mux_fence == 1'b1) begin
//             //execute_state <= 0;

//         // stateD <= '{
//         //     pc_D: pcCurr,
//         //     insn_D: instr,
//         //     cycle_status_D: cycleStatus,
//         //     rd_no_D: insn_opcode == OpcodeBranch ? 0 : insn_rd,
      
//         //     rs1_no_D: insn_opcode == OpcodeLui ? 0: insn_rs1,
//         //     rs1_data_temp_D: rs1_data_temp,
//         //     rs2_no_D: ((insn_opcode == OpcodeRegImm) || (insn_opcode == OpcodeLui)) ? 0: insn_rs2,
//         //     rs2_data_temp_D: rs2_data_temp,
//         //     insn7bit_D: insn_opcode == OpcodeLui ? 0: insn7bit,
//         //     insn3bit_D: insn_opcode == OpcodeLui ? 0: insn3bit,
//         //     addr_to_dmem_D: 0,
//         //     store_we_to_dmem_D: 0,
//         //     store_data_to_dmem_D: 0,
//         //     insn_imem_D: insn_from_imem,
//         //     imm_i_sext_D: 0,
//         //     insn_opcode_D: insn_opcode,
//         //     dec_control_D: '{default:0}
//         //   };

//         end else begin
//             stateD <= '{
//             pc_D: fetch_pc_pass,
//             insn_D: fetch_insn_pass,
//             cycle_status_D: fetch_cycle_status_pass,
//             rd_no_D: ((insn_opcode == 7'h63) || (insn_opcode == 7'h23)) ? 0 : insn_rd,
      
//             rs1_no_D: insn_opcode == 7'h37 || insn_opcode == 7'h6f ? 0: insn_rs1,
//             rs1_data_temp_D: 0,
//             rs2_no_D: ((insn_opcode == 7'h13) || (insn_opcode == 7'h37) || 
//                   (insn_opcode == 7'h3) || (insn_opcode == 7'h6f)) ? 0: insn_rs2,
//             rs2_data_temp_D: 0,
//             insn7bit_D: ((insn_opcode == 7'h37) || (insn_opcode == 7'h3) ||
//                       (insn_opcode == 7'h37) || (insn_opcode == 7'h23)
//                       || (insn_opcode == 7'h6f )) ? 0: insn7bit,
//             insn3bit_D: insn_opcode == 7'h37 || insn_opcode == 7'h6f ? 0: insn3bit,
//             // insn_funct3: insn_opcode == 7'h37 || insn_opcode == 7'h6f ? 0: insn_funct3,
//             addr_to_dmem_D: 0,
//             store_we_to_dmem_D: 0,
//             store_data_to_dmem_D: 0,
//             insn_imem_D: fetch_insn_pass,
//             imm_i_sext_D: 0,
//             insn_opcode_D: insn_opcode,
//             dec_control_D: '{default:0}
//           };
//         end
//       end
//     end
//   end

  logic [`OPCODE_SIZE] insn_opcode_temp;
  logic [`REG_SIZE] insn_buffer_temp;
  cycle_status_e temp_cycle_status;

  always_comb begin

    insn_buffer_temp = 32'b0;
    stateD = 0; 
    stateD.cycle_status_D = decode_state_cycle_status;
    insn_buffer_temp = 0;
    insn_opcode_temp = 0;

    if (rst) begin
      stateD = '{
        pc_D: 0,
        insn_D: 0,
        cycle_status_D: CYCLE_RESET,
        rd_no_D: 0,
        rs1_no_D: 0,
        rs1_data_temp_D: 0,
        rs2_no_D: 0,
        rs2_data_temp_D: 0,
        insn7bit_D: 0,
        insn3bit_D: 0,
        addr_to_dmem_D: 0,
        store_we_to_dmem_D: 0,
        store_data_to_dmem_D: 0,
        insn_imem_D: 0,
        imm_i_sext_D: 0,
        insn_opcode_D: 0,
        dec_control_D: '{default:0}
      };
    end else begin
      begin
        if (branch_taken == 1'b1) begin
          stateD = 0;
          stateD.cycle_status_D = CYCLE_TAKEN_BRANCH;
        end 
        // else begin
        if (lw_stall_m == 1'b1 || div_stall_m == 1'b1 || mux_fence_m == 1'b1) begin
          insn_buffer_temp = decode_stall_temp;
          insn_opcode_temp = decode_stall_temp[6:0];
          // temp_cycle_status = decode_state_cycle_status;
          // stateD.pc_D = pcCurr - 32'd4;
          stateD = '{
          pc_D: (pcCurr != 32'b0) ? (pcCurr - 32'd4) : (pcCurr),
          insn_D: insn_buffer_temp,
          cycle_status_D: decode_state_cycle_status,
          rd_no_D: ((insn_opcode_temp == 7'h63) || (insn_opcode_temp == 7'h23)) ? 0 : insn_buffer_temp[11:7],
          rs1_no_D: insn_opcode_temp == 7'h37 || insn_opcode_temp == 7'h6f ? 0 : insn_buffer_temp[19:15],
          rs1_data_temp_D: 0,
          rs2_no_D: ((insn_opcode_temp == 7'h13) || (insn_opcode_temp == 7'h37) || 
                (insn_opcode_temp == 7'h3) || (insn_opcode_temp == 7'h6f)) ? 0: insn_buffer_temp[24:20],
          rs2_data_temp_D: 0,
          insn7bit_D: ((insn_opcode_temp == 7'h37) || (insn_opcode_temp == 7'h3) ||
                    (insn_opcode_temp == 7'h37) || (insn_opcode_temp == 7'h23)
                    || (insn_opcode_temp == 7'h6f )) ? 0: insn_buffer_temp[31:25],
          insn3bit_D: insn_opcode_temp == 7'h37 || insn_opcode_temp == 7'h6f ? 0: insn_buffer_temp[14:12],
          // insn_funct3: insn_opcode == 7'h37 || insn_opcode == 7'h6f ? 0: insn_funct3,
          addr_to_dmem_D: 0,
          store_we_to_dmem_D: 0,
          store_data_to_dmem_D: 0,
          insn_imem_D: insn_buffer_temp,
          imm_i_sext_D: 0,
          insn_opcode_D: insn_opcode_temp,
          dec_control_D: '{default:0}
        };
        end else begin
          if(imem.RVALID) begin
            insn_buffer_temp = imem.RDATA;;
            insn_opcode_temp = insn_buffer_temp[6:0];
            stateD = '{
            pc_D: (pcCurr != 32'b0)?(pcCurr - 32'd4):(pcCurr),
            insn_D: insn_buffer_temp,
            cycle_status_D: CYCLE_NO_STALL,
            rd_no_D: ((insn_opcode_temp == 7'h63) || (insn_opcode_temp == 7'h23)) ? 0 : insn_buffer_temp[11:7],
            rs1_no_D: insn_opcode_temp == 7'h37 || insn_opcode_temp == 7'h6f ? 0 : insn_buffer_temp[19:15],
            rs1_data_temp_D: 0,
            rs2_no_D: ((insn_opcode_temp == 7'h13) || (insn_opcode_temp == 7'h37) || 
                  (insn_opcode_temp == 7'h3) || (insn_opcode_temp == 7'h6f)) ? 0: insn_buffer_temp[24:20],
            rs2_data_temp_D: 0,
            insn7bit_D: ((insn_opcode_temp == 7'h37) || (insn_opcode_temp == 7'h3) ||
                      (insn_opcode_temp == 7'h37) || (insn_opcode_temp == 7'h23)
                      || (insn_opcode_temp == 7'h6f )) ? 0: insn_buffer_temp[31:25],
            insn3bit_D: insn_opcode_temp == 7'h37 || insn_opcode_temp == 7'h6f ? 0: insn_buffer_temp[14:12],
            // insn_funct3: insn_opcode == 7'h37 || insn_opcode == 7'h6f ? 0: insn_funct3,
            addr_to_dmem_D: 0,
            store_we_to_dmem_D: 0,
            store_data_to_dmem_D: 0,
            insn_imem_D: insn_buffer_temp,
            imm_i_sext_D: 0,
            insn_opcode_D: insn_opcode_temp,
            dec_control_D: '{default:0}
          };
            // temp_cycle_status = CYCLE_NO_STALL;
          end
        end 
          
          // stateD = '{
          //   pc_D: (pcCurr != 32'b0)?(pcCurr - 32'd4):(pcCurr),
          //   insn_D: insn_buffer_temp,
          //   cycle_status_D: decode_state_cycle_status,
          //   rd_no_D: ((insn_opcode_temp == 7'h63) || (insn_opcode_temp == 7'h23)) ? 0 : insn_buffer_temp[11:7],
          //   rs1_no_D: insn_opcode_temp == 7'h37 || insn_opcode_temp == 7'h6f ? 0 : insn_buffer_temp[19:15],
          //   rs1_data_temp_D: 0,
          //   rs2_no_D: ((insn_opcode_temp == 7'h13) || (insn_opcode_temp == 7'h37) || 
          //         (insn_opcode_temp == 7'h3) || (insn_opcode_temp == 7'h6f)) ? 0: insn_buffer_temp[24:20],
          //   rs2_data_temp_D: 0,
          //   insn7bit_D: ((insn_opcode_temp == 7'h37) || (insn_opcode_temp == 7'h3) ||
          //             (insn_opcode_temp == 7'h37) || (insn_opcode_temp == 7'h23)
          //             || (insn_opcode_temp == 7'h6f )) ? 0: insn_buffer_temp[31:25],
          //   insn3bit_D: insn_opcode_temp == 7'h37 || insn_opcode_temp == 7'h6f ? 0: insn_buffer_temp[14:12],
          //   // insn_funct3: insn_opcode == 7'h37 || insn_opcode == 7'h6f ? 0: insn_funct3,
          //   addr_to_dmem_D: 0,
          //   store_we_to_dmem_D: 0,
          //   store_data_to_dmem_D: 0,
          //   insn_imem_D: insn_buffer_temp,
          //   imm_i_sext_D: 0,
          //   insn_opcode_D: insn_opcode_temp,
          //   dec_control_D: '{default:0}
          // };
        end
        // if(imem.RVALID) begin
        //   stateD.cycle_status_D = CYCLE_NO_STALL;
        // end
        
      end
    end
  // end

  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (stateD.insn_D),
      .disasm(d_disasm)
  );

  assign imm_i = stateD.insn_imem_D[31:20];
  wire [ 4:0] imm_shamt = stateD.insn_imem_D[24:20];
    logic [1:0] selectDivider;
  logic [`REG_SIZE] divMulticycle;

  // assign imm_s[11:5] = stateD.insn7bit_D, imm_s[4:0] = stateD.insn_imem_D[11:7];
  assign imm_s[11:5] = stateD.insn_imem_D[31:25], imm_s[4:0] = stateD.insn_imem_D[11:7]; 

  assign {imm_b[12], imm_b[10:5]} = stateD.insn7bit_D, {imm_b[4:1], imm_b[11]} = stateD.insn_imem_D[11:7], imm_b[0] = 1'b0;

  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {stateD.insn_imem_D[31:12], 1'b0};
  
  assign imm_u = stateD.insn_imem_D[31:12];

  logic [1:0] mux_val_wd;
  logic [4:0] wd_rd_no;
  logic divStall;
  logic fenceStall;
  logic loadStall;
  assign wd_rd_no = stateW.rd_no_W;

  assign imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  assign imm_i_ext = {{20{1'b0}}, imm_i[11:0]};
  assign imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  assign imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  assign imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};
  assign imm_u_ext = {{12{1'b0}},imm_u[19:0]};

  assign insnSetX.insn_lui = stateD.insn_opcode_D == OpcodeLui;
  assign insnSetX.insn_auipc = stateD.insn_opcode_D == OpcodeAuipc;
  assign insnSetX.insn_jal = stateD.insn_opcode_D == OpcodeJal;
  assign insnSetX.insn_jalr = stateD.insn_opcode_D == OpcodeJalr;

  assign insnSetX.insn_beq = stateD.insn_opcode_D == OpcodeBranch && stateD.insn_imem_D[14:12] == 3'b000;
  assign insnSetX.insn_bne = stateD.insn_opcode_D == OpcodeBranch && stateD.insn_imem_D[14:12] == 3'b001;
  assign insnSetX.insn_blt = stateD.insn_opcode_D == OpcodeBranch && stateD.insn_imem_D[14:12] == 3'b100;
  assign insnSetX.insn_bge = stateD.insn_opcode_D == OpcodeBranch && stateD.insn_imem_D[14:12] == 3'b101;
  assign insnSetX.insn_bltu = stateD.insn_opcode_D == OpcodeBranch && stateD.insn_imem_D[14:12] == 3'b110;
  assign insnSetX.insn_bgeu = stateD.insn_opcode_D == OpcodeBranch && stateD.insn_imem_D[14:12] == 3'b111;

  assign insnSetX.insn_lb = stateD.insn_opcode_D == OpcodeLoad && stateD.insn_imem_D[14:12] == 3'b000;
  assign insnSetX.insn_lh = stateD.insn_opcode_D == OpcodeLoad && stateD.insn_imem_D[14:12] == 3'b001;
  assign insnSetX.insn_lw = stateD.insn_opcode_D == OpcodeLoad && stateD.insn_imem_D[14:12] == 3'b010;
  assign insnSetX.insn_lbu = stateD.insn_opcode_D == OpcodeLoad && stateD.insn_imem_D[14:12] == 3'b100;
  assign insnSetX.insn_lhu = stateD.insn_opcode_D == OpcodeLoad && stateD.insn_imem_D[14:12] == 3'b101;

  assign insnSetX.insn_sb = stateD.insn_opcode_D == OpcodeStore && stateD.insn_imem_D[14:12] == 3'b000;
  assign insnSetX.insn_sh = stateD.insn_opcode_D == OpcodeStore && stateD.insn_imem_D[14:12] == 3'b001;
  assign insnSetX.insn_sw = stateD.insn_opcode_D == OpcodeStore && stateD.insn_imem_D[14:12] == 3'b010;

  assign insnSetX.insn_addi = stateD.insn_opcode_D == OpcodeRegImm && stateD.insn_imem_D[14:12] == 3'b000;
  assign insnSetX.insn_slti = stateD.insn_opcode_D == OpcodeRegImm && stateD.insn_imem_D[14:12] == 3'b010;
  assign insnSetX.insn_sltiu = stateD.insn_opcode_D == OpcodeRegImm && stateD.insn_imem_D[14:12] == 3'b011;
  assign insnSetX.insn_xori = stateD.insn_opcode_D == OpcodeRegImm && stateD.insn_imem_D[14:12] == 3'b100;
  assign insnSetX.insn_ori = stateD.insn_opcode_D == OpcodeRegImm && stateD.insn_imem_D[14:12] == 3'b110;
  assign insnSetX.insn_andi = stateD.insn_opcode_D == OpcodeRegImm && stateD.insn_imem_D[14:12] == 3'b111;

  assign insnSetX.insn_slli = stateD.insn_opcode_D == OpcodeRegImm && stateD.insn_imem_D[14:12] == 3'b001 && stateD.insn_imem_D[31:25] == 7'd0;
  assign insnSetX.insn_srli = stateD.insn_opcode_D == OpcodeRegImm && stateD.insn_imem_D[14:12] == 3'b101 && stateD.insn_imem_D[31:25] == 7'd0;
  assign insnSetX.insn_srai = stateD.insn_opcode_D == OpcodeRegImm && stateD.insn_imem_D[14:12] == 3'b101 && stateD.insn_imem_D[31:25] == 7'b0100000;

  assign insnSetX.insn_add = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[14:12] == 3'b000 && stateD.insn_imem_D[31:25] == 7'd0;
  assign insnSetX.insn_sub  = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[14:12] == 3'b000 && stateD.insn_imem_D[31:25] == 7'b0100000;
  assign insnSetX.insn_sll = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[14:12] == 3'b001 && stateD.insn_imem_D[31:25] == 7'd0;
  assign insnSetX.insn_slt = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[14:12] == 3'b010 && stateD.insn_imem_D[31:25] == 7'd0;
  assign insnSetX.insn_sltu = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[14:12] == 3'b011 && stateD.insn_imem_D[31:25] == 7'd0;
  assign insnSetX.insn_xor = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[14:12] == 3'b100 && stateD.insn_imem_D[31:25] == 7'd0;
  assign insnSetX.insn_srl = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[14:12] == 3'b101 && stateD.insn_imem_D[31:25] == 7'd0;
  assign insnSetX.insn_sra  = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[14:12] == 3'b101 && stateD.insn_imem_D[31:25] == 7'b0100000;
  assign insnSetX.insn_or = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[14:12] == 3'b110 && stateD.insn_imem_D[31:25] == 7'd0;
  assign insnSetX.insn_and = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[14:12] == 3'b111 && stateD.insn_imem_D[31:25] == 7'd0;

  assign insnSetX.insn_mul    = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[31:25] == 7'd1 && stateD.insn_imem_D[14:12] == 3'b000;
  assign insnSetX.insn_mulh   = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[31:25] == 7'd1 && stateD.insn_imem_D[14:12] == 3'b001;
  assign insnSetX.insn_mulhsu = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[31:25] == 7'd1 && stateD.insn_imem_D[14:12] == 3'b010;
  assign insnSetX.insn_mulhu  = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[31:25] == 7'd1 && stateD.insn_imem_D[14:12] == 3'b011;
  assign insnSetX.insn_div    = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[31:25] == 7'd1 && stateD.insn_imem_D[14:12] == 3'b100;
  assign insnSetX.insn_divu   = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[31:25] == 7'd1 && stateD.insn_imem_D[14:12] == 3'b101;
  assign insnSetX.insn_rem    = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[31:25] == 7'd1 && stateD.insn_imem_D[14:12] == 3'b110;
  assign insnSetX.insn_remu   = stateD.insn_opcode_D == OpcodeRegReg && stateD.insn_imem_D[31:25] == 7'd1 && stateD.insn_imem_D[14:12] == 3'b111;
 
  assign insnSetX.insn_ecall = stateD.insn_opcode_D == OpcodeEnviron && stateD.insn_imem_D[31:7] == 25'd0;
  assign insnSetX.insn_fence = stateD.insn_opcode_D == OpcodeMiscMem;
  always_comb begin
    imm_i_sext_X = 0;
    if (insnSetX.insn_jalr ||
        insnSetX.insn_addi ||
        insnSetX.insn_slti ||
        insnSetX.insn_sltiu ||
        insnSetX.insn_xori ||
        insnSetX.insn_ori ||
        insnSetX.insn_andi ||
        (stateD.insn_opcode_D == OpcodeLoad)) begin
        
      imm_i_sext_X = imm_i_sext;
    end
    else if (insnSetX.insn_slli ||
             insnSetX.insn_srli ||
             insnSetX.insn_srai) begin
      imm_i_sext_X = imm_i_ext;
    end
    else if (stateD.insn_opcode_D == OpcodeStore) begin
    
      imm_i_sext_X = imm_s_sext;
    end
    else if (stateD.insn_opcode_D == OpcodeBranch) begin
    
      imm_i_sext_X = imm_b_sext;
    end
    else if (stateD.insn_opcode_D == OpcodeJal) begin
    
      imm_i_sext_X = imm_j_sext;
    end
    else if ((stateD.insn_opcode_D == OpcodeLui) ||
             (stateD.insn_opcode_D == OpcodeAuipc)) begin
      imm_i_sext_X = imm_u_ext;
    end
    
    rs1_mux_data = rs1_data_temp;
    rs2_mux_data = rs2_data_temp;

    mux_val_wd = 2'b0;

    loadStall = 1'b0;
    divStall = 1'b0;
    fenceStall = 1'b0;

    if (wd_rd_no != 0) begin
      case (wd_rd_no)
        stateD.rs1_no_D: begin
        
            mux_val_wd = 2'b01;
            // rs1_mux_data = stateW.rd_val_W;
            rs1_mux_data = rd_val_mem_temp;
        end
        stateD.rs2_no_D: begin
        
            mux_val_wd = 2'b10;
            // rs2_mux_data = stateW.rd_val_W;
            rs2_mux_data = rd_val_mem_temp;
        end
        default: begin
            // No action needed
        end
      endcase
    end

    if (stateX.insn_opcode_X == OpcodeLoad &&
        stateX.rd_no_X != 5'b0) begin
      if (stateX.rd_no_X == stateD.rs1_no_D) begin
            loadStall = 1'b1;
            tempStateX = 0;
      end else if (stateX.rd_no_X == stateD.rs2_no_D) begin
          if (stateD.insn_opcode_D != OpcodeStore) begin
            loadStall = 1'b1;
            tempStateX = 0;
          end
      end
    end

    if (stateX.exe_control_X.insn_div ||
        stateX.exe_control_X.insn_divu ||
        stateX.exe_control_X.insn_rem ||
        stateX.exe_control_X.insn_remu) begin
      if (stateX.rd_no_X == stateD.rs1_no_D ||
          stateX.rd_no_X == stateD.rs2_no_D) begin
          divStall = 1'b1;
          tempStateX = 0;
      end
    end

    if (insnSetX.insn_fence == 1'b1) begin
      if (stateX.insn_opcode_X == OpcodeStore ||
          stateM.insn_opcode_M == OpcodeStore ) begin
        fenceStall = 1'b1;
        // tempStateX = 0;
      end else begin
        fenceStall = 1'b0;
      end
    end

    tempStateX = 0;

    if (branch_taken == 1'b1 || branch_taken_m == 1'b1 || insnSetX.insn_fence == 1'b1) begin// || insnSetX.insn_fence == 1'b1) begin //adding bubble for fence and branch
    //   tempStateX = 0;
    end else begin
      tempStateX = '{
        pc_X: stateD.pc_D,
        insn_X: stateD.insn_D,
        cycle_status_X: stateD.cycle_status_D,
        rd_no_X: stateD.rd_no_D,
        rd_val_X: 0,
        rs1_no_X: stateD.rs1_no_D,
        rs1_data_temp_X: rs1_mux_data,
        rs2_no_X: stateD.rs2_no_D,
        rs2_data_temp_X: rs2_mux_data,
        addr_to_dmem_X: stateD.addr_to_dmem_D,
        store_we_to_dmem_X: stateD.store_we_to_dmem_D,
        store_data_to_dmem_X: stateD.store_data_to_dmem_D,
        insn_imem_X: stateD.insn_imem_D,
        imm_i_sext_X: imm_i_sext_X,
        insn_opcode_X: stateD.insn_opcode_D,
        exe_control_X: insnSetX
      };
    end
  end

  /****************/
  /* EXECUTE STAGE */
  /****************/
  stage_execute_t stateX;
  stage_execute_t tempStateX;

  always_ff @(posedge clk) begin
    if (rst) begin
      stateX <= '{
        pc_X: 0,
        insn_X: 0,
        cycle_status_X: CYCLE_RESET,
        rd_no_X: 0,
        rd_val_X: 0,
        rs1_no_X: 0,
        rs1_data_temp_X: 0,
        rs2_no_X: 0,
        rs2_data_temp_X: 0,
        addr_to_dmem_X: 0,
        store_we_to_dmem_X: 0,
        store_data_to_dmem_X: 0,
        insn_imem_X: 0,
        imm_i_sext_X: 0,
        insn_opcode_X: 0,
        exe_control_X: '{default:0}
      };
    end else begin
      begin
        if (branch_taken || branch_taken_m ) begin
            stateX <= 0;
            stateX.cycle_status_X <= CYCLE_TAKEN_BRANCH;
        end else if (loadStall) begin
            stateX <= 0;
            stateX.cycle_status_X <= CYCLE_LOAD2USE;
        end else if (divStall) begin
            stateX <= 0;
            stateX.cycle_status_X <= CYCLE_DIV2USE;
        end else if (fenceStall) begin
            stateX <= 0;
            stateX.cycle_status_X <= CYCLE_FENCEI;
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
      .insn  (stateX.insn_X),
      .disasm(e_disasm)
  );
  logic [31:0] address_bits_temp;
  
  assign m_rd_no = stateM.rd_no_M;
  assign w_rd_no = stateW.rd_no_W;
  assign x_rs1_no = stateX.rs1_no_X;
  assign x_rs2_no = stateX.rs2_no_X;
  assign insn_opcode_x = stateX.insn_opcode_X;

  always_latch begin
    x_rs1_data = stateX.rs1_data_temp_X;
    x_rs2_data = stateX.rs2_data_temp_X;

    mux_val_mx_wx = 0;

    if (m_rd_no != 0 || w_rd_no != 0) begin
      if (m_rd_no == x_rs1_no && m_rd_no != x_rs2_no && m_rd_no != 0) begin
        mux_val_mx_wx = 1;
        x_rs1_data = stateM.rd_val_M;
      end if (m_rd_no == x_rs2_no && m_rd_no != x_rs1_no && m_rd_no != 0) begin
        mux_val_mx_wx = 2;
        x_rs2_data = stateM.rd_val_M;
      end if (m_rd_no == x_rs1_no && m_rd_no == x_rs2_no && m_rd_no != 0) begin
        mux_val_mx_wx = 3;
        x_rs1_data = stateM.rd_val_M;
        x_rs2_data = stateM.rd_val_M;
      end if (w_rd_no == x_rs1_no && w_rd_no != x_rs2_no && w_rd_no != m_rd_no && w_rd_no != 0) begin
        mux_val_mx_wx = 4;
        // x_rs1_data = stateW.rd_val_W;
        x_rs1_data = rd_val_mem_temp;
      end if (w_rd_no == x_rs2_no && w_rd_no != x_rs1_no && w_rd_no != m_rd_no && w_rd_no != 0) begin
        mux_val_mx_wx = 5;
        // x_rs2_data = stateW.rd_val_W;
        x_rs2_data = rd_val_mem_temp;
      end if (w_rd_no == x_rs1_no && w_rd_no == x_rs2_no && w_rd_no != m_rd_no && w_rd_no != 0) begin
        mux_val_mx_wx = 6;
        // x_rs2_data = stateW.rd_val_W;
        // x_rs1_data = stateW.rd_val_W;
        x_rs2_data = rd_val_mem_temp;
        x_rs1_data = rd_val_mem_temp;
        // edited: case for handling double bypass
      end if (m_rd_no == x_rs1_no && w_rd_no == x_rs2_no && x_rs1_no != x_rs2_no && (w_rd_no != 0 && m_rd_no != 0)) begin
        mux_val_mx_wx = 7;
        x_rs1_data = stateM.rd_val_M;
        // x_rs2_data = stateW.rd_val_W;
        x_rs2_data = rd_val_mem_temp;
      end if (m_rd_no == x_rs2_no && w_rd_no == x_rs1_no && x_rs1_no != x_rs2_no && (w_rd_no != 0 && m_rd_no != 0)) begin
        mux_val_mx_wx = 8;
        x_rs2_data = stateM.rd_val_M;
        // x_rs1_data = stateW.rd_val_W;
        x_rs1_data = rd_val_mem_temp;
      end
    end

    add_cin = 1'b0;
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
    address_bits_temp = 32'b0;
    // addr_to_dmem_temp = 32'b0;

    case (insn_opcode_x)
      OpcodeMiscMem: begin
        // addr_to_dmem_temp = stateX.addr_to_dmem_X;

        if(stateX.exe_control_X.insn_fence) begin 
          //we = 1'b0;
        end else begin
          illegal_insn = 1'b1;
        end 
      end
      
      OpcodeEnviron: begin
        // addr_to_dmem_temp = stateX.addr_to_dmem_X;

            if(stateX.exe_control_X.insn_ecall) begin
              halt_sig_temp = 1'b1;
            end
        end

      OpcodeLui: begin
        // addr_to_dmem_temp = stateX.addr_to_dmem_X;

        if(stateX.rd_no_X == 5'b0)
          rd_temp = 32'b0;
        else begin
          rd_temp = {stateX.insn_imem_X[31:12], 12'd0};
          rd_temp = {stateX.insn_imem_X[31:12], 12'd0};
        end
      end

      OpcodeJal: begin
        // addr_to_dmem_temp = stateX.addr_to_dmem_X;

        if (stateX.exe_control_X.insn_jal) begin
          rd_temp = stateX.pc_X + 32'd4;
          pcNext = stateX.pc_X + stateX.imm_i_sext_X;
          branch_taken = 1'b1;
        end 
        else begin 
          branch_taken = 1'b0;
        end
      end

      OpcodeJalr: begin
        // addr_to_dmem_temp = stateX.addr_to_dmem_X;

        if (stateX.exe_control_X.insn_jalr) begin 
          rd_temp = stateX.pc_X + 32'd4;
          pcNext = (($signed(x_rs1_data) + $signed(stateX.imm_i_sext_X)) & 32'hFFFFFFFE);
          branch_taken = 1'b1;
        end 
        else begin 
          branch_taken = 1'b0;
        end
      end 

      OpcodeAuipc: begin
        // addr_to_dmem_temp = stateX.addr_to_dmem_X;

        rd_temp = stateX.pc_X + {stateX.insn_X[31:12],12'd0};
      end


      OpcodeBranch: begin
        // addr_to_dmem_temp = stateX.addr_to_dmem_X;

        if(stateX.exe_control_X.insn_beq) begin 
          if(x_rs1_data == x_rs2_data) begin 
            pcNext = stateX.pc_X + stateX.imm_i_sext_X;
            
            branch_taken = 1'b1;
          end
          else begin 
            branch_taken = 1'b0;
          end 
        end else if(stateX.exe_control_X.insn_bne)begin
        
          if (x_rs1_data != x_rs2_data) begin
            pcNext = stateX.pc_X + stateX.imm_i_sext_X;
            
            branch_taken = 1'b1;
            end
          else begin 
            branch_taken = 1'b0;
          end 
        end  
        else if(stateX.exe_control_X.insn_blt)begin 
        
          if($signed(x_rs1_data) < $signed(x_rs2_data)) begin
            pcNext = stateX.pc_X + stateX.imm_i_sext_X;
            
            branch_taken = 1'b1;
          end 
          else begin 
            branch_taken = 1'b0;
          end
        end
        else if(stateX.exe_control_X.insn_bge)begin 
         
          if($signed(x_rs1_data) >= $signed(x_rs2_data)) begin
            pcNext = stateX.pc_X + stateX.imm_i_sext_X;
   
            branch_taken = 1'b1;
          end
          else begin 
            branch_taken = 1'b0;
          end 
        end 
        else if(stateX.exe_control_X.insn_bltu)begin 
        
          if($signed(x_rs1_data) < $unsigned(x_rs2_data)) begin
            pcNext = stateX.pc_X + stateX.imm_i_sext_X;
            branch_taken = 1'b1;
          end
          else begin 
            branch_taken = 1'b0;
          end
        end
            
        else if(stateX.exe_control_X.insn_bgeu)begin 
          if($signed(x_rs1_data) >= $unsigned(x_rs2_data)) begin
            pcNext = stateX.pc_X + stateX.imm_i_sext_X;
            branch_taken = 1'b1;
          end
          else begin 
            branch_taken = 1'b0;
          end
        end      
      end 

      OpcodeRegImm: begin 
        // addr_to_dmem_temp = stateX.addr_to_dmem_X;

        if(stateX.exe_control_X.insn_addi) begin 
          add_cin = 1'b0;
          // we = 1'b1;
          add_a = x_rs1_data;
          add_b = stateX.imm_i_sext_X;
          rd_temp = add_sum;
        end
        else if (stateX.exe_control_X.insn_slti) begin 
         
          //     we = 1'b1; 
          rd_temp = ($signed(stateX.imm_i_sext_X) > $signed(x_rs1_data)) ? 32'b1 : 32'b0;
        end
        else if(stateX.exe_control_X.insn_sltiu) begin
        
          //     we = 1'b1;
          rd_temp = ($signed(x_rs1_data) < $unsigned(stateX.imm_i_sext_X)) ? 32'b1 : 32'b0;
        end  
        else if(stateX.exe_control_X.insn_xori) begin 
        
          //     we = 1'b1;
          rd_temp = $signed(x_rs1_data) ^ stateX.imm_i_sext_X;
        end 
        else if(stateX.exe_control_X.insn_ori) begin
        
          //     we = 1'b1;
          rd_temp = $signed(x_rs1_data) | stateX.imm_i_sext_X;
        end
        else if(stateX.exe_control_X.insn_andi) begin
        
          //     we = 1'b1;
          rd_temp = $signed(x_rs1_data) & stateX.imm_i_sext_X;
        end
        else if(stateX.exe_control_X.insn_slli) begin
        
          //     we = 1'b1;
          rd_temp = (x_rs1_data << (stateX.imm_i_sext_X[4:0]));
        end
        else if(stateX.exe_control_X.insn_srli) begin
        
          //     we = 1'b1;
          rd_temp = (x_rs1_data >> (stateX.imm_i_sext_X[4:0]));
        end
        else if(stateX.exe_control_X.insn_srai) begin
        
          //     we = 1'b1;
          rd_temp = ($signed(x_rs1_data) >>> (stateX.imm_i_sext_X[4:0]));
        end
        else begin 
          illegal_insn = 1'b1;
        end 
      end

      OpcodeRegReg: begin
        // addr_to_dmem_temp = stateX.addr_to_dmem_X;
        if(stateX.exe_control_X.insn_add) begin 
          add_cin = 1'b0;
          // we = 1'b1;
          add_a = x_rs1_data;
          add_b = x_rs2_data;
          rd_temp = add_sum;
        end
        else if(stateX.exe_control_X.insn_sub) begin 
        
          add_cin = 1'b1;
          // we = 1'b1;
          add_a = x_rs1_data;
          add_b = ~x_rs2_data;
          rd_temp = add_sum;
        end
        else if(stateX.exe_control_X.insn_sll) begin 
        
          // we = 1'b1;
          rd_temp = x_rs1_data << x_rs2_data[4:0];
        end
        else if(stateX.exe_control_X.insn_slt) begin  
         
          //   we = 1'b1;
          rd_temp = $signed(x_rs1_data) < $signed(x_rs2_data) ? 32'b1 : 32'b0;
        end
        else if(stateX.exe_control_X.insn_sltu) begin 
        
          //   we = 1'b1;
          rd_temp = (x_rs1_data < $unsigned(x_rs2_data))? 32'b1:32'b0;
        end
        else if(stateX.exe_control_X.insn_xor) begin 
         
          //   we = 1'b1;
          rd_temp = x_rs1_data ^ x_rs2_data;
        end
        else if(stateX.exe_control_X.insn_srl) begin 
        
          //   we = 1'b1;
          rd_temp = x_rs1_data >> (x_rs2_data[4:0]);
        end
        else if(stateX.exe_control_X.insn_sra) begin 
         
          //   we = 1'b1;
          rd_temp = $signed(x_rs1_data) >>> (x_rs2_data[4:0]);
        end
        else if(stateX.exe_control_X.insn_or) begin 
        
          //   we = 1'b1;
          rd_temp = x_rs1_data | x_rs2_data;
        end
        else if(stateX.exe_control_X.insn_and) begin 
         
          //   we = 1'b1;
          rd_temp = x_rs1_data & x_rs2_data;
        end
        else if(stateX.exe_control_X.insn_mul) begin 
        
          product = x_rs1_data * x_rs2_data;
          rd_temp = product[31:0];
        end 
        else if(stateX.exe_control_X.insn_mulh) begin 
        
          product = ($signed(x_rs1_data) * $signed(x_rs2_data));
          rd_temp = product[63:32];
        end  
        else if(stateX.exe_control_X.insn_mulhsu) begin
        
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
        else if(stateX.exe_control_X.insn_mulhu) begin 
        
          product = ($unsigned(x_rs1_data) *  $unsigned(x_rs2_data));
          rd_temp = product[63:32];
        end
        else if(stateX.exe_control_X.insn_div) begin 
        
          
          // dividend = x_rs1_data[31] ? (~x_rs1_data + 1) : x_rs1_data;
          // divisor = x_rs2_data[31] ? (~x_rs2_data + 1) : x_rs2_data;
          // rd_temp = (x_rs1_data == 0 | x_rs2_data == 0) ? $signed(32'hFFFFFFFF) :
          //                                                 ((div_rs1 != div_rs2) ?
          //                                                 (~quotient + 1) : quotient);

          // rs1d = x_rs1_data[31];
          // rs2d = x_rs2_data[31];
          // zero_check = (x_rs1_data == 0) | (x_rs2_data == 0);
          dividend = x_rs1_data[31] ? (~x_rs1_data + 1) : x_rs1_data;
          divisor = x_rs2_data[31] ? (~x_rs2_data + 1) : x_rs2_data;
          // rd_temp = ((x_rs1_data == 0) | (x_rs2_data == 0)) ? $signed(32'hFFFFFFFF) : ((x_rs1_data[31] != x_rs2_data[31]) ? (~quotient + 1) : quotient);

        end
        else if(stateX.exe_control_X.insn_divu) begin 
          dividend = $unsigned(x_rs1_data);
          divisor = $unsigned(x_rs2_data);
          rd_temp = (x_rs1_data == 0 | x_rs2_data == 0) ? $signed(32'hFFFFFFFF) : quotient;
        end
       
        else if (stateX.exe_control_X.insn_rem) begin 
          dividend = x_rs1_data[31] ? (~x_rs1_data + 1) : x_rs1_data;
          divisor = x_rs2_data[31] ? (~x_rs2_data + 1) : x_rs2_data;
          rd_temp = (x_rs1_data == 0 | x_rs2_data == 0) ? x_rs1_data[31] ?
                                                          (~x_rs1_data + 1) : x_rs1_data :
                                                          (x_rs1_data[31] == 1'b1) ?
                                                            (~remainder + 1) : (remainder);
        end 
        else if(stateX.exe_control_X.insn_remu)begin
          dividend = $unsigned(x_rs1_data);
          divisor =  $unsigned(x_rs2_data);
          rd_temp = remainder;
        end  
        else begin 
          illegal_insn = 1'b1;
        end
      end

      OpcodeStore: begin
        // address_bits_temp = stateX.rs1_data_temp_X + stateX.imm_i_sext_X;
        // address_bits_temp = stateX.rs1_data_temp_X + stateX.imm_i_sext_X;
        address_bits_temp = x_rs1_data + stateX.imm_i_sext_X;      
      end

      OpcodeLoad: begin
        if(((stateM.insn_opcode_M == OpcodeRegReg) || (stateM.insn_opcode_M == OpcodeRegImm) && (stateM.rd_no_M == stateX.rs1_no_X))||
         ((stateW.insn_opcode_W == OpcodeRegReg) || (stateW.insn_opcode_W == OpcodeRegImm) && (stateW.rd_no_W == stateX.rs1_no_X)) ||
         ((stateM.insn_opcode_M == OpcodeAuipc) && (stateM.rd_no_M == stateX.rs1_no_X)) ||
          ((stateW.insn_opcode_W == OpcodeAuipc) && (stateW.rd_no_W == stateX.rs1_no_X)))
          begin
            if(stateM.rd_no_M == stateX.rs1_no_X)
              address_bits_temp = stateM.rd_val_M+ stateX.imm_i_sext_X;
            else if(stateW.rd_no_W == stateX.rs1_no_X)
              address_bits_temp = stateW.rd_val_W + stateX.imm_i_sext_X;
          end
          
        else
          address_bits_temp = stateX.rs1_data_temp_X + stateX.imm_i_sext_X;
        // address_bits_temp = stateX.rs1_data_temp_X + stateX.imm_i_sext_X;
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
  assign lw_stall_m = stateM.lw_stall_m;
  assign div_stall_m = stateM.div_stall_m;
  assign mux_fence_m = stateM.mux_fence_m;
  assign branch_taken_m = stateM.branch_taken_M;

  stage_memory_t stateM;
  logic [31:0] rd_val_temp;//Temporary variable to store the value to be written to the register file in memory stage
  logic [31:0]stateM_store_data_to_dmem;
  logic [3:0]stateM_store_we_to_dmem_M; 
  // assign addr_to_dmem = stateM.addr_to_dmem_M & 32'hFFFFFFFC;

  always_ff @(posedge clk) begin
    if (rst) begin
      stateM <= '{
        pc_M: 0,
        insn_M: 0,
        cycle_status_M: CYCLE_RESET,
        rd_no_M: 0,
        rd_val_M: 0,
        rs1_no_M: 0,
        rs1_data_temp_M: 0,
        rs2_no_M: 0,
        rs2_data_temp_M: 0,
        addr_to_dmem_M: 0,
        store_we_to_dmem_M: 0,
        store_data_to_dmem_M: 0,
        insn_opcode_M: 0,
        halt_sig_M: 0,
        branch_taken_M: 0,
        address_bits_M: 0,
        pcNext_M: 0,
        lw_stall_m: 0,
        div_stall_m: 0,
        mux_fence_m: 0,
        mem_control_M: '{default:0}

      };
    end else begin
      begin
        stateM <= '{
          pc_M: stateX.pc_X,
          insn_opcode_M: stateX.insn_opcode_X,
          insn_M: stateX.insn_X,
          cycle_status_M: stateX.cycle_status_X,
          rd_no_M: stateX.rd_no_X,
          rd_val_M: rd_temp,
          rs1_no_M: stateX.rs1_no_X,
          rs1_data_temp_M:x_rs1_data,
          rs2_no_M: stateX.rs2_no_X,
          rs2_data_temp_M: ((stateW.insn_opcode_W == OpcodeLoad) && //WM bypass
                          (stateM.insn_opcode_M == OpcodeStore)&&
                          (stateW.rd_no_W == stateM.rs2_no_M))?stateW.rd_val_W:x_rs2_data,
          addr_to_dmem_M: addr_to_dmem_temp,
          store_we_to_dmem_M: stateX.store_we_to_dmem_X,
          store_data_to_dmem_M: stateX.store_data_to_dmem_X,
          halt_sig_M: halt_sig_temp,
          branch_taken_M: branch_taken,
          address_bits_M: address_bits_temp,
          pcNext_M: pcNext,
          lw_stall_m: loadStall,
          div_stall_m: divStall,
          mux_fence_m: fenceStall,
          mem_control_M: stateX.exe_control_X//fenceStall || divStall || loadStall
        };
      end
    end
    
  end
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_1memory (
      .insn  (stateM.insn_M),
      .disasm(m_disasm)
  );

  logic [`REG_SIZE] addr_to_dmem_temp;
  // logic [31:0] address_bits_temp;
  logic [`REG_SIZE] rd_val_mem_temp;
  logic [`REG_SIZE] rs1_val_temp;
  logic [`REG_SIZE] rs2_val_temp;
  logic [`REG_SIZE] store_data_temp_mem;
  logic [`REG_SIZE] address_bits_mem;
  logic [`REG_SIZE] store_data_to_dmem_temp;

  logic [`REG_SIZE] addr_to_dmem_rdata;
  logic [`REG_SIZE] addr_to_dmem_wdata;
  logic [`REG_SIZE] rdata_data_from_dmem_temp;
  logic [`REG_SIZE] wdata_data_to_dmem_temp;
  //logic [3:0] rdata_we_to_dmem_temp;
  logic [3:0] wdata_we_to_dmem_temp;
  //logic rdata_valid;
  logic wdata_valid;
  logic ardata_valid;
  logic awdata_valid;
  logic rdata_ready;
  logic wdata_bready;

  // edited
  logic [1:0] wm_mux;
  logic [1:0] div_rem_mux;
  logic [`REG_SIZE] div_rem_two_cycle_data;

  always_latch begin
  
    divMulticycle = 0;
    address_bits_mem = stateM.address_bits_M;
    selectDivider = 0;
    wm_mux = 2'b0;

    addr_to_dmem_wdata = 0;
    wdata_we_to_dmem_temp = 0;
    wdata_data_to_dmem_temp = 0;
    awdata_valid = 0;
    wdata_valid = 0;
    wdata_bready = 0;

    //addr_to_dmem_rdata = 0;
    //rdata_data_from_dmem_temp = 0;
    ardata_valid = 0;
    //rdata_ready = 0;

    // store_we_to_dmem_temp = 0;
    
    if (stateW.insn_opcode_W == OpcodeLoad && stateW.rd_no_W != 5'b0) begin
      if (stateW.rd_no_W == stateM.rs2_no_M && stateW.rd_no_W != stateM.rs1_no_M) begin
        wm_mux = 2'b01;
        address_bits_mem = stateM.address_bits_M;
      end else if (stateW.rd_no_W != stateM.rs2_no_M && stateW.rd_no_W == stateM.rs1_no_M) begin
        wm_mux = 2'b10;
        //address_bits_mem = stateW.rd_val_W;
      end else if (stateW.rd_no_W == stateM.rs2_no_M && stateW.rd_no_W == stateM.rs1_no_M) begin
        wm_mux = 2'b11;
        //address_bits_mem = stateW.rd_val_W;
        address_bits_mem = stateM.address_bits_M;
      end
    end

    if (stateM.mem_control_M.insn_div == 1'b1) begin
        //divMulticycle = o_quotient_temp;
        selectDivider = 2'b1;
        if (stateM.rs1_data_temp_M == 0 | stateM.rs2_data_temp_M == 0) begin  
          divMulticycle = $signed(32'hFFFF_FFFF);             
        end 
        else if(stateM.rs1_data_temp_M[31] != stateM.rs2_data_temp_M[31]) begin
          divMulticycle = (~quotient + 32'b1);
        end 
        else begin 
          divMulticycle = quotient;
        end 
    end else if (stateM.mem_control_M.insn_divu == 1'b1) begin
        divMulticycle = quotient;
        selectDivider = 2'b1;
    end else if (stateM.mem_control_M.insn_rem == 1'b1) begin
        selectDivider = 2'b10;
        if(stateM.rs1_data_temp_M == 32'b0) begin  
          divMulticycle = (stateM.rs2_data_temp_M[31]) ? 
            (~stateM.rs2_data_temp_M + 32'b1) : stateM.rs2_data_temp_M;             
        end 
        else if((stateM.rs1_data_temp_M[31])) begin
          divMulticycle = (~remainder + 32'b1);
        end 
        else begin 
          divMulticycle = remainder;
        end
    end else if (stateM.mem_control_M.insn_remu == 1'b1 ) begin
        divMulticycle = remainder;
        selectDivider = 2'b10;
    end
    
    case (stateM.insn_opcode_M)
      OpcodeStore: begin
        // addr_to_dmem_temp = (address_bits_mem & 32'hFFFF_FFFC);
        addr_to_dmem_wdata = (address_bits_mem & 32'hFFFF_FFFC);
        awdata_valid = 1'b1;
        // store_data_temp_mem = (wm_mux == 2'b1 || wm_mux == 2'b11) ? stateW.rd_val_W : stateM.rs2_data_temp_M;

        store_data_temp_mem = (wm_mux == 2'b1 || wm_mux == 2'b11) ? rd_val_mem_temp : stateM.rs2_data_temp_M;
        if(stateM.mem_control_M.insn_sb)begin
          //store_data_to_dmem_temp = (wm_mux == 2'b10) ? {{4{stateW.rd_val_W[7:0]}}} : {{4{stateM.rs2_data_temp_M[7:0]}}};
          if(address_bits_mem[1:0] == 2'b00) begin
            // store_data_to_dmem_temp = {{24{1'b0}},{store_data_temp_mem[7:0]}};
            // store_we_to_dmem_temp = 4'b0001;

            wdata_data_to_dmem_temp = {{24{1'b0}},{store_data_temp_mem[7:0]}};
            wdata_we_to_dmem_temp = 4'b0001;
            wdata_valid = 1'b1;
            wdata_bready = 1'b1;
          end
          else if(address_bits_mem[1:0] == 2'b01)begin
            // store_data_to_dmem_temp = {{16{1'b0}},{store_data_temp_mem[7:0]},{8{1'b0}}};
            // store_we_to_dmem_temp= 4'b0010;

            wdata_data_to_dmem_temp = {{16{1'b0}},{store_data_temp_mem[7:0]},{8{1'b0}}};
            wdata_we_to_dmem_temp = 4'b0010;
            wdata_valid = 1'b1;
            wdata_bready = 1'b1;
          end
          else if(address_bits_mem[1:0] == 2'b10) begin 
            // store_data_to_dmem_temp = {{8{1'b0}},{store_data_temp_mem[7:0]},{16{1'b0}}};
            // store_we_to_dmem_temp= 4'b0100;
            wdata_data_to_dmem_temp = {{8{1'b0}},{store_data_temp_mem[7:0]},{16{1'b0}}};
            wdata_we_to_dmem_temp = 4'b0100;
            wdata_valid = 1'b1;
            wdata_bready = 1'b1;
          end
          else begin
            // store_data_to_dmem_temp = {{store_data_temp_mem[7:0]},{24{1'b0}}};
            // store_we_to_dmem_temp= 4'b1000; 
            wdata_data_to_dmem_temp = {{store_data_temp_mem[7:0]},{24{1'b0}}};
            wdata_we_to_dmem_temp = 4'b1000;
            wdata_valid = 1'b1;
            wdata_bready = 1'b1;
          end 
        end
        else if(stateM.mem_control_M.insn_sh)begin
          //store_data_to_dmem_temp = (wm_mux == 2'b10) ? {{2{stateW.rd_val_W[15:0]}}} : {{2{stateM.rs2_data_temp_M[15:0]}}};
          if(address_bits_mem[1:0] == 2'b00) begin
            // store_data_to_dmem_temp = {{16{1'b0}},{store_data_temp_mem[15:0]}};
            // store_we_to_dmem_temp= 4'b0011;
            wdata_data_to_dmem_temp = {{16{1'b0}},{store_data_temp_mem[15:0]}};
            wdata_we_to_dmem_temp= 4'b0011;
            wdata_valid = 1'b1;
            wdata_bready = 1'b1;
          end
          else begin
            // store_data_to_dmem_temp = {{store_data_temp_mem[15:0]},{16{1'b0}}};
            // store_we_to_dmem_temp= 4'b1100;
            wdata_data_to_dmem_temp = {{store_data_temp_mem[15:0]},{16{1'b0}}};
            wdata_we_to_dmem_temp= 4'b1100;
            wdata_valid = 1'b1;
            wdata_bready = 1'b1;
          end 
        end
        else if(stateM.mem_control_M.insn_sw)begin 
        //   store_data_to_dmem_temp = (wm_mux == 2'b1 || wm_mux == 2'b11) ? stateW.rd_val_W : stateM.rs2_data_temp_M;
        //   store_we_to_dmem_temp= 4'b1111;
          wdata_data_to_dmem_temp = (wm_mux == 2'b1 || wm_mux == 2'b11) ? rd_val_mem_temp : stateM.rs2_data_temp_M; 
          wdata_we_to_dmem_temp= 4'b1111;
          wdata_valid = 1'b1;
          wdata_bready = 1'b1;
        end
      end

      OpcodeLoad: begin
        address_bits_mem = stateM.address_bits_M;
        addr_to_dmem_rdata = (address_bits_mem & 32'hFFFF_FFFC);
        ardata_valid = 1'b1;
      end

      default: begin
        // rd_val_mem_temp = stateM.rd_val_M;
      end
  endcase
    end
  // end
  

  /****************/
  /* WRITEBACK STAGE */
  /****************/
  stage_write_t stateW;
  always_ff @(posedge clk) begin
    if (rst) begin
      stateW <= '{
        pc_W: 0,
        insn_W: 0,
        cycle_status_W: CYCLE_RESET,
        rd_no_W: 0,
        rd_val_W: 0,
        rs1_no_W: 0,
        rs1_data_temp_W: 0,
        rs2_no_W: 0,
        rs2_data_temp_W: 0,
        insn_opcode_W: 0,
        halt_sig_W: 0,
        store_data_to_dmem_W:'{default:0},
        store_we_to_dmem_W:'{default:0},
        address_bits_wb: 0,
        write_control_W: 0
        
      };
    end else begin
      begin
        stateW <= '{
          pc_W: stateM.pc_M,
          insn_W: stateM.insn_M,
          cycle_status_W: stateM.cycle_status_M,
          rd_no_W: stateM.rd_no_M,
          // rd_val_W: ((selectDivider == 2'b1 || selectDivider == 2'b10) ?
          //             divMulticycle : (stateM.insn_opcode_M == OpcodeLoad) ?
          //             rd_val_temp : stateM.rd_val_M),
        //   rd_val_W: selectDivider == 2'b1 || selectDivider == 2'b10 ? 
        //           divMulticycle : rd_val_mem_temp,
          rd_val_W: selectDivider == 2'b1 || selectDivider == 2'b10 ? 
                  divMulticycle : stateM.rd_val_M,
          // rd_val_W: selectDivider == 2'b1 || selectDivider == 2'b10 ? 
          //         divMulticycle : rd_val_mem_temp,
          rs1_no_W: stateM.rs1_no_M,
          rs1_data_temp_W: stateM.rs1_data_temp_M,
          rs2_no_W: stateM.rs2_no_M,
          rs2_data_temp_W: stateM.rs2_data_temp_M,
          insn_opcode_W: stateM.insn_opcode_M,
          halt_sig_W: stateM.halt_sig_M,
          store_data_to_dmem_W: stateM_store_data_to_dmem,
          store_we_to_dmem_W: stateM_store_we_to_dmem_M,
          address_bits_wb: stateM.address_bits_M,
          write_control_W: stateM.mem_control_M
        };
      end
    end
    // dmem.AWVALID <= dmem.AWVALID^1'b1;
    // dmem.WVALID <= dmem.WVALID^1'b1;
  end

  wire [255:0] wb_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_1writeback (
      .insn  (stateW.insn_W),
      .disasm(wb_disasm)
  );

  always_comb begin
    rd_val_mem_temp = stateW.rd_val_W;
    rdata_ready = 0;

    if (stateW.insn_opcode_W == OpcodeLoad) begin
      if(stateW.write_control_W.insn_lb) begin
        if(stateW.address_bits_wb[1:0] == 2'b00) begin
          //rd_val_mem_temp = {{24{load_data_from_dmem[7]}},load_data_from_dmem[7:0]};
          rd_val_mem_temp = {{24{rdata_data_from_dmem_temp[7]}},rdata_data_from_dmem_temp[7:0]};
          rdata_ready = 1'b1;
          //assign f_insn = imem.RDATA;
        end 
        else if(stateW.address_bits_wb[1:0] == 2'b01) begin 
          //rd_val_mem_temp = {{24{load_data_from_dmem[15]}},load_data_from_dmem[15:8]};
          rd_val_mem_temp = {{24{rdata_data_from_dmem_temp[15]}},rdata_data_from_dmem_temp[15:8]};
          rdata_ready = 1'b1;
        end 
        else if(stateW.address_bits_wb[1:0] == 2'b10) begin 
          //rd_val_mem_temp = {{24{load_data_from_dmem[23]}},load_data_from_dmem[23:16]};
          rd_val_mem_temp = {{24{rdata_data_from_dmem_temp[23]}},rdata_data_from_dmem_temp[23:16]};
          rdata_ready = 1'b1;
        end 
        else begin
          //rd_val_mem_temp = {{24{load_data_from_dmem[31]}},load_data_from_dmem[31:24]}; 
          rd_val_mem_temp = {{24{rdata_data_from_dmem_temp[31]}},rdata_data_from_dmem_temp[31:24]};
          rdata_ready = 1'b1;
        end 
      end  
      else if(stateW.write_control_W.insn_lh)begin 
        if(stateW.address_bits_wb[1:0] == 2'b00) begin
          //rd_val_mem_temp = {{16{load_data_from_dmem[15]}},load_data_from_dmem[15:0]};
          rd_val_mem_temp = {{16{rdata_data_from_dmem_temp[15]}},rdata_data_from_dmem_temp[15:0]};
          rdata_ready = 1'b1; 
        end 
        else begin
          //rd_val_mem_temp = {{16{load_data_from_dmem[31]}},load_data_from_dmem[31:16]};
          rd_val_mem_temp = {{16{rdata_data_from_dmem_temp[31]}},rdata_data_from_dmem_temp[31:16]}; 
          rdata_ready = 1'b1; 
        end 
      end
      else if(stateW.write_control_W.insn_lw)begin 
        //rd_val_mem_temp = load_data_from_dmem[31:0];
        rd_val_mem_temp = rdata_data_from_dmem_temp[31:0];
        rdata_ready = 1'b1; 
      end 
      else if(stateW.write_control_W.insn_lbu)begin 
        if(stateW.address_bits_wb[1:0] == 2'b00) begin 
          //rd_val_mem_temp = {{24'b0},load_data_from_dmem[7:0]};
          rd_val_mem_temp = {{24'b0}, rdata_data_from_dmem_temp[7:0]};
          rdata_ready = 1'b1;
        end 
        else if(stateW.address_bits_wb[1:0] == 2'b01) begin
          //rd_val_mem_temp = {{24'b0},load_data_from_dmem[15:8]};
          rd_val_mem_temp = {{24'b0},rdata_data_from_dmem_temp[15:8]};
          rdata_ready = 1'b1;
        end 
        else if(stateW.address_bits_wb[1:0] == 2'b10) begin
          //rd_val_mem_temp = {{24'b0},load_data_from_dmem[23:16]};
          rd_val_mem_temp = {{24'b0},rdata_data_from_dmem_temp[23:16]};
          rdata_ready = 1'b1;
        end 
        else begin
          //rd_val_mem_temp = {{24'b0},load_data_from_dmem[31:24]};
          rd_val_mem_temp = {{24'b0},rdata_data_from_dmem_temp[31:24]};
          rdata_ready = 1'b1;
        end 
      end 
      else if(stateW.write_control_W.insn_lhu)begin 
        if(stateW.address_bits_wb[1:0] == 2'b00) begin
          //rd_val_mem_temp = {{16'b0},load_data_from_dmem[15:0]};
          rd_val_mem_temp = {{16'b0},rdata_data_from_dmem_temp[15:0]};
          rdata_ready = 1'b1;
        end 
        else begin
          //rd_val_mem_temp = {{16'b0},load_data_from_dmem[31:16]};
          rd_val_mem_temp = {{16'b0},rdata_data_from_dmem_temp[31:16]};
          rdata_ready = 1'b1;
        end 
      end
    end
  end

  // assign store_data_to_dmem = stateW.store_data_to_dmem_W;
  // assign store_we_to_dmem = stateW.store_we_to_dmem_W;
  // assign addr_to_dmem = addr_to_dmem_temp;
//   assign dmem.WSTRB = store_we_to_dmem_temp;
//   assign dmem.WDATA = store_data_to_dmem_temp;
  assign we = (stateW.insn_opcode_W == OpcodeBranch ||
                  stateW.insn_opcode_W == OpcodeStore) ||
                  (stateW.rd_no_W == 0)? 1'b0 : 1'b1;//If not store or branch or rd_no is 0, we = 1
  assign halt = stateW.halt_sig_W;
//   assign dmem.AWADDR = addr_to_dmem_temp;

  assign dmem.AWADDR = addr_to_dmem_wdata;
  assign dmem.WSTRB = wdata_we_to_dmem_temp;
  assign dmem.WDATA = wdata_data_to_dmem_temp;
  assign dmem.AWVALID = awdata_valid;
  assign dmem.WVALID = wdata_valid;
  assign dmem.BREADY = wdata_bready;

  assign dmem.ARADDR = addr_to_dmem_rdata;
  assign rdata_data_from_dmem_temp = dmem.RDATA;
  assign dmem.ARVALID = ardata_valid;
  assign dmem.RREADY = rdata_ready;

  // assign addr_to_dmem = addr_to_dmem_temp & 32'hFFFFFFFC;
  // assign addr_to_dmem = stateM.addr_to_dmem_M & 32'hFFFFFFFC;

  assign trace_writeback_cycle_status = stateW.cycle_status_W;
  assign trace_writeback_pc = stateW.pc_W;
  assign trace_writeback_insn = stateW.insn_W;
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
    input wire clk,
    input wire rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  // HW5 memory interface
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

  // HW6 memory interface
  axi_clkrst_if axi_cr (.ACLK(clk), .ARESETn(~rst));
  axi_if axi_data ();
  axi_if axi_insn ();
  MemoryAxiLite #(.NUM_WORDS(8192)) mem (
    .axi(axi_cr),
    .insn(axi_insn.subord),
    .data(axi_data.subord)
  );

  DatapathAxilMemory datapath (
      .clk(clk),
      .rst(rst),
      .imem(axi_insn.manager),
      .dmem(axi_data.manager),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );
  // DatapathAxilMemory datapath (
  //     .clk(clk),
  //     .rst(rst),
  //     .imem(axi_insn.manager),
  //     .addr_to_dmem(mem_data_addr),
  //     .store_data_to_dmem(mem_data_to_write),
  //     .store_we_to_dmem(mem_data_we),
  //     .load_data_from_dmem(mem_data_loaded_value),
  //     .halt(halt),
  //     .trace_writeback_pc(trace_writeback_pc),
  //     .trace_writeback_insn(trace_writeback_insn),
  //     .trace_writeback_cycle_status(trace_writeback_cycle_status)
  // );

  

endmodule
