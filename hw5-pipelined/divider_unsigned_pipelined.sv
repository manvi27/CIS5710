/* 
    Manvi Agarwal (iamanvi)
    Adithya Rajeev (adithyar)
*/

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned_pipelined (
    input wire clk, rst,
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here
    logic [31:0] dividend_stage_1[15:0];
    logic [31:0] remainder_stage_1[15:0];
    logic [31:0] quotient_stage_1[15:0];
    logic [31:0] dividend_stage_2[15:0];
    logic [31:0] remainder_stage_2[15:0];
    logic [31:0] quotient_stage_2[15:0];

    reg [31:0] dividend1;
    reg [31:0] divisor1;
    reg [31:0] remainder1;
    reg [31:0] quotient1;

    genvar i, j;
    for(i = 0; i < 16; i = i + 1) begin : Stage1
        if( i == 0) begin : Iteration1
            divu_1iter divu1_1(.i_dividend(i_dividend), 
                            .i_divisor(i_divisor), 
                            .i_remainder(32'd0), 
                            .i_quotient(32'd0), 
                            .o_dividend(dividend_stage_1[0]), 
                            .o_remainder(remainder_stage_1[0]), 
                            .o_quotient(quotient_stage_1[0]));
        end : Iteration1
        else begin : Iteration2
            divu_1iter divu1_2(.i_dividend(dividend_stage_1[i-1]), 
                            .i_divisor(i_divisor), 
                            .i_remainder(remainder_stage_1[i-1]),
                            .i_quotient(quotient_stage_1[i-1]), 
                            .o_dividend(dividend_stage_1[i]), 
                            .o_remainder(remainder_stage_1[i]), 
                            .o_quotient(quotient_stage_1[i]));
        end : Iteration2
    end : Stage1

    always @(posedge clk) begin
        if (rst) begin
            dividend1 <= 0;
            divisor1 <= 0;
            remainder1 <= 0;
            quotient1 <= 0;
        end else begin
            dividend1 <= dividend_stage_1[15];
            divisor1 <= i_divisor;
            remainder1 <= remainder_stage_1[15];
            quotient1 <= quotient_stage_1[15];
        end
    end

    for(j = 0; j < 16; j=j+1) begin : Stage2
        if( j == 0)begin : Iteration1
            divu_1iter divu2_1(.i_dividend(dividend1), 
                            .i_divisor(divisor1), 
                            .i_remainder(remainder1), 
                            .i_quotient(quotient1), 
                            .o_dividend(dividend_stage_2[0]), 
                            .o_remainder(remainder_stage_2[0]), 
                            .o_quotient(quotient_stage_2[0]));
        end : Iteration1
        else begin : Iteration2
            divu_1iter divu2_2(.i_dividend(dividend_stage_2[j-1]), 
                            .i_divisor(divisor1), 
                            .i_remainder(remainder_stage_2[j-1]),
                            .i_quotient(quotient_stage_2[j-1]), 
                            .o_dividend(dividend_stage_2[j]), 
                            .o_remainder(remainder_stage_2[j]), 
                            .o_quotient(quotient_stage_2[j]));
        end : Iteration2
    end : Stage2

    assign o_remainder = remainder_stage_2[15];
    assign o_quotient = quotient_stage_2[15];

endmodule


module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // Wires to store temporary remainder
    wire [31:0] temp_remainder;
    // Calculate Temporary Remainder
    assign temp_remainder = (i_remainder << 1) | ((i_dividend >> 31) & 32'b1);
    // Output Quotient Calculation
    assign o_quotient = (temp_remainder < i_divisor) ? (i_quotient) << 1 : (i_quotient << 1) | 32'b1;
    // Output Remainder Calculation
    assign o_remainder = (temp_remainder < i_divisor) ? temp_remainder : temp_remainder - i_divisor;
    // Update Dividend
    assign o_dividend = i_dividend << 1; 

endmodule
