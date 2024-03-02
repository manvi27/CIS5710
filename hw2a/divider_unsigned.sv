/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // Extra bit to store the initial as well as final values
    // Temporary Quotient for intermediate values
    wire [31:0] temp_quotient[32:0];
    // Temporary Remainder for intermediate values
    wire [31:0] temp_remainder[32:0];
    // Temporary Dividend for intermediate values
    wire [31:0] temp_dividend[32:0];

    // Assign Final bit to Output of Quotient and Remainder
    // Assign 0 if Divisor is 0
    assign  o_quotient = (i_divisor == 32'b0) ? 32'b0 : temp_quotient[32];
    assign o_remainder = (i_divisor == 32'b0) ? 32'b0 : temp_remainder[32];

    // Initialize first wire for each temporary variable with the input
    assign temp_quotient[0] = 32'b0;
    assign temp_remainder[0] = 32'b0;
    assign temp_dividend[0] = i_dividend;

    // Iterating variable
    genvar i;
    // Call Single iteration Divider 32 times
    for( i = 0; i < 32; i = i + 1) begin

        divu_1iter div(.i_dividend(temp_dividend[i]), .i_divisor(i_divisor), .i_remainder(temp_remainder[i]), 
                        .i_quotient(temp_quotient[i]), .o_dividend(temp_dividend[i+1]), .o_remainder(temp_remainder[i+1]),
                        .o_quotient(temp_quotient[i+1]));

    end


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
  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }
    */

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
