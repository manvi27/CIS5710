`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   assign pout = (& pin[3:0]); 
   assign gout = gin[3] |
                  pin[3] & gin[2] |
                  pin[3] & pin[2] & gin[1] |
                  pin[3] & pin[2] & pin[1] & gin[0];
   assign cout[0] = gin[0] |
                     pin[0] & cin;
   assign cout[1] = gin[1] |
                     pin[1] & gin[0] |
                     pin[1] & pin[0] & cin;
   assign cout[2] = gin[2] |
                     pin[2] & gin[1] |
                     pin[2] &  pin[1] & gin[0] |
                     pin[2] &  pin[1] & pin[0] & cin;

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   assign pout = (& pin[7:0]);
   assign gout = gin[7] |
                  pin[7] & gin[6] |
                  pin[7] & pin[6] & gin[5] |
                  pin[7] & pin[6] & pin[5] & gin[4] |
                  pin[7] & pin[6] & pin[5] & pin[4] & gin[3] |
                  pin[7] & pin[6] & pin[5] & pin[4] & pin[3] & gin[2] |
                  pin[7] & pin[6] & pin[5] & pin[4] & pin[3] & pin[2] & gin[1] |
                  pin[7] & pin[6] & pin[5] & pin[4] & pin[3] & pin[2] & pin[1] & gin[0];
   assign cout[0] = gin[0] |
                     pin[0] & cin;
   assign cout[1] = gin[1] |
                     pin[1] & gin[0] |
                     pin[1] & pin[0] & cin;
   assign cout[2] = gin[2] |
                     pin[2] & gin[1] |
                     pin[2] &  pin[1] & gin[0] |
                     pin[2] &  pin[1] & pin[0] & cin;
   assign cout[3] = gin[3] |
                     pin[3] & gin[2] |
                     pin[3] &  pin[2] & gin[1] |
                     pin[3] &  pin[2] & pin[1] & gin[0] |
                     pin[3] &  pin[2] & pin[1] & pin[0] & cin;
   assign cout[4] = gin[4] |
                     pin[4] & gin[3] |
                     pin[4] &  pin[3] & gin[2] |
                     pin[4] &  pin[3] & pin[2] & gin[1] |
                     pin[4] &  pin[3] & pin[2] & pin[1] & gin[0] |
                     pin[4] &  pin[3] & pin[2] & pin[1] & pin[0] & cin;
   assign cout[5] = gin[5] |
                     pin[5] & gin[4] |
                     pin[5] &  pin[4] & gin[3] |
                     pin[5] &  pin[4] & pin[3] & gin[2] |
                     pin[5] &  pin[4] & pin[3] & pin[2] & gin[1] |
                     pin[5] &  pin[4] & pin[3] & pin[2] & pin[1] & gin[0] |
                     pin[5] &  pin[4] & pin[3] & pin[2] & pin[1] & pin[0] & cin;
   assign cout[6] = gin[6] |
                     pin[6] & gin[5] |
                     pin[6] &  pin[5] & gin[4] |
                     pin[6] &  pin[5] & pin[4] & gin[3] |
                     pin[6] &  pin[5] & pin[4] & pin[3] & gin[2] |
                     pin[6] &  pin[5] & pin[4] & pin[3] & pin[2] & gin[1] |
                     pin[6] &  pin[5] & pin[4] & pin[3] & pin[2] & pin[1] & gin[0] | 
                     pin[6] &  pin[5] & pin[4] & pin[3] & pin[2] & pin[1] & pin[0] & cin;  

endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   wire [31:0] g, p, carry;

   wire g31_0; 
   wire p31_0; 

   assign carry[0] = cin; 

   wire [3:0] g_grp, p_grp;
   wire [2:0] car_grp;

   assign carry[24] = car_grp[2]; 
   assign carry[16] = car_grp[1]; 
   assign carry[8] = car_grp[0]; 

   genvar i;

   for(i = 0; i < 32; i = i + 1) begin
      gp1 g_mod(.a(a[i]), .b(b[i]), .g(g[i]), .p(p[i]));
   end

    gp8 gp8_1(.gin(g[7:0]), .pin(p[7:0]), .cin(carry[0]), .gout(g_grp[0]), .pout(p_grp[0]), .cout(carry[7:1]));

    gp8 gp8_2(.gin(g[15:8]), .pin(p[15:8]), .cin(car_grp[0]), .gout(g_grp[1]), .pout(p_grp[1]), .cout(carry[15:9]));

    gp8 gp8_3(.gin(g[23:16]), .pin(p[23:16]), .cin(car_grp[1]), .gout(g_grp[2]), .pout(p_grp[2]), .cout(carry[23:17]));

    gp8 gp8_4(.gin(g[31:24]), .pin(p[31:24]), .cin(car_grp[2]), .gout(g_grp[3]), .pout(p_grp[3]), .cout(carry[31:25]));

    gp4 gp4_final(.gin(g_grp[3:0]), .pin(p_grp[3:0]), .cin(carry[0]), .gout(g31_0), .pout(p31_0), .cout(car_grp[2:0]));


   for(i = 0; i < 32; i = i + 1) begin
      assign sum[i] =  a[i] ^ b[i] ^ carry[i];
   end 

endmodule
