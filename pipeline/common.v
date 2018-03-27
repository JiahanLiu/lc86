`define IDTR_VAL 32'h02000000

module sar32 (out, in, cnt);
   input [31:0] in;
   input [4:0] cnt;

   output [31:0] out;

   wire [31:0] ind0, ind1, ind2, ind3;

   mux2$ mux0[31:0] (ind0, in, {{16{in[31]}}, {in[31:16]}}, cnt[4]),
     mux1[31:0] (ind1, ind0, {{8{ind0[31]}}, {ind0[31:8]}}, cnt[3]),
     mux2[31:0] (ind2, ind1, {{4{ind1[31]}}, {ind1[31:4]}}, cnt[2]),
     mux3[31:0] (ind3, ind2, {{2{ind2[31]}}, {ind2[31:2]}}, cnt[1]),
     mux4[31:0] (out, ind3, {{1{ind3[31]}}, {ind3[31:1]}}, cnt[0]);

endmodule // sar32

module sal32 (out, in, cnt);
   input [31:0] in;
   input [4:0] cnt;

   output [31:0] out;

   wire [31:0] ind0, ind1, ind2, ind3;

   mux2$ mux0[31:0] (ind0, in, {in[15:0], 16'b0}, cnt[4]),
     mux1[31:0] (ind1, ind0, {ind0[23:0], 8'b0}, cnt[3]),
     mux2[31:0] (ind2, ind1, {ind1[27:0], 4'b0}, cnt[2]),
     mux3[31:0] (ind3, ind2, {ind2[29:0], 2'b0}, cnt[1]),
     mux4[31:0] (out, ind3, {ind3[30:0], 1'b0}, cnt[0]);

endmodule // sal32

module comp4 (out, out_bar, in0, in1);
   input [3:0] in0, in1;

   output out, out_bar;

   wire [3:0] xnor_out;

   xnor2$ xnor0 [3:0] (xnor_out, in0, in1);
   and4$ and0 (out, xnor_out[3], xnor_out[2], xnor_out[1], xnor_out[0]);
   nand4$ nand0 (out_bar, xnor_out[3], xnor_out[2], xnor_out[1], xnor_out[0]);

endmodule

module comp16 (out, out_bar, in0, in1);
   input [15:0] in0, in1;

   // outputs EQ or NEQ
   output out, out_bar;

   wire [15:0] xnor_out;
   wire and0_out, and1_out, and2_out, and3_out;

   xnor2$ xnor0 [15:0] (xnor_out, in0, in1);
   and4$
      and0 (and0_out, xnor_out[3], xnor_out[2], xnor_out[1], xnor_out[0]),
      and1 (and1_out, xnor_out[7], xnor_out[6], xnor_out[5], xnor_out[4]),
      and2 (and2_out, xnor_out[11], xnor_out[10], xnor_out[9], xnor_out[8]),
      and3 (and3_out, xnor_out[15], xnor_out[14], xnor_out[13], xnor_out[12]),
      and4 (out, and0_out, and1_out, and2_out, and3_out);
   
   nand4$ nand0 (out_bar, and0_out, and1_out, and2_out, and3_out);
endmodule

//module mag_comp8$(A, B, AGB, BGA);
module mag_comp32 (A, B, AGB, BGA, EQ);
   input [31:0] A, B;

   output AGB, BGA, EQ;

   wire AGB_lolo, AGB_lohi, AGB_hilo, AGB_hihi;
   wire BGA_lolo_, BGA_lohi, BGA_hilo, BGA_hihi;

   wire hihi_eq, lohi_eq, hi_eq, lo_eq;
   wire agb0, agb1, agb2, bga0, bga1, bga2;

   wire eq[7:0];

   mag_comp8$
      mag_comp_lolo (A[7:0], B[7:0], AGB_lolo, BGA_lolo),
      mag_comp_lohi (A[15:8], B[15:8], AGB_lohi, BGA_lohi),
      mag_comp_hilo (A[23:16], B[23:16], AGB_hilo, BGA_hilo),
      mag_comp_hihi (A[31:24], B[31:24], AGB_hihi, BGA_hihi);

   // assign AGB = AGB_hihi or (hihi_eq and AGB_hilo) or (hihi_eq and hilo_eq and AGB_lohi) or (hihi_eq and hilo_eq and lohi_eq and AGB_lolo)

   generate
      genvar i;
      for (i = 0; i < 32; i = i + 4) begin: gen_comp4
         comp4 u_comp4 (eq[i/4], , A[i+3:i], B[i+3:i]);
      end
   endgenerate

   and2$
      and0 (hihi_eq, eq[7], eq[6]),
      and1 (lohi_eq, eq[3], eq[2]);

   and4$
      and4_0 (hi_eq, eq[7], eq[6], eq[5], eq[4]),
      and4_1 (lo_eq, eq[3], eq[2], eq[1], eq[0]);

   and2$
      and3 (agb0, hihi_eq, AGB_hilo),
      and4 (agb1, hi_eq, AGB_lohi),

      and6 (bga0, hihi_eq, BGA_hilo),
      and7 (bga1, hi_eq, BGA_lohi);

   and3$
      and3_0 (agb2, hi_eq, lohi_eq, AGB_lolo),
      and3_1 (bga2, hi_eq, lohi_eq, BGA_lolo);

   or4$
      or0 (AGB, AGB_hihi, agb0, agb1, agb2),
      or1 (BGA, BGA_hihi, bga0, bga1, bga2);

   and2$
      and_eq (EQ, hi_eq, lo_eq);

endmodule

module adder32 (out, cout, a, b, cin);
   input [31:0] a, b;
   input        cin;

   output [31:0] out;
   output        cout;

   wire          co0, co1, co2, co3, co4, co5, co6, co7;

   alu4$
     add3_0 (a[3:0], b[3:0], 1'b0, 1'b1, 4'd9, co0, out[3:0]),
     add7_4 (a[7:4], b[7:4], co0, 1'b1, 4'd9, co1, out[7:4]),
     add11_8 (a[11:8], b[11:8], co1, 1'b1, 4'd9, co2, out[11:8]),
     add15_12 (a[15:12], b[15:12], co2, 1'b1, 4'd9, co3, out[15:12]),
     add19_16 (a[19:16], b[19:16], co3, 1'b1, 4'd9, co4, out[19:16]),
     add23_20 (a[23:20], b[23:20], co4, 1'b1, 4'd9, co5, out[23:20]),
     add27_24 (a[27:24], b[27:24], co5, 1'b1, 4'd9, co6, out[27:24]),
     add31_28 (a[31:28], b[31:28], co6, 1'b1, 4'd9, cout, out[31:28]);

endmodule // add32

module alu32 (
   input [31:0] A, B,
   input [2:0] sel,

   output [31:0] OUT
);
endmodule

module alu64 (
   input [63:0] A, B,
   input [2:0] sel,

   output [63:0] OUT
);
endmodule

module shf32 (
   input [31:0] A,
   input [4:0] AMT,
   input DIR,

   output [31:0] OUT
);
endmodule


// 4-bit carry look ahead adder
// Worst case delay -> 12 nand gate for SUM

module carry_lookahead (sum, p, g, cout, a, b, cin);
    input cin;
    input [3:0] a, b;
    output [3:0] sum;
    output p, g, cout;

    wire p0, p1, p2, p3, g0, g1, g2, g3, c1, c2, c3;
    wire g0_b, g1_b, g2_b, g3_b;
    wire w1, w2, w3, w4, w5, w6, w7, w8, w9, w10;
    wire w11, w12, w13, w14, w15, w16, w17, w18, w19;

    full_adder f0 (sum[0], p0, g0, a[0], b[0], cin);
    full_adder f1 (sum[1], p1, g1, a[1], b[1], c1);
    full_adder f2 (sum[2], p2, g2, a[2], b[2], c2);
    full_adder f3 (sum[3], p3, g3, a[3], b[3], c3);

    inv1$ inv1 (g0_b, g0),
          inv2 (g1_b, g1),
          inv3 (g2_b, g2),
          inv4 (g3_b, g3);

    // Calculate the carry bits
    nand2$ nand1 (w1, p0, cin),
           nand2 (c1, w1, g0_b),

           nand3 (w2, c1, p1),
           nand4 (c2, w2, g1_b),

           nand5 (w3, c2, p2),
           nand6 (c3, w3, g2_b),

           nand7 (w4, c3, p3),
           nand8 (cout, w4, g3_b);

    // Calculate the PG bit
    nand2$ nand9 (w5, p0, p1),
          inv5 (w6, w5, w5),

          nand10 (w7, p2, p3),
          inv6 (w8, w7, w7),

          nand11 (w9, w6, w8),
          nand12 (p, w9, w9);

    // Calculate the GG bit
    nand2$ nand13 (w10, g2, p3),
          nand14 (w11, w10, g3_b),
          inv7 (w12, w11, w11),

          nand15 (w13, p1, p2),
          inv8 (w14, w13, w13),
          nand16 (w15, w14, g0),

          nand17 (w16, g1, p2),

          nand18 (w17, w15, w16),
          nand19 (w18, w17, p3),

          nand20 (g, w18, w12);

endmodule


// 32-bit carry look ahead adder
module carry_lookahead32 (sum, p, g, cout, v, a, b, cin, AF);
    input cin, AF;
    input [31:0] a, b;
    output [31:0] sum;
    output p, g, cout, v;

    wire p0, p1, g0, g1, c1;
    wire g0_b, g1_b;
    wire w1, w2, w5, w10;
    wire co1, co2;

    //carry_lookahead16_AF f0 (sum[15:0], p0, g0, co1, a[15:0], b[15:0], cin, AF);
    //carry_lookahead16_sat f1 (sum[31:16], p1, g1, co2, v, a[31:16], b[31:16], c1);

    inv1$ inv1 (g0_b, g0),
          inv2 (g1_b, g1);

    // Calculate the carry bits
    nand2$ nand1 (w1, p0, cin),
           nand2 (c1, w1, g0_b),

           nand3 (w2, c1, p1),
           nand4 (cout, w2, g1_b);

    // Calculate the PG bit
    nand2$ nand9 (w5, p0, p1),
          inv5 (p, w5, w5);

    // Calculate the GG bit
    nand2$ nand13 (w10, g0, p1),
          nand14 (g, w10, g1_b);

endmodule


// Full_adder with propagate and generate bits
// Gate delay: p=3, g=2, s=6
module full_adder (sum, p, g, a, b, cin);
    input a, b, cin;
    output sum, p, g;

    wire w1;

    xor2$ xor1 (p, a, b),
          xor2 (sum, p, cin);

    nand2$ nand1 (w1, a, b),
           nand2 (g, w1, w1);

endmodule          
