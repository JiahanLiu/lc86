// Initialized constants

`define IDTR_VAL 32'h02000000
`define IDT_NMI_INT_VECTOR 32'h02000010
`define IDT_GEN_PROT_VECTOR 32'h02000068
`define IDT_PAGE_FAULT_VECTOR 32'h02000070

`define INT_CONTROL_STORE_ADDR 8'h10

/*
ES = 000
CS = 001
SS = 010 // no checking for SS
DS = 011
FS = 100
GS  = 101
*/
     
`define CS_LIMIT_REGISTER 20'h04fff
`define DS_LIMIT_REGISTER 20'h011ff
`define SS_LIMIT_REGISTER 20'h04000
`define ES_LIMIT_REGISTER 20'h00419
//`define ES_LIMIT_REGISTER 20'h003ff
`define FS_LIMIT_REGISTER 20'h003ff
`define GS_LIMIT_REGISTER 20'h007ff

/*
Virtual Page    Physical Page   Valid   Present R/W PCD
20'h00000       20'h00000       1       1       0   0
20'h02000       20'h00002       1       1       1   0
20'h04000       20'h00005       1       1       1   0
20'h0b000       20'h00004       1       1       1   0
20'h0c000       20'h00007       1       1       1   0
20'h0a000       20'h00005       1       1       1   0
*/

//  TLB ENTRY        VPN        RPN        V     PRE   R/W   PCD
`define TLB_ENTRY_0 {20'h00000, 20'h00000, 1'b1, 1'b1, 1'b0, 1'b0}
`define TLB_ENTRY_1 {20'h02000, 20'h00002, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_2 {20'h04000, 20'h00005, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_3 {20'h0b000, 20'h00004, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_4 {20'h0c000, 20'h00007, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_5 {20'h0a000, 20'h00005, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_6 {20'h10000, 20'h10000, 1'b1, 1'b0, 1'b1, 1'b1}
`define TLB_ENTRY_7 {20'h02001, 20'h2FFFF, 1'b1, 1'b0, 1'b1, 1'b1}

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

module slr64 (out, in, cnt);
   input [63:0] in;
   input [5:0] cnt;

   output [63:0] out;

   wire [63:0] ind0, ind1, ind2, ind3, ind4;

   mux2$
     mux0[63:0] (ind0, in, {32'b0, {in[63:32]}}, cnt[5]),
     mux1[63:0] (ind1, ind0, {16'b0, {ind0[63:16]}}, cnt[4]),
     mux2[63:0] (ind2, ind1, {8'b0, {ind1[63:8]}}, cnt[3]),
     mux3[63:0] (ind3, ind2, {4'b0, {ind2[63:4]}}, cnt[2]),
     mux4[63:0] (ind4, ind3, {2'b0, {ind3[63:2]}}, cnt[1]),
     mux5[63:0] (out, ind4, {1'b0, {ind4[63:1]}}, cnt[0]);

endmodule // slr64

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

module sll64 (out, in, cnt);
   input [63:0] in;
   input [5:0] cnt;

   output [63:0] out;

   wire [63:0] ind0, ind1, ind2, ind3, ind4;

   mux2$
     mux0[63:0] (ind0, in, {in[31:0], 32'b0}, cnt[5]),
     mux1[63:0] (ind1, ind0, {ind0[47:0], 16'b0}, cnt[4]),
     mux2[63:0] (ind2, ind1, {ind1[55:0], 8'b0}, cnt[3]),
     mux3[63:0] (ind3, ind2, {ind2[59:0], 4'b0}, cnt[2]),
     mux4[63:0] (ind4, ind3, {ind3[61:0], 2'b0}, cnt[1]),
     mux5[63:0] (out, ind4, {ind4[62:0], 1'b0}, cnt[0]);

endmodule // sll64

module sll128 (out, in, cnt);
   input [127:0] in;
   input [6:0] cnt;

   output [127:0] out;

   wire [127:0] ind0, ind1, ind2, ind3, ind4, ind5;

   mux2$
     mux0[127:0] (ind0, in, {in[63:0], 64'b0}, cnt[6]),
     mux1[127:0] (ind1, ind0, {ind0[95:0], 32'b0}, cnt[5]),
     mux2[127:0] (ind2, ind1, {ind1[111:0], 16'b0}, cnt[4]),
     mux3[127:0] (ind3, ind2, {ind2[119:0], 8'b0}, cnt[3]),
     mux4[127:0] (ind4, ind3, {ind3[123:0], 4'b0}, cnt[2]),
     mux5[127:0] (ind5, ind4, {ind4[125:0], 2'b0}, cnt[1]),
     mux6[127:0] (out, ind5, {ind5[126:0], 1'b0}, cnt[0]);

endmodule // sll128

module reg128e (
   input CLK,
   input [127:0] Din,

   output [127:0] Q,
   output [127:0] QBAR,

   input CLR,
   input PRE,
   input en);

reg64e$ low(CLK, Din[63:0], Q[63:0], QBAR[63:0], CLR, PRE, en);
reg64e$ high(CLK, Din[127:64], Q[127:64], QBAR[127:64], CLR, PRE, en);

endmodule

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

module comp20 (out, out_bar, in0, in1);
   input [19:0] in0, in1;

   // outputs EQ or NEQ
   output out, out_bar;

   wire [19:0] xnor_out;
   wire and0_out, and1_out, and2_out, and3_out, and4_out, and5_out, and6_out;

   xnor2$ xnor0 [19:0] (xnor_out, in0, in1);
   and4$
      and0 (and0_out, xnor_out[3], xnor_out[2], xnor_out[1], xnor_out[0]),
      and1 (and1_out, xnor_out[7], xnor_out[6], xnor_out[5], xnor_out[4]),
      and2 (and2_out, xnor_out[11], xnor_out[10], xnor_out[9], xnor_out[8]),
      and3 (and3_out, xnor_out[15], xnor_out[14], xnor_out[13], xnor_out[12]),
      and4 (and4_out, xnor_out[19], xnor_out[18], xnor_out[17], xnor_out[16]);

   and3$
      and5 (and5_out, and0_out, and1_out, and2_out);
   and2$
      and6 (and6_out, and3_out, and4_out),
      and7 (out, and5_out, and6_out);

   nand2$ nand0 (out_bar, and5_out, and6_out);

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

module mux2_2 (Y, IN0, IN1, S0);
   output [1:0] Y;

   input [1:0] IN0, IN1;
   input S0;

   wire [7:0] in0, in1;
   wire [5:0] Y_NC;

   assign in0[1:0] = IN0;
   assign in1[1:0] = IN1;

   mux2_8$ mux0 ({Y_NC, Y}, in0, in1, S0);

endmodule

module mux2_3 (Y, IN0, IN1, S0);
   output [2:0] Y;

   input [2:0] IN0, IN1;
   input S0;

   wire [7:0] in0, in1;
   wire [4:0] Y_NC;

   assign in0[2:0] = IN0;
   assign in1[2:0] = IN1;

   mux2_8$ mux0 ({Y_NC, Y}, in0, in1, S0);

endmodule

module mux2_4 (Y, IN0, IN1, S0);
   output [3:0] Y;

   input [3:0] IN0, IN1;
   input S0;

   wire [7:0] in0, in1;
   wire [3:0] Y_NC;

   assign in0[3:0] = IN0;
   assign in1[3:0] = IN1;

   mux2_8$ mux0 ({Y_NC, Y}, in0, in1, S0);

endmodule

module mux2_32 (Y, IN0, IN1, S0);
   output [31:0] Y;

   input [31:0] IN0, IN1;
   input S0;

   mux2_16$
      muxhi (Y[31:16], IN0[31:16], IN1[31:16], S0),
      muxlo (Y[15:0], IN0[15:0], IN1[15:0], S0);

endmodule

module mux2_64 (Y, IN0, IN1, S0);
   output [63:0] Y;

   input [63:0] IN0, IN1;
   input S0;

   mux2_32
      muxhi (Y[63:32], IN0[63:32], IN1[63:32], S0),
      muxlo (Y[31:0], IN0[31:0], IN1[31:0], S0);

endmodule

module mux2_128 (Y, IN0, IN1, S0);
   output [127:0] Y;

   input [127:0] IN0, IN1;
   input S0;

   mux2_64
      muxhi (Y[127:64], IN0[127:64], IN1[127:64], S0),
      muxlo (Y[63:0], IN0[63:0], IN1[63:0], S0);

endmodule // mux2_128

module mux4_4 (Y, IN0, IN1, IN2, IN3, S0, S1);
   output [3:0] Y;

   input [3:0] IN0, IN1, IN2, IN3;
   input S0, S1;

   wire [7:0] in0, in1, in2, in3;
   wire [3:0] Y_NC;

   assign in0[3:0] = IN0;
   assign in1[3:0] = IN1;
   assign in2[3:0] = IN2;
   assign in3[3:0] = IN3;

   mux4_8$ mux0 ({Y_NC, Y}, in0, in1, in2, in3, S0, S1);

endmodule // mux4_4

module mux3_32 (Y, IN0, IN1, IN2, S0, S1);
   output [31:0] Y;

   input [31:0] IN0, IN1, IN2;
   input S0, S1;

   mux3_16$
      muxhi (Y[31:16], IN0[31:16], IN1[31:16], IN2[31:16], S0, S1),
      muxlo (Y[15:0], IN0[15:0], IN1[15:0], IN2[15:0], S0, S1);

endmodule // mux3_32

module mux4_32 (Y, IN0, IN1, IN2, IN3, S0, S1);
   output [31:0] Y;

   input [31:0] IN0, IN1, IN2, IN3;
   input S0, S1;

   mux4_16$
      muxhi (Y[31:16], IN0[31:16], IN1[31:16], IN2[31:16], IN3[31:16], S0, S1),
      muxlo (Y[15:0], IN0[15:0], IN1[15:0], IN2[15:0], IN3[15:0], S0, S1);

endmodule // mux4_32

module mux4_128 (Y, IN0, IN1, IN2, IN3, S0, S1);
   output [127:0] Y;

   input [127:0] IN0, IN1, IN2, IN3;
   input S0, S1;

   mux4_16$
      mux0 (Y[127:112], IN0[127:112], IN1[127:112], IN2[127:112], IN3[127:112], S0, S1),
      mux1 (Y[111:96], IN0[111:96], IN1[111:96], IN2[111:96], IN3[111:96], S0, S1),
      mux2 (Y[95:80], IN0[95:80], IN1[95:80], IN2[95:80], IN3[95:80], S0, S1),
      mux3 (Y[79:64], IN0[79:64], IN1[79:64], IN2[79:64], IN3[79:64], S0, S1),
      mux4 (Y[63:48], IN0[63:48], IN1[63:48], IN2[63:48], IN3[63:48], S0, S1),
      mux5 (Y[47:32], IN0[47:32], IN1[47:32], IN2[47:32], IN3[47:32], S0, S1),
      mux6 (Y[31:16], IN0[31:16], IN1[31:16], IN2[31:16], IN3[31:16], S0, S1),
      mux7 (Y[15:0], IN0[15:0], IN1[15:0], IN2[15:0], IN3[15:0], S0, S1);

endmodule // mux4_128

module mux8 (Y, IN0, IN1, IN2, IN3, IN4, IN5, IN6, IN7, S);
   output Y;

   input IN0, IN1, IN2, IN3, IN4, IN5, IN6, IN7;
   input [2:0] S;

   wire mux0_out, mux1_out;

   mux4$ mux0 (mux0_out, IN0, IN1, IN2, IN3, S[0], S[1]);
   mux4$ mux1 (mux1_out, IN4, IN5, IN6, IN7, S[0], S[1]);

   mux2$ mux2 (Y, mux0_out, mux1_out, S[2]);

endmodule

module mux8_4 (Y, IN0, IN1, IN2, IN3, IN4, IN5, IN6, IN7, S);
   output [3:0] Y;

   input [3:0] IN0, IN1, IN2, IN3, IN4, IN5, IN6, IN7;
   input [2:0] S;

   wire [3:0] mux0_out, mux1_out;

   mux4_4 mux0 (mux0_out, IN0, IN1, IN2, IN3, S[0], S[1]);
   mux4_4 mux1 (mux1_out, IN4, IN5, IN6, IN7, S[0], S[1]);

   mux2_4 mux2 (Y, mux0_out, mux1_out, S[2]);

endmodule

module mux8_32 (
   output [31:0] out,

   input [31:0] in0, in1, in2, in3,
   input [31:0] in4, in5, in6, in7,

   input [2:0] s
);

   wire [15:0] mux0_out, mux1_out, mux2_out, mux3_out;

   mux4_16$
      mux0 (mux0_out, in0[31:16], in1[31:16], in2[31:16], in3[31:16], s[0], s[1]),
      mux1 (mux1_out, in4[31:16], in5[31:16], in6[31:16], in7[31:16], s[0], s[1]),

      mux2 (mux2_out, in0[15:0], in1[15:0], in2[15:0], in3[15:0], s[0], s[1]),
      mux3 (mux3_out, in4[15:0], in5[15:0], in6[15:0], in7[15:0], s[0], s[1]);

   mux2_16$
      mux4 (out[31:16], mux0_out, mux1_out, s[2]),
      mux5 (out[15:0], mux2_out, mux3_out, s[2]);

endmodule

module mux8_64 (
   output [63:0] out,

   input [63:0] in0, in1, in2, in3,
   input [63:0] in4, in5, in6, in7,

   input [2:0] s
);

   mux8_32
      mux0 (out[63:32], in0[63:32], in1[63:32], in2[63:32], in3[63:32], in4[63:32], in5[63:32], in6[63:32], in7[63:32], s),
      mux1 (out[31:0], in0[31:0], in1[31:0], in2[31:0], in3[31:0], in4[31:0], in5[31:0], in6[31:0], in7[31:0], s);

endmodule

//module adder32 (out, cout, a, b, cin);
//   input [31:0] a, b;
//   input        cin;
//
//   output [31:0] out;
//   output        cout;
//
//   wire          co0, co1, co2, co3, co4, co5, co6, co7;
//
//   alu4$
//     add3_0 (a[3:0], b[3:0], 1'b0, 1'b1, 4'd9, co0, out[3:0]),
//     add7_4 (a[7:4], b[7:4], co0, 1'b1, 4'd9, co1, out[7:4]),
//     add11_8 (a[11:8], b[11:8], co1, 1'b1, 4'd9, co2, out[11:8]),
//     add15_12 (a[15:12], b[15:12], co2, 1'b1, 4'd9, co3, out[15:12]),
//     add19_16 (a[19:16], b[19:16], co3, 1'b1, 4'd9, co4, out[19:16]),
//     add23_20 (a[23:20], b[23:20], co4, 1'b1, 4'd9, co5, out[23:20]),
//     add27_24 (a[27:24], b[27:24], co5, 1'b1, 4'd9, co6, out[27:24]),
//     add31_28 (a[31:28], b[31:28], co6, 1'b1, 4'd9, cout, out[31:28]);
//
//endmodule // add32


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

module carry_lookahead_sat (sum, p, g, cout, v, a, b, cin);
    input cin;
    input [3:0] a, b;
    output [3:0] sum;
    output p, g, cout, v;

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

    // Calculate the overflow bit
    xor2$ xor1 (v, c3, cout);

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


// 16-bit carry look ahead saturating adder
module carry_lookahead16_sat (sum, p, g, cout, v, a, b, cin);
    input cin;
    input [15:0] a, b;
    output [15:0] sum;
    output p, g, cout, v;

    wire p0, p1, p2, p3, g0, g1, g2, g3, c1, c2, c3;
    wire g0_b, g1_b, g2_b, g3_b;
    wire w1, w2, w3, w4, w5, w6, w7, w8, w9, w10;
    wire w11, w12, w13, w14, w15, w16, w17, w18, w19;
    wire co1, co2, co3, co4;

    carry_lookahead f0 (sum[3:0], p0, g0, co1, a[3:0], b[3:0], cin);
    carry_lookahead f1 (sum[7:4], p1, g1, co2, a[7:4], b[7:4], c1);
    carry_lookahead f2 (sum[11:8], p2, g2, co3, a[11:8], b[11:8], c2);
    carry_lookahead_sat f3 (sum[15:12], p3, g3, co4, v, a[15:12], b[15:12], c3);

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

// 16-bit carry look ahead adder with AF flag calculation
module carry_lookahead16_AF (sum, p, g, cout, a, b, cin, AF);
    input cin, AF;
    input [15:0] a, b;
    output [15:0] sum;
    output p, g, cout;

    wire p0, p1, p2, p3, g0, g1, g2, g3, c1, c2, c3;
    wire g0_b, g1_b, g2_b, g3_b;
    wire w1, w2, w3, w4, w5, w6, w7, w8, w9, w10;
    wire w11, w12, w13, w14, w15, w16, w17, w18, w19;
    wire co1, co2, co3, co4;

    assign AF = co1;

    carry_lookahead f0 (sum[3:0], p0, g0, co1, a[3:0], b[3:0], cin);
    carry_lookahead f1 (sum[7:4], p1, g1, co2, a[7:4], b[7:4], c1);
    carry_lookahead f2 (sum[11:8], p2, g2, co3, a[11:8], b[11:8], c2);
    carry_lookahead f3 (sum[15:12], p3, g3, co4, a[15:12], b[15:12], c3);

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

    carry_lookahead16_AF f0 (sum[15:0], p0, g0, co1, a[15:0], b[15:0], cin, AF);
    carry_lookahead16_sat f1 (sum[31:16], p1, g1, co2, v, a[31:16], b[31:16], c1);

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

     
