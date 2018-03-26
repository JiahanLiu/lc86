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

module comp16 (out, out_bar, in0, in1);
   input [15:0] in0, in1;

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
