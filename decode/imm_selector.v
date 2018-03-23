module imm_selector (
    input [127:0] IR,
    input [3:0] imm_sel,
    input [1:0] imm_size,
    output [31:0] imm
);

wire [7:0] byte2, byte3, byte4, byte5, byte6, byte7;
wire [7:0] byte8, byte9, byte10, byte11, byte12;
wire [7:0] byte13, byte14, byte15;
wire [7:0] out1m, out2m, out3m, out4m, out5m, out6m;
wire [7:0] out7m, out8m, out9m, out10m, out11m, out12m;
wire [7:0] out13m, out14m, out15m, out16m;
wire imm_sel0, imm_sel1, imm_sel2, imm_sel3;
wire imm_size0_b, imm_size1_b;
wire out1r, out2a, out8a, out2r;
wire out1r_buf, out2r_buf, out1a_buf;

assign byte2 = IR[119:112];
assign byte3 = IR[111:104];
assign byte4 = IR[103:96];
assign byte5 = IR[95:88];
assign byte6 = IR[87:80];
assign byte7 = IR[79:72];
assign byte8 = IR[71:64];
assign byte9 = IR[63:56];
assign byte10 = IR[55:48];
assign byte11 = IR[47:40];
assign byte12 = IR[39:32];
assign byte13 = IR[31:24];
assign byte14 = IR[23:16];
assign byte15 = IR[15:8];

bufferH256$ buf4 (imm_sel0, imm_sel[0]);
bufferH256$ buf5 (imm_sel1, imm_sel[1]);
bufferH64$ buf6 (imm_sel2, imm_sel[2]);
bufferH64$ buf7 (imm_sel3, imm_sel[3]);

mux4_8$ mux1_l1 (out1m, , byte2, byte3, byte4, imm_sel0, imm_sel1);
mux4_8$ mux1_l2 (out2m, , byte3, byte4, byte5, imm_sel0, imm_sel1);
mux4_8$ mux1_l3 (out3m, , byte4, byte5, byte6, imm_sel0, imm_sel1);
mux4_8$ mux1_l4 (out4m, , byte5, byte6, byte7, imm_sel0, imm_sel1);

mux4_8$ mux1_l5 (out5m, byte5, byte6, byte7, byte8, imm_sel0, imm_sel1);
mux4_8$ mux1_l6 (out6m, byte6, byte7, byte8, byte9, imm_sel0, imm_sel1);
mux4_8$ mux1_l7 (out7m, byte7, byte8, byte9, byte10, imm_sel0, imm_sel1);
mux4_8$ mux1_l8 (out8m, byte8, byte9, byte10, byte11, imm_sel0, imm_sel1);

mux4_8$ mux1_l9 (out9m, byte9, byte10, byte11, byte12, imm_sel0, imm_sel1);
mux4_8$ mux1_l10 (out10m, byte10, byte11, byte12, byte13, imm_sel0, imm_sel1);
mux4_8$ mux1_l11 (out11m, byte11, byte12, byte13, byte14, imm_sel0, imm_sel1);
mux4_8$ mux1_l12 (out12m, byte12, byte13, byte14, byte15, imm_sel0, imm_sel1);

mux4_8$ mux2_l1 (out13m, out1m, out5m, out9m, , imm_sel2, imm_sel3);
mux4_8$ mux2_l2 (out14m, out2m, out6m, out10m, , imm_sel2, imm_sel3);
mux4_8$ mux2_l3 (out15m, out3m, out7m, out11m, , imm_sel2, imm_sel3);
mux4_8$ mux2_l4 (out16m, out4m, out8m, out12m, , imm_sel2, imm_sel3);

// Logic for masking the output
// b4 = (s1 &!s0);
// b3 = (s1 &!s0);
// b2 = (!s1 &s0) | (s1 &!s0);
// b1 = (!s1 &s0) | (!s0);
inv1$ inv1 (imm_size0_b, imm_size[0]);
inv1$ inv2 (imm_size1_b, imm_size[1]);

and2$ and1 (out1a, imm_size[1], imm_size0_b);
and2$ and2 (out2a, imm_size1_b, imm_size[0]);

and2$ and8 (out8a, imm_size[1], imm_size0_b);
or2$ or1 (out1r, out2a, out8a);
or2$ or2 (out2r, out2a, imm_size0_b);

bufferH16$ buf1 (out1a_buf, out1a);
bufferH16$ buf2 (out1r_buf, out1r);
bufferH16$ buf3 (out2r_buf, out2r);

and2$ and3[7:0] (imm[7:0], out2r_buf, out13m);
and2$ and4[7:0] (imm[15:8], out1r_buf, out14m);
and2$ and5[7:0] (imm[23:16], out1a_buf, out15m);
and2$ and6[7:0] (imm[31:24], out1a_buf, out16m);

endmodule
