// Sign extend for 83 and 6A
// Assuming that we do not have invalid opcodes, there is no 0F 83 and 0F 6A,
// so we dont care about opcode size

module imm_selector (
    input [127:0] IR,
    input [15:0] opcode,
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
wire out1r;
wire out1c, out2c, out3c, out4c, out5c, out6c;
wire sign_extend, imm_sign;
wire [7:0] imm_sign8;
wire op7_b, op6_b, op5_b, op4_b, op3_b, op2_b, op1_b, op0_b;

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

inv1$ inv1 (op7_b, opcode[7]);
inv1$ inv2 (op6_b, opcode[6]);
inv1$ inv3 (op5_b, opcode[5]);
inv1$ inv4 (op4_b, opcode[4]);
inv1$ inv5 (op3_b, opcode[3]);
inv1$ inv6 (op2_b, opcode[2]);
inv1$ inv7 (op1_b, opcode[1]);
inv1$ inv8 (op0_b, opcode[0]);

// Check if opcode is 6A or 83
// t = (!b7 &b6 &b5 &!b4 &b3 &!b2 &b1 &!b0) | (b7 &!b6 &!b5 &!b4 &!b3 &!b2 &b1 &b0);
and4$ and1c (out1c, op7_b, opcode[6], opcode[5], op4_b);
and4$ and2c (out2c, opcode[3], op2_b, opcode[1], op0_b);
and2$ and3c (out3c, out1c, out2c);

and4$ and4c (out4c, opcode[7], op6_b, op5_b, op4_b);
and4$ and5c (out5c, op3_b, op2_b, opcode[1], opcode[0]);
and2$ and6c (out6c, out4c, out5c);

or2$ or1c (sign_extend, out3c, out6c);

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
// b4 = (s1);
// b3 = (s1);
// b2 = (s0) | (s1);
// b1 = ();

assign imm_sign = out13m[7];
assign imm_sign8 = {imm_sign, imm_sign, imm_sign, imm_sign, imm_sign, imm_sign, imm_sign, imm_sign};
or2$ or1 (out1r, imm_size[1], imm_size[0]);

assign imm[7:0] = out13m;
mux4_8$ mux1f (imm[15:8], 8'b0, out14m, imm_sign8, imm_sign8, out1r, sign_extend);
mux4_8$ mux2f (imm[23:16], 8'b0, out15m, imm_sign8, imm_sign8, imm_size[1], sign_extend);
mux4_8$ mux3f (imm[31:24], 8'b0, out16m, imm_sign8, imm_sign8, imm_size[1], sign_extend);

endmodule
