// Bytes 1-16
module offset_selector (
    input [127:0] IR,
    input [2:0] off_sel,
    input [1:0] offset_size,
    input ovr,
    output [47:0] offset
);

wire [7:0] byte2, byte3, byte4, byte5, byte6, byte7;
wire [7:0] byte8, byte9, byte10, byte11;
wire [7:0] out1m, out2m, out3m, out4m, out5m, out6m;
wire [7:0] out7m, out8m, out9m, out10m, out11m, out12m;
wire off_sel0, off_sel1, off_sel2, offset_size1;
wire out1r, out4a, out1r_buf, out4a_buf;

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

bufferH64$ buf0 (off_sel0, off_sel[0]);
bufferH64$ buf1 (off_sel1, off_sel[1]);
bufferH64$ buf2 (off_sel2, off_sel[2]);
bufferH64$ buf3 (offset_size1, offset_size[1]);

mux4_8$ mux1_l1 (.Y(out1m), .IN0(byte5) ,.IN1(byte2) ,.IN2(byte3) ,.IN3(byte4) ,.S0(off_sel0) ,.S1(off_sel1));
mux4_8$ mux2_l1 (out2m, byte6, byte3, byte4, byte5, off_sel0 ,off_sel1);
mux4_8$ mux3_l1 (out3m, byte7, byte4, byte5, byte6, off_sel0 ,off_sel1);
mux4_8$ mux4_l1 (out4m, byte8, byte5, byte6, byte7, off_sel0 ,off_sel1);
mux4_8$ mux5_l1 (out5m, byte9, byte6, byte7, byte8, off_sel0 ,off_sel1);
mux4_8$ mux6_l1 (out6m, byte10, byte7, byte8, byte9, off_sel0 ,off_sel1);

mux2_8$ mux1_l2 (out7m, byte6, out1m, off_sel2);
mux2_8$ mux2_l2 (out8m, byte7, out2m, off_sel2);
mux2_8$ mux3_l2 (out9m, byte8, out3m, off_sel2);
mux2_8$ mux4_l2 (out10m, byte9, out4m, off_sel2);
mux2_8$ mux5_l2 (out11m, byte10, out5m, off_sel2);
mux2_8$ mux6_l2 (out12m, byte11, out6m, off_sel2);

// Mask the output - {out7m, out8m, out9m, out10m, out11m, out12m}
// b6 = (s1&s0);
// b5 = (s1&s0);
// b4 = (s1);
// b3 = (s1);
// b2 = (s0) | (s1);
// b1 = ();
assign offset[7:0] = out7m;

or2$ or1 (out1r, offset_size[0], offset_size1);
bufferH16$ buf4 (out1r_buf, out1r);
and2$ and1[7:0] (offset[15:8], out1r_buf, out8m);

//and2$ and2[7:0] (offset[23:16], offset_size1, out9m);
//and2$ and3[7:0] (offset[31:24], offset_size1, out10m);

// if 32 - out9m, else if opcode==EA and operand_override and 32-00, else 00
// if 32 - out9m, else if opcode==EA and operand_override and 32-00, else 00
mux4_8$ mux1 (offset[23:16], 8'b0, out9m, 8'b0, 8'b0, offset_size1, ovr);
mux4_8$ mux2 (offset[31:24], 8'b0, out10m, 8'b0, 8'b0, offset_size1, ovr);

and2$ and4 (out4a, offset_size1, offset_size[0]);
bufferH16$ buf5 (out4a_buf, out4a);
//and2$ and5[7:0] (offset[39:32], out4a_buf, out11m);
//and2$ and6[7:0] (offset[47:40], out4a_buf, out12m);

// if 48, out11m, else if opcode==EA and operand_override and !48- out9m, else 00
// if 48, out12m, else if opcode==EA and operand_override and !48- out10m, else 00
mux4_8$ mux3 (offset[39:32], 8'b0, out11m, out9m, out11m, out4a_buf, ovr);
mux4_8$ mux4 (offset[47:40], 8'b0, out12m, out10m, out12m, out4a_buf, ovr);

endmodule
