module disp_selector (
    input [127:0] IR,
    input [2:0] disp_sel,
    input disp_size,
    output [31:0] disp
);

wire [7:0] byte3, byte4, byte5, byte6, byte7;
wire [7:0] byte8, byte9, byte10, byte11;
wire [7:0] out1m, out2m, out3m, out4m, out5m, out6m;
wire [7:0] out7m, out8m, out9m, out10m, out11m, out12m;
wire disp_sel0, disp_sel1, disp_sel2;
wire disp_size_bf, disp_size_b;
wire disp_sign;
wire [7:0] disp_sign8;

assign byte3 = IR[111:104];
assign byte4 = IR[103:96];
assign byte5 = IR[95:88];
assign byte6 = IR[87:80];
assign byte7 = IR[79:72];
assign byte8 = IR[71:64];
assign byte9 = IR[63:56];
assign byte10 = IR[55:48];
assign byte11 = IR[47:40];

bufferH64$ buf1 (disp_sel0, disp_sel[0]);
bufferH16$ buf2 (disp_sel1, disp_sel[1]);
bufferH16$ buf3 (disp_sel2, disp_sel[2]);

mux4_8$ mux1_l1 (out1m, byte5, byte6, byte7, byte8, disp_sel0, disp_sel1);
mux4_8$ mux1_l2 (out2m, byte6, byte7, byte8, byte9, disp_sel0, disp_sel1);
mux4_8$ mux1_l3 (out3m, byte7, byte8, byte9, byte10, disp_sel0, disp_sel1);
mux4_8$ mux1_l4 (out4m, byte8, byte9, byte10, byte11, disp_sel0, disp_sel1);

mux2_8$ mux1_l5 (out5m, byte3, byte4, disp_sel0);
mux2_8$ mux1_l6 (out6m, byte4, byte5, disp_sel0);
mux2_8$ mux1_l7 (out7m, byte5, byte6, disp_sel0);
mux2_8$ mux1_l8 (out8m, byte6, byte7, disp_sel0);

mux2_8$ mux2_l1 (out9m, out5m, out1m, disp_sel2);
mux2_8$ mux2_l2 (out10m, out6m, out2m, disp_sel2);
mux2_8$ mux2_l3 (out11m, out7m, out3m, disp_sel2);
mux2_8$ mux2_l4 (out12m, out8m, out4m, disp_sel2);

// Logic for masking
// b4 = (!s);
// b3 = (!s);
// b2 = (!s);
// b1 = ();
inv1$ inv1 (disp_size_bf, disp_size);
bufferH64$ buf4 (disp_size_b, disp_size_bf);

assign disp[7:0] = out9m;
bufferH64$ buf5 (disp_sign, out9m[7]);
assign disp_sign8 = {disp_sign, disp_sign, disp_sign, disp_sign, disp_sign, disp_sign, disp_sign, disp_sign};

// Sign extended disp
mux2_8$ muxc1 (disp[15:8], disp_sign8, out10m, disp_size_b);
mux2_8$ muxc2 (disp[23:16], disp_sign8, out11m, disp_size_b);
mux2_8$ muxc3 (disp[31:24], disp_sign8, out12m, disp_size_b);


endmodule
