module decoder5to32 (
	output [31:0] out,
	input [4:0] in
	);
	
	wire [4:0] in_not;

	inv1$ u_in_not0(in_not[0], in[0]);
	inv1$ u_in_not1(in_not[1], in[1]);
	inv1$ u_in_not2(in_not[2], in[2]);
	inv1$ u_in_not3(in_not[3], in[3]);
	inv1$ u_in_not4(in_not[4], in[4]);

	and1_5way u_out0(out[0], in_not[4], in_not[3], in_not[2], in_not[1], in_not[0]);
	and1_5way u_out1(out[1], in_not[4], in_not[3], in_not[2], in_not[1], in[0]);
	and1_5way u_out2(out[2], in_not[4], in_not[3], in_not[2], in[1], in_not[0]);
	and1_5way u_out3(out[3], in_not[4], in_not[3], in_not[2], in[1], in[0]);

	and1_5way u_out4(out[4], in_not[4], in_not[3], in[2], in_not[1], in_not[0]);
	and1_5way u_out5(out[5], in_not[4], in_not[3], in[2], in_not[1], in[0]);
	and1_5way u_out6(out[6], in_not[4], in_not[3], in[2], in[1], in_not[0]);
	and1_5way u_out7(out[7], in_not[4], in_not[3], in[2], in[1], in[0]);

	and1_5way u_out8(out[8], in_not[4], in[3], in_not[2], in_not[1], in_not[0]);
	and1_5way u_out9(out[9], in_not[4], in[3], in_not[2], in_not[1], in[0]);
	and1_5way u_out10(out[10], in_not[4], in[3], in_not[2], in[1], in_not[0]);
	and1_5way u_out11(out[11], in_not[4], in[3], in_not[2], in[1], in[0]);

	and1_5way u_out12(out[12], in_not[4], in[3], in[2], in_not[1], in_not[0]);
	and1_5way u_out13(out[13], in_not[4], in[3], in[2], in_not[1], in[0]);
	and1_5way u_out14(out[14], in_not[4], in[3], in[2], in[1], in_not[0]);
	and1_5way u_out15(out[15], in_not[4], in[3], in[2], in[1], in[0]);

	//half 16+

	and1_5way u_out16(out[16], in[4], in_not[3], in_not[2], in_not[1], in_not[0]);
	and1_5way u_out17(out[17], in[4], in_not[3], in_not[2], in_not[1], in[0]);
	and1_5way u_out18(out[18], in[4], in_not[3], in_not[2], in[1], in_not[0]);
	and1_5way u_out19(out[19], in[4], in_not[3], in_not[2], in[1], in[0]);

	and1_5way u_out20(out[20], in[4], in_not[3], in[2], in_not[1], in_not[0]);
	and1_5way u_out21(out[21], in[4], in_not[3], in[2], in_not[1], in[0]);
	and1_5way u_out22(out[22], in[4], in_not[3], in[2], in[1], in_not[0]);
	and1_5way u_out23(out[23], in[4], in_not[3], in[2], in[1], in[0]);

	and1_5way u_out24(out[24], in[4], in[3], in_not[2], in_not[1], in_not[0]);
	and1_5way u_out25(out[25], in[4], in[3], in_not[2], in_not[1], in[0]);
	and1_5way u_out26(out[26], in[4], in[3], in_not[2], in[1], in_not[0]);
	and1_5way u_out27(out[27], in[4], in[3], in_not[2], in[1], in[0]);

	and1_5way u_out28(out[28], in[4], in[3], in[2], in_not[1], in_not[0]);
	and1_5way u_out29(out[29], in[4], in[3], in[2], in_not[1], in[0]);
	and1_5way u_out30(out[30], in[4], in[3], in[2], in[1], in_not[0]);
	and1_5way u_out31(out[31], in[4], in[3], in[2], in[1], in[0]);

endmodule // decoder5to32

module decoder5to32_w_en (
	output [31:0] out,
	input [4:0] in,
    input en
	);
	
	wire [4:0] in_not;

	inv1$ u_in_not0(in_not[0], in[0]);
	inv1$ u_in_not1(in_not[1], in[1]);
	inv1$ u_in_not2(in_not[2], in[2]);
	inv1$ u_in_not3(in_not[3], in[3]);
	inv1$ u_in_not4(in_not[4], in[4]);

	and1_6way u_out0(out[0], in_not[4], in_not[3], in_not[2], in_not[1], in_not[0], en);
	and1_6way u_out1(out[1], in_not[4], in_not[3], in_not[2], in_not[1], in[0], en);
	and1_6way u_out2(out[2], in_not[4], in_not[3], in_not[2], in[1], in_not[0], en);
	and1_6way u_out3(out[3], in_not[4], in_not[3], in_not[2], in[1], in[0], en);

	and1_6way u_out4(out[4], in_not[4], in_not[3], in[2], in_not[1], in_not[0], en);
	and1_6way u_out5(out[5], in_not[4], in_not[3], in[2], in_not[1], in[0], en);
	and1_6way u_out6(out[6], in_not[4], in_not[3], in[2], in[1], in_not[0], en);
	and1_6way u_out7(out[7], in_not[4], in_not[3], in[2], in[1], in[0], en);

	and1_6way u_out8(out[8], in_not[4], in[3], in_not[2], in_not[1], in_not[0], en);
	and1_6way u_out9(out[9], in_not[4], in[3], in_not[2], in_not[1], in[0], en);
	and1_6way u_out10(out[10], in_not[4], in[3], in_not[2], in[1], in_not[0], en);
	and1_6way u_out11(out[11], in_not[4], in[3], in_not[2], in[1], in[0], en);

	and1_6way u_out12(out[12], in_not[4], in[3], in[2], in_not[1], in_not[0], en);
	and1_6way u_out13(out[13], in_not[4], in[3], in[2], in_not[1], in[0], en);
	and1_6way u_out14(out[14], in_not[4], in[3], in[2], in[1], in_not[0], en);
	and1_6way u_out15(out[15], in_not[4], in[3], in[2], in[1], in[0], en);

	//half 16+

	and1_6way u_out16(out[16], in[4], in_not[3], in_not[2], in_not[1], in_not[0], en);
	and1_6way u_out17(out[17], in[4], in_not[3], in_not[2], in_not[1], in[0], en);
	and1_6way u_out18(out[18], in[4], in_not[3], in_not[2], in[1], in_not[0], en);
	and1_6way u_out19(out[19], in[4], in_not[3], in_not[2], in[1], in[0], en);

	and1_6way u_out20(out[20], in[4], in_not[3], in[2], in_not[1], in_not[0], en);
	and1_6way u_out21(out[21], in[4], in_not[3], in[2], in_not[1], in[0], en);
	and1_6way u_out22(out[22], in[4], in_not[3], in[2], in[1], in_not[0], en);
	and1_6way u_out23(out[23], in[4], in_not[3], in[2], in[1], in[0], en);

	and1_6way u_out24(out[24], in[4], in[3], in_not[2], in_not[1], in_not[0], en);
	and1_6way u_out25(out[25], in[4], in[3], in_not[2], in_not[1], in[0], en);
	and1_6way u_out26(out[26], in[4], in[3], in_not[2], in[1], in_not[0], en);
	and1_6way u_out27(out[27], in[4], in[3], in_not[2], in[1], in[0], en);

	and1_6way u_out28(out[28], in[4], in[3], in[2], in_not[1], in_not[0], en);
	and1_6way u_out29(out[29], in[4], in[3], in[2], in_not[1], in[0], en);
	and1_6way u_out30(out[30], in[4], in[3], in[2], in[1], in_not[0], en);
	and1_6way u_out31(out[31], in[4], in[3], in[2], in[1], in[0], en);

endmodule // decoder5to32



module decoder10to1024 (
    output [1023:0] out,
    input [9:0] in
);

wire [31:0] en;
decoder5to32 u_decoder_init (en[31:0], in[9:5]);

decoder5to32_w_en u_decoder0 (out[31:0], in[4:0], en[0]);
decoder5to32_w_en u_decoder1 (out[63:32], in[4:0], en[1]);
decoder5to32_w_en u_decoder2 (out[95:64], in[4:0], en[2]);
decoder5to32_w_en u_decoder3 (out[127:96], in[4:0], en[3]);
decoder5to32_w_en u_decoder4 (out[159:128], in[4:0], en[4]);
decoder5to32_w_en u_decoder5 (out[191:160], in[4:0], en[5]);
decoder5to32_w_en u_decoder6 (out[223:192], in[4:0], en[6]);
decoder5to32_w_en u_decoder7 (out[255:224], in[4:0], en[7]);
decoder5to32_w_en u_decoder8 (out[287:256], in[4:0], en[8]);
decoder5to32_w_en u_decoder9 (out[319:288], in[4:0], en[9]);
decoder5to32_w_en u_decoder10 (out[351:320], in[4:0], en[10]);
decoder5to32_w_en u_decoder11 (out[383:352], in[4:0], en[11]);
decoder5to32_w_en u_decoder12 (out[415:384], in[4:0], en[12]);
decoder5to32_w_en u_decoder13 (out[447:416], in[4:0], en[13]);
decoder5to32_w_en u_decoder14 (out[479:448], in[4:0], en[14]);
decoder5to32_w_en u_decoder15 (out[511:480], in[4:0], en[15]);
decoder5to32_w_en u_decoder16 (out[543:512], in[4:0], en[16]);
decoder5to32_w_en u_decoder17 (out[575:544], in[4:0], en[17]);
decoder5to32_w_en u_decoder18 (out[607:576], in[4:0], en[18]);
decoder5to32_w_en u_decoder19 (out[639:608], in[4:0], en[19]);
decoder5to32_w_en u_decoder20 (out[671:640], in[4:0], en[20]);
decoder5to32_w_en u_decoder21 (out[703:672], in[4:0], en[21]);
decoder5to32_w_en u_decoder22 (out[735:704], in[4:0], en[22]);
decoder5to32_w_en u_decoder23 (out[767:736], in[4:0], en[23]);
decoder5to32_w_en u_decoder24 (out[799:768], in[4:0], en[24]);
decoder5to32_w_en u_decoder25 (out[831:800], in[4:0], en[25]);
decoder5to32_w_en u_decoder26 (out[863:832], in[4:0], en[26]);
decoder5to32_w_en u_decoder27 (out[895:864], in[4:0], en[27]);
decoder5to32_w_en u_decoder28 (out[927:896], in[4:0], en[28]);
decoder5to32_w_en u_decoder29 (out[959:928], in[4:0], en[29]);
decoder5to32_w_en u_decoder30 (out[991:960], in[4:0], en[30]);
decoder5to32_w_en u_decoder31 (out[1023:992], in[4:0], en[31]);

endmodule
