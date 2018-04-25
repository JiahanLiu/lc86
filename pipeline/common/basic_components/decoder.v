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
