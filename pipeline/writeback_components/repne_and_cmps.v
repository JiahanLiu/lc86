//-------------------------------------------------------------------------------------
//
// 					 		    CMPS_POINTER_LOGIC
//
//-------------------------------------------------------------------------------------
// Functionality: increments pointers for cmps
//
// Combinational Delay: 
//
module CMPS_POINTER_LOGIC (
	output cmps_updated_pointer,
	input WB_CMPS_POINTER,
	input [1:0] de_datasize_all,
	input OF
);

wire [31:0] positive_inc, negative_inc, final_inc; 

mux32_3way u_pos_inc(positive_inc, 32'h0001, 32'h0002, 32'h0004, de_datasize_all); 
mux32_3way u_neg_inc(negative_inc, 32'hfff, 32'hfffe, 32'hfffc, de_datasize_all); 

mux32_2way u_final_inc(final_inc, positive_inc, negative_inc, OF);

adder32 u_adder32(cmps_updated_pointer, ,WB_CMPS_POINTER, final_inc);

endmodule

//-------------------------------------------------------------------------------------
//
// 					 		    REPNE_COUNT_LOGIC
//
//-------------------------------------------------------------------------------------
// Functionality: decrement count for repne
//
// Combinational Delay: 
//
module repne_and_cmps (
	output [31:0] internal_count,
	output ex_repne_termination_all,
	input [31:0] WB_COUNT,
	input cs_is_first_of_repne_wb,
	input cs_is_cmps_second_uop_all,
	input ZF,
);

	wire [31:0] internal_internal_count, count_minus_one, chosen_count;

	mux32_2way u_pick_count(chosen_count, internal_count, WB_COUNT, cs_is_first_of_repne_wb);
	adder32 u_adder32(count_minus_one, ,chosen_count, 32'hffff);
	reg32e$ count_register (CLK, count_minus_one, internal_internal_count, , 1'b1, 1'b1, cs_is_cmps_second_uop_all);
	assign internal_count = internal_internal_count;

	wire boolean; 

	equal_to_zero u_equal_to_zero(boolean, count_minus_one);
	and2$(ex_repne_termination_all, ZF, boolean); 

endmodule
