//-------------------------------------------------------------------------------------
//
// 					 			Make Control Store Line
//
//-------------------------------------------------------------------------------------
// Functionality: Generate the control store from individual wires
//
// Combinational Delay: 
//
module make_control_store_line (
	output [63:0] control_store,
	input cs_is_cmps_first_uop_all, //0
	input cs_is_cmps_second_uop_all, //1
	input [1:0] de_datasize_all, //2-3
	input cs_is_first_of_repne, //4
	input de_dr1_write_wb, //5
	input de_dr2_write_wb, //6
	input de_dr3_write_wb, //7
	input [6:0] de_flags_affected_wb, //8-14
	input [2:0] de_aluk_ex //15-17
	);

	assign control_store [0] = cs_is_cmps_first_uop_all; 
	assign control_store [1] = cs_is_cmps_second_uop_all; 
	assign control_store [3:2] = de_datasize_all; 
	assign control_store [4] = cs_is_first_of_repne;
	assign control_store [5] = de_dr1_write_wb;
	assign control_store [6] = de_dr2_write_wb;
	assign control_store [7] = de_dr2_write_wb;
	assign control_store [14:8] = de_flags_affected_wb; 
	assign control_store [17:15] = de_aluk_ex;
	assign control_store [63:18] = 0; 

endmodule

//-------------------------------------------------------------------------------------
//
// 					 			Undo Control Store
//
//-------------------------------------------------------------------------------------
// Functionality: Generate the control store from individual wires
//
// Combinational Delay: 
//
module undo_control_store (
	output cs_is_cmps_first_uop_all, //0
	output cs_is_cmps_second_uop_all, //1
	output [1:0] de_datasize_all, //2-3
	output cs_is_first_of_repne, //4
	output de_dr1_write_wb, //5
	output de_dr2_write_wb, //6
	output de_dr3_write_wb, //7
	output [6:0] de_flags_affected_wb, //8-14
	output [2:0] de_aluk_ex, //15-17
	input [63:0] control_store
	);

	assign cs_is_cmps_first_uop_all = control_store [0];
	assign cs_is_cmps_second_uop_all = control_store [1];
	assign de_datasize_all = control_store [3:2];
	assign cs_is_first_of_repne = control_store [4];
	assign de_dr1_write_wb = control_store [5];
	assign de_dr2_write_wb = control_store [6];
	assign de_dr2_write_wb = control_store [7];
	assign de_flags_affected_wb = control_store [14:8];
	assign de_aluk_ex = control_store [17:15];

endmodule