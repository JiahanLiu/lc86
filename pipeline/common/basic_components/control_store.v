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
	input cs_is_cmps_first_uop_all, 
	input cs_is_cmps_second_uop_all, 
	input cs_is_first_of_repne_wb, 
	input cs_ld_gpr2_wb, 
	input cs_ld_gpr3_wb,
	input cs_ld_flags_wb
	);

	assign control_store [0] = cs_is_cmps_first_uop_all; 
	assign control_store [1] = cs_is_cmps_second_uop_all; 
	assign control_store [2] = cs_is_first_of_repne_wb;
	assign control_store [3] = cs_ld_gpr2_wb;
	assign control_store [4] = cs_ld_gpr3_wb;
	assign control_store [5] = cs_ld_flags_wb; 

	assign control_store [63:5] = 0; 

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
	output cs_is_cmps_first_uop_all, 
	output cs_is_cmps_second_uop_all, 
	output cs_is_first_of_repne_wb, 
	output cs_ld_gpr2_wb, 
	output cs_ld_gpr3_wb, 
	output cs_ld_flags_wb, 
	input [63:0] control_store
	);

	assign cs_is_cmps_first_uop_all = control_store [0];
	assign cs_is_cmps_second_uop_all = control_store [1];
	assign cs_is_first_of_repne = control_store [2];
	assign cs_ld_gpr2_wb = control_store [3];
	assign cs_ld_gpr3_wb = control_store [4];
	assign cs_ld_flags_wb = control_store[5]; 

endmodule