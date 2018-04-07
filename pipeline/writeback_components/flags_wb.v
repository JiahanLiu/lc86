//-------------------------------------------------------------------------------------
//
// 								Update Flags
//
//-------------------------------------------------------------------------------------
// Functionality: Updates Affected
//
// Combinational Delay: 
//
module Flags_WB(
	output [31:0] current_flags,
	input CLK, 
	input v_cs_ld_flags_wb,
	input [6:0] de_flags_affected_wb,
	input [31:0] WB_FLAGS
	);

wire [31:0] internal_current_flags;
wire [31:0] next_flags; 

assign current_flags = internal_current_flags; 

reg32e$ flags_register (CLK, next_flags, internal_current_flags, , 1'b1, 1'b1, v_cs_ld_flags_wb);

integer i;
for(i = 12; i < 32; i++) begin
	assign next_flags[i] = current_flags[i]; 
end
assign next_flags[9] = current_flags[9];
assign next_flags[8] = current_flags[8];
assign next_flags[5] = current_flags[5];
assign next_flags[3] = current_flags[3];
assign next_flags[1] = current_flags[1];
mux2$ u_mux_flag_6(next_flags[11], internal_current_flags[11], WB_FLAGS[11], de_flags_affected_wb[6]);
mux2$ u_mux_flag_5(next_flags[10], internal_current_flags[10], WB_FLAGS[10], de_flags_affected_wb[5]);
mux2$ u_mux_flag_4(next_flags[7], internal_current_flags[7], WB_FLAGS[7], de_flags_affected_wb[4]);
mux2$ u_mux_flag_3(next_flags[6], internal_current_flags[6], WB_FLAGS[6], de_flags_affected_wb[3]);
mux2$ u_mux_flag_2(next_flags[4], internal_current_flags[4], WB_FLAGS[4], de_flags_affected_wb[2]);
mux2$ u_mux_flag_1(next_flags[2], internal_current_flags[2], WB_FLAGS[2], de_flags_affected_wb[1]);
mux2$ u_mux_flag_0(next_flags[0], internal_current_flags[0], WB_FLAGS[0], de_flags_affected_wb[0]);


//Flags is a 32 bit register. Here each flag's location within the register:
/*
assign flags[11] = OF; 
assign flags[10] = DF; 

assign flags[7] = SF; 
assign flags[6] = ZF; 

assign flags[4] = AF; 
assign flags[2] = PF; 
assign flags[0] = CF; 
*/

endmodule // Flags_WB