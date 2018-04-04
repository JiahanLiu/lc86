
//-------------------------------------------------------------------------------------
// logic_gates
// --------------------
// EE382N, Spring 2018
// Apruv Narkhede, Nelson Wu, Steven Flolid, Jiahan Liu
//
// and1_5way                        - 1-Bit 5-Input AND Gate         
// and32_2way                       - a32 & b32                      
// or1_5way                         - 1-Bit 5-Input OR Gate          
// or1_6way                         - 1-Bit 6-Input OR Gate          
// or32_2way                        - a32 | b32                      
// not4_1way                        - !a4                            
// not32_1way                       - !a32                           
// buffer32_4x                      - 32-Bit 1x->4x Buffer   
// buffer32_16x						- 32-Bit 1x->16x Buffer        
//
//-------------------------------------------------------------------------------------

//-------------------------------------------------------------------------------------
//
// 					 			1-Bit 5-Input AND Gate
//
//-------------------------------------------------------------------------------------
// Functionality: 1-Bit 5-Input AND Gate
//
// Combinational Delay: 
//
module and1_5way (
	output and_out,
	input a, b, c, d, e
	);

	wire intermediate_3side, intermediate_2side;

	and3$ u_and_intermediate3 (intermediate_3side, a, b, c);
	and2$ u_and_intermedaite2 (intermediate_2side, d, e);

	and2$ u_and_final (and_out, intermediate_3side, intermediate_2side);

endmodule

//-------------------------------------------------------------------------------------
//
// 					 		 32-Bit 2-Input AND Gate
//
//-------------------------------------------------------------------------------------
// Functionality: a32 & b32
//
// Combinational Delay: 
//
module and32_2way (
	output [31:0] and_out, 
	input [31:0] a,
	input [31:0] b
	);

	genvar i;
	generate
		for(i = 0; i < 32; i = i + 1)
		begin : u_and
			and2$ u_and (and_out[i], a[i], b[i]);
		end 
	endgenerate

endmodule

//-------------------------------------------------------------------------------------
//
// 					 			1-Bit 5-Input OR Gate
//
//-------------------------------------------------------------------------------------
// Functionality: 1-Bit 5-Input OR Gate
//
// Combinational Delay: 
//
module or1_5way (
	output or_out,
	input a, b, c, d, e
	);

	wire intermediate_3side, intermediate_2side;

	or3$ u_or_intermediate3 (intermediate_3side, a, b, c);
	or2$ u_or_intermedaite2 (intermediate_2side, d, e);

	or2$ u_or_final (or_out, intermediate_3side, intermediate_2side);

endmodule

//-------------------------------------------------------------------------------------
//
// 					 			1-Bit 6-Input OR Gate
//
//-------------------------------------------------------------------------------------
// Functionality: 1-Bit 6-Input OR Gate
//
// Combinational Delay: 
//
module or1_6way (
	output or_out,
	input a, b, c, d, e, f
	);

	wire intermediate_3side_1, intermediate_3side_2;

	or3$ u_or_intermediate3_1 (intermediate_3side_1, a, b, c);
	or3$ u_or_intermedaite3_2 (intermediate_3side_2, d, e, f);

	or2$ u_or_final (or_out, intermediate_3side_1, intermediate_3side_2);

endmodule

//-------------------------------------------------------------------------------------
//
// 					 			32-Bit 2-Input OR Gate
//
//-------------------------------------------------------------------------------------
// Functionality: a32 | b32
//
// Combinational Delay: 
//
module or32_2way (
	output [31:0] or_out, 
	input [31:0] a,
	input [31:0] b
	);

	genvar i;
	generate
		for(i = 0; i < 32; i = i + 1)
		begin : u_or
			or2$ u_or (or_out[i], a[i], b[i]);
		end 
	endgenerate

endmodule

//-------------------------------------------------------------------------------------
//
// 					 			4-Bit 1-Input NOT Gate
//
//-------------------------------------------------------------------------------------
// Functionality: !a4
//
// Combinational Delay: 
//
module not4_1way (
	output [3:0] not_out,
	input [3:0] a
	);

	genvar i;
	generate
		for(i = 0; i < 4; i = i + 1)
		begin : u_not
			inv1$ u_not (not_out[i], a[i]);
		end 
	endgenerate	

endmodule

//-------------------------------------------------------------------------------------
//
// 					 		32-Bit 1-Input NOT Gate
//
//-------------------------------------------------------------------------------------
// Functionality: !a32
//
// Combinational Delay: 
//
module not32_1way (
	output [31:0] not_out, 
	input [31:0] a
	);

	genvar i;
	generate
		for(i = 0; i < 32; i = i + 1)
		begin : u_not
			inv1$ u_not (not_out[i], a[i]);
		end 
	endgenerate

endmodule

//-------------------------------------------------------------------------------------
//
// 					 		 32-Bit 1-Input Buffer 
//
//-------------------------------------------------------------------------------------
// Functionality: 32-Bit 1x->4x Buffer
//
// Combinational Delay: 
//
module buffer32_4way (
	output [31:0] out,
	input [31:0] in
	);

	buffer16$ u_buffu_high(out[31:16], in[31:16]);
	buffer16$ u_buff_low(out[15:0], in[15:0]);

endmodule

//-------------------------------------------------------------------------------------
//
// 					 		 32-Bit 1-Input Buffer 
//
//-------------------------------------------------------------------------------------
// Functionality: 32-Bit 1x->16x Buffer
//
// Combinational Delay: 
//
module buffer32_16way (
	output [31:0] out0, out1, out2, out3,
	input [31:0] in
	);

	wire [31:0] level_1_intermediate; 

	buffer32_4way buffer_level1_0(level_1_intermediate, in);

	buffer32_4way buffer_level2_0(out0, level_1_intermediate);
	buffer32_4way buffer_level2_1(out1, level_1_intermediate);
	buffer32_4way buffer_level2_2(out2, level_1_intermediate);
	buffer32_4way buffer_level2_3(out3, level_1_intermediate);
endmodule