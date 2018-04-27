module bus_controller(//interface with bus
		      input BUS_CLK,
		      input RST, SET,
		      input [2:0] MY_ID,
		      inout [31:0] D,
		      inout [15:0] A,
		      inout [2:0] MASTER,
		      inout [2:0] DEST,
		      inout [11:0] SIZE,
		      inout RW,
		      inout ACK,
		      //interface with arbitrator
		      output BR,
		      input BG,
		      //interface with work unit
		      input MOD_EN, //simple signal saying we have a request
		      input MOD_WR,
		      input [15:0] MOD_A,
		      input [127:0] MOD_WRITE_DATA,
		      output [127:0] MOD_READ_DATA,
		      output MOD_R
		      //needs to be modifed for each unit
		      );
   //CURRENT STATE REG
   wire [7:0] 		    current_state, next_state;
   dff8$ state_reg(BUS_CLK, next_state, current_state, , RST, SET);

   //GENERATE NEXT STATE
   ctrler_gen_n_state ctrler_gen_n_state_u(next_state, current_state, MOD_EN, BG, MY_ID, DEST, DONE);


   //GENERATE CTRL SIGNALS



   //REGISTERS FOR THE CONTROLLER
      wire 	[15:0]	    current_size, next_size;
   ioreg16$ size_reg(BUS_CLK, current_size , next_size, , RST, SET);

   wire [31:0] 		    data_buffer_in, data_buffer_out;
   ioreg32$ data_buffer(BUS_CLK, data_buffer_in, data_buffer_out, , RST, SET);
   

endmodule // bus_controller


module ctrler_gen_n_state(
	output [7:0] next_state,
	input [7:0] current_state,
	input EN, BG, ACK,
	input [2:0] MY_ID, DEST,
	input DONE
	);
	
	wire dest_eq_us;

	equalitycheck3 u_equalitycheck3(dest_eq_us, MY_ID, DEST);	

	wire RW_not, dest_eq_us_not, EN_not, BG_not, DONE_not, ACK_not;  

	inv1$ u_RW_not(RW_not, RW);
	inv1$ u_dest_eq_us_not(dest_eq_us_not, dest_eq_us);
	inv1$ u_EN_not(EN_not, EN);
	inv1$ u_BG_not(BG_not, BG);
	inv1$ u_DONE_not(DONE_not, DONE);
	inv1$ u_ACK_not(ACK_not, ACK);

	wire s4_RWnot, s3_DONE, s2_ACK_RWnot, s0_ENnot, s5_Done; 
	wire s0_EN_destusnot, s1_BGnot_destusnot;
	wire s1_BG, s2_ACKnot;
	wire s2_ACK_RW, s3_DONEnot;
	wire s0_destus, s1_destus;
	wire s4_RW, s5_DONEnot;

	and2$ u_s4_RWnot(s4_RWnot, current_state[4], RW_not);
	and2$ u_s3_DONE(s3_DONE, current_state[3], DONE);
	and3$ u_s2_ACK_RWnot(s2_ACK_RWnot, current_state[2], ACK, RW_not);
	and2$ u_s0_ENnot(s0_ENnot, current_state[0], EN_not);
	and2$ u_s5_Done(s5_Done, current_state[5], DONE);

	and3$ u_s0_EN_destusnot(s0_EN_destusnot, current_state[0], EN, dest_eq_us_not);
	and3$ u_s1_BGnot_destusnot(s1_BGnot_destusnot, current_state[1], BG_not, dest_eq_us_not);

	and2$ u_s1_BG(s1_BG, current_state[1], BG);
	and2$ u_s2_ACKnot(s2_ACKnot, current_state[2], ACK_not);

	and3$ u_s2_ACK_RW(s2_ACK_RW, current_state[2], ACK, RW);
	and2$ u_s3_DONEnot(s3_DONEnot, current_state[3], DONE_not);

	and2$ u_s0_destus(s0_destus, current_state[0], dest_eq_us);
	and2$ u_s1_destus(s1_destus, current_state[1], dest_eq_us);

	and2$ u_s4_RW(s4_RW, current_state[4], RW);
	and2$ u_s1_destus(s1_destus, current_state[1], dest_eq_us);

	and2$ u_s4_RW(s4_RW, current_state[4], RW);
	and2$ u_s5_DONEnot(s5_DONEnot, current_state[5], DONE_not);

	or1_5way u_s0(next_state[0], s4_RWnot, s3_DONE, s2_ACK_RWnot, s0_ENnot, s5_Done);
	or2$ u_s1(next_state[1], s0_EN_destusnot, s1_BGnot_destusnot);
	or2$ u_s2(next_state[2], s1_BG, s2_ACKnot);
	or2$ u_s3(next_state[3], s2_ACK_RW, s3_DONEnot);
	or2$ u_s4(next_state[4], s0_destus, s1_destus);
	or2$ u_s5(next_state[5], s4_RW, s5_DONEnot);


endmodule // ctrler_gen_n_state


module arbitrator(input BUS_CLK,
		  input [5:0] BR,
		  output [5:0] BG);



endmodule // arbitrator



module ioreg32$(input CLK,
		input [31:0] D,
		output [31:0] Q,
		output [31:0] QBAR,
		input CLR,
		input PRE);
   ioreg16$ low(CLK, D[15:0], Q[15:0], QBAR[15:0], CLR, PRE);
   ioreg16$ high(CLK, D[31:16], Q[31:16], QBAR[31:16], CLR, PRE);
endmodule // ioreg32

   