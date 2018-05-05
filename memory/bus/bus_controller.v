
//IMPORTANT: This module is the template bus controller
//EACH Memory module has a slightly specialized version of this controller
module bus_controller(//interface with bus
		      input BUS_CLK,
		      input RST, SET,
		      inout [31:0] D,
		      inout [15:0] A,
		      inout [11:0] SIZE,
		      inout RW,

		      //interface with arbitrator and other controllers
		      output BR,
		      input BG,
		      output ACK_OUT,
		      input ACK_IN,
		      output DEST_OUT,//wire goes directly to RAM
		      input DEST_IN,
		      //interface with work unit
		      //needs to be modifed for each unit
		      input MOD_EN, //simple signal saying we have a request
		      input MOD_WR,
		      input [15:0] MOD_A,
		      input [127:0] MOD_WRITE_DATA,
		      output [127:0] MOD_READ_DATA,
		      output MOD_R

		      );
   //CURRENT STATE REG
   wire [7:0] 		    current_state, next_state;
   dff8$ state_reg(BUS_CLK, next_state, current_state, , RST, SET);

   //GENERATE NEXT STATE
      parameter IDLE  = 8'b0000_0001,
		  ST_BR  = 8'b0000_0010,
		  MSTR = 8'b0000_0100,
		  ST_WR = 8'b0000_1000,
		  SLV = 8'b0001_0000,
		  ST_RD = 8'b0010_0000;
   wire 		    BUS_CLK_DEL;
   assign #(0.5) BUS_CLK_DEL = BUS_CLK;
   


   //GENERATE CTRL SIGNALS
   gen_ctrl_bus gen_ctrl_bus_u(current_state, CTRL_TRI_EN, D_TRI_EN, ACK_OUT, BR, SIZE_DECR, RD_BUS_CTRL);
   wire 		    DONE;
   ctrler_gen_n_state ctrler_gen_n_state_u(next_state, current_state, MOD_EN, BG, ACK_IN, RW, DEST_IN, DONE);
   wire [2:0] 		    amnt_decr;
   wire [15:0] 		    current_size, current_size_in, next_size;
   assign next_size[15:12] = 0;
   size_decrement size_decrement_u(next_size[11:0], amnt_decr, DONE, current_size[11:0], A);


   //REGISTERS FOR THE CONTROLLER
   //SIZE REGISTER: muxed between the decremented value or 16
   mux2_16$ mux_size_u(current_size_in, 16'h0010, next_size, SIZE_DECR);
   ioreg16$ size_reg(BUS_CLK, current_size_in, current_size, , RST, SET);

   //DATA BUFFER
   wire [127:0] 		    data_buffer_bus, data_buffer_in, data_buffer_out;
   wire [3:0]			    SIZE_SELECT;
   wire [1:0] 			    next_size_bar;
   //as size goes down, buffer location goes up
   inv1$ siz_bar_u_0(next_size_bar[0], next_size[2]);
   inv1$ siz_bar_u_1(next_size_bar[1], next_size[3]);
   decoder2_4$ size_decode(next_size_bar, SIZE_SELECT, );
   wire [3:0] 			    RD_BUS;
   and2$ rd_0(RD_BUS[0], SIZE_SELECT[0], RD_BUS_CTRL);
   and2$ rd_1(RD_BUS[1], SIZE_SELECT[1], RD_BUS_CTRL);
   and2$ rd_2(RD_BUS[2], SIZE_SELECT[2], RD_BUS_CTRL);
   and2$ rd_3(RD_BUS[3], SIZE_SELECT[3], RD_BUS_CTRL);
   //muxes select between updating reading from bus or staying same
   mux32_2way mux_u_0(data_buffer_in[31:0],data_buffer_out[31:0] , D, RD_BUS[0]);
   mux32_2way mux_u_1(data_buffer_in[63:32],data_buffer_out[63:32] , D, RD_BUS[1]);
   mux32_2way mux_u_2(data_buffer_in[95:64],data_buffer_out[95:64] , D, RD_BUS[2]);
   mux32_2way mux_u_3(data_buffer_in[127:96],data_buffer_out[127:96] , D, RD_BUS[3]);
   ioreg128$ data_buffer(BUS_CLK, data_buffer_in, data_buffer_out, , RST, SET);
   assign MOD_READ_DATA = data_buffer_out;
   //DONE BUFFER FOR MAIN UNIT
   wire [7:0] 			    MOD_DONE_IN, MOD_DONE_OUT;
   mux2_8$ READY_SEL(MOD_DONE_IN, 8'b0, 8'HFF, DONE);
   assign 		       MOD_R = MOD_DONE_OUT[0];
   ioreg8$ READY_REG(BUS_CLK, MOD_DONE_IN, MOD_DONE_OUT, , RST, SET);
   
      
   //TRISTATE BUFFERS FOR THE BUS
   wire [31:0] 			    D_TRI_IN;
   mux4_32 D_DRIV_SEL(D_TRI_IN, MOD_WRITE_DATA[31:0], MOD_WRITE_DATA[63:32],
	    MOD_WRITE_DATA[95:64], MOD_WRITE_DATA[127:96],
	    next_size_bar[0], next_size_bar[1]);
   tristate_bus_driver32$ D_TRI(D_TRI_EN, D_TRI_IN, D);



//DEST, ACK, and MASTER IS NO LONGER USED, NOW USING DIRECT CONNECTIONS
/*   wire [2:0] 		    DEST_TRI_IN, MASTER_TRI_IN;
   wire 		    DEST_TRI_EN, MASTER_TRI_EN;
   assign MASTER_TRI_IN = MY_ID;
   assign DEST_TRI_EN = CTRL_TRI_EN;
   assign MASTER_TRI_EN = CTRL_TRI_EN;
   tristate_bus_driver1$ DEST2_TRI(DEST_TRI_EN, DEST_TRI_IN[2], DEST[2]);
   tristate_bus_driver1$ DEST1_TRI(DEST_TRI_EN, DEST_TRI_IN[1], DEST[1]);
   tristate_bus_driver1$ DEST0_TRI(DEST_TRI_EN, DEST_TRI_IN[0], DEST[0]);
   tristate_bus_driver1$ MAS2_TRI(MASTER_TRI_EN, MASTER_TRI_IN[2], MASTER[2]);
   tristate_bus_driver1$ MAS1_TRI(MASTER_TRI_EN, MASTER_TRI_IN[1], MASTER[1]);
   tristate_bus_driver1$ MAS0_TRI(MASTER_TRI_EN, MASTER_TRI_IN[0], MASTER[0]);
 */
    wire 		    A_TRI_EN;
   assign A_TRI_EN = CTRL_TRI_EN;
   tristate_bus_driver16$ A_TRI(A_TRI_EN, MOD_A, A);
   

   wire [11:0] 		    SIZE_TRI_IN;
   assign SIZE_TRI_IN = 12'h010; //Always sending 16 bytes on the bus
   wire 		    SIZE_TRI_EN;
   assign SIZE_TRI_EN = CTRL_TRI_EN;
   tristate_bus_driver8$ SIZE8_TRI(SIZE_TRI_EN, SIZE_TRI_IN[11:4], SIZE[11:4]);
   tristate_bus_driver1$ SIZE3_TRI(SIZE_TRI_EN, SIZE_TRI_IN[3], SIZE[3]);
   tristate_bus_driver1$ SIZE2_TRI(SIZE_TRI_EN, SIZE_TRI_IN[2], SIZE[2]);
   tristate_bus_driver1$ SIZE1_TRI(SIZE_TRI_EN, SIZE_TRI_IN[1], SIZE[1]);
   tristate_bus_driver1$ SIZE0_TRI(SIZE_TRI_EN, SIZE_TRI_IN[0], SIZE[0]);
   
   wire 		    RW_TRI_IN, ACK_TRI_IN;
   wire 		    RW_TRI_EN;
   assign RW_TRI_EN = CTRL_TRI_EN;
   assign RW_TRI_IN = MOD_WR;
   assign ACK_TRI_IN = 1'b1;
   tristate_bus_driver1$ RW_TRI(RW_TRI_EN, RW_TRI_IN, RW);
   tristate_bus_driver1$ ACK_TRI(ACK_TRI_EN, ACK_TRI_IN, ACK);
   

endmodule // bus_controller


module ctrler_gen_n_state(
	output [7:0] next_state,
	input [7:0] current_state,
	input EN, BG, ACK, RW,
	input DEST_IN,
	input DONE
	);
	
	wire dest_eq_us;
        assign dest_eq_us = DEST_IN;
   


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
	and3$ u_s0_ENnot(s0_ENnot, current_state[0], EN_not, dest_eq_us_not);
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
	and2$ u_s1_destus1(s1_destus, current_state[1], dest_eq_us);

	and2$ u_s4_RW1(s4_RW, current_state[4], RW);
	and2$ u_s5_DONEnot(s5_DONEnot, current_state[5], DONE_not);

	or1_5way u_s0(next_state[0], s4_RWnot, s3_DONE, s2_ACK_RWnot, s0_ENnot, s5_Done);
	or2$ u_s1(next_state[1], s0_EN_destusnot, s1_BGnot_destusnot);
	or2$ u_s2(next_state[2], s1_BG, s2_ACKnot);
	or2$ u_s3(next_state[3], s2_ACK_RW, s3_DONEnot);
	or2$ u_s4(next_state[4], s0_destus, s1_destus);
	or2$ u_s5(next_state[5], s4_RW, s5_DONEnot);
   assign next_state[6] = 0;
   assign next_state[7] = 0;
   


endmodule // ctrler_gen_n_state


module gen_ctrl_bus(input[7:0] current_state,
		    output CTRL_TRI_ENBAR, D_TRI_ENBAR, ACK_TRI_ENBAR, BR_EN, SIZE_DECR, RD_BUS);
   wire IDLE  = current_state[0];
   wire BR = current_state[1];
   wire MSTR = current_state[2];
   wire WR = current_state[3];
   wire SLV = current_state[4];
   wire RD = current_state[5];
   or2$ CTRL_u(CTRL_TRI_EN, MSTR, WR);
   assign D_TRI_EN = WR;
   assign ACK_TRI_EN = SLV;
   or3$ BR_u(BR_EN, BR, MSTR, WR);
   or2$ DECR_u(SIZE_DECR, WR, RD);
   assign RD_BUS = RD;
   inv1$ CTRL_IN(CTRL_TRI_ENBAR, CTRL_TRI_EN);
   inv1$ D_Inv(D_TRI_ENBAR, D_TRI_EN);
   inv1$ ACK_INV(ACK_TRI_ENBAR, ACK_TRI_EN);
   
endmodule // gen_ctrl_bus


module	equalitycheck_bus (output dest_eq_us,
			   input [2:0] MY_ID,
			   input [2:0] DEST);
   wire [2:0] 			 one_equal, zero_equal, MY_ID_BAR, equal;
   and2$ eq_1 [2:0](one_equal, MY_ID, DEST);
   inv1$ inv [2:0](MY_ID_BAR, MY_ID);
   and2$ eq_0 [2:0](zero_equal, MY_ID_BAR, DEST);
   
   or2$ eq [2:0](equal, zero_equal, one_equal);
   and3$ all_eq(dest_eq_us, equal[2], equal[1], equal[0]);
endmodule // equalitycheck_bus



module ioreg128$(input CLK,
		input [127:0] D,
		output [127:0] Q,
		output [127:0] QBAR,
		input CLR,
		input PRE);
   ioreg32$ low(CLK, D[31:0], Q[31:0], QBAR[31:0], CLR, PRE);
   ioreg32$ next(CLK, D[63:32], Q[63:32], QBAR[63:32], CLR, PRE);
   ioreg32$ nexter(CLK, D[95:64], Q[95:64], QBAR[95:64], CLR, PRE);
   ioreg32$ high(CLK, D[127:96], Q[127:96], QBAR[127:96], CLR, PRE);
endmodule // ioreg128



module ioreg32$(input CLK,
		input [31:0] D,
		output [31:0] Q,
		output [31:0] QBAR,
		input CLR,
		input PRE);
   ioreg16$ low(CLK, D[15:0], Q[15:0], QBAR[15:0], CLR, PRE);
   ioreg16$ high(CLK, D[31:16], Q[31:16], QBAR[31:16], CLR, PRE);
endmodule // ioreg32

module  tristate_bus_driver32$(enbar, in, out);

   input enbar;
   input [31:0] in;
   output [31:0] out;

   tristate_bus_driver16$ a(enbar, in[15:0], out[15:0]);
   tristate_bus_driver16$ b(enbar, in[31:16], out[31:16]);
   

endmodule // tristate_bus_driver16


module done_logic(output DONE,//Not used anymore
		  input [11:0] next_size);
   equal_to_zero done_checker(DONE, {20'h00000, next_size});


endmodule // done_logic

   

module size_decrement(output [11:0] next_size,
		      output [2:0] amnt_decr,
		      output DONE,
		      input [11:0] current_size,
		      input [15:0] A);
   wire 			   OFFSET = A[1:0];
   wire 			   SIZE_OFFSET = current_size[1:0];
   wire 			   done_temp;
   equal_to_zero done_t_checker(DONE, {22'h000000, next_size[11:2]});
   assign amnt_decr = 3'b100;//always remove 4 bytes from the access
   assign next_size = current_size - amnt_decr;
   
   
   
   //calculating offset stuff
   //This logic is almost entirely for the DMA transfers that do not
   //have to be word aligned or of word size
   // Decr_temp[1] = (A[0] XOR A[1]) OR (SIZE[1] AND A=00)
   // Decr_temp[0] = A[0] OR (SIZE[0] AND A=00)
   //Decr_temp is used if A != 0 or we are done and size has an offset
/*   wire  [1:0]			   decr_temp;
   wire 			   no_a_offset,yes_a_offset, a_xor, temp_0, temp_1;
   nor2$ no_a_u(no_a_offset, OFFSET[0], OFFSET[1]);
   or2$ yes_a_u(yes_a_offset, OFFSET[0], OFFSET[1]);
   xor2$ a_xor_u(a_xor, OFFSET[0], OFFSET[1]);
   and2$ temp_1_u(temp_1, SIZE_OFFSET[1], no_a_offset);
   and2$ temp_0_u(temp_0, SIZE_OFFSET[0], no_a_offset);
   or2$ dec_1(decr_temp[1], temp_1, a_xor);
   or2$ dec_0(decr_temp[0], temp_0, OFFSET[0]);

   //Calculating if we are done or not
   // Done if size=4 and no offsets
   // or if size<4 and address<4 and size+address<=4
   wire 			   small_present, big_carry, big_present, not_simple;
   or4$ not_simple_u(not_simple, OFFSET[0], OFFSET[1], SIZE_OFFSET[0], SIZE_OFFSET[1]);
   and2$ big_carry_u(big_carry, OFFSET[1], SIZE_OFFSET[1]);
   or2$ small_present_u(small_present, OFFSET[0], SIZE_OFFSET[0]);*/
   //THIS IS ONLY NECESSARY FOR THE DMA, WHICH WILL BE BEHAVIORAL!
endmodule // size_decrement
