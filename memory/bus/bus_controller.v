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


module  ctrler_gen_n_state(output [7:0] next_state,
			   input [7:0] current_state,
			   input EN, BG,
			   input [2:0] MY_ID, DEST,
			   input DONE);



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

   