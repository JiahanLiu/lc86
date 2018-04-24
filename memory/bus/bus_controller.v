module bus_controller(//interface with bus
		      input BUS_CLK,
		      input RST, SET,
		      input MY_ID,
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
		      input EN, //simple signal saying we have a request
		      input M_WR
		      //needs to be modifed for each unit
		      );
   //CURRENT STATE REG
   wire [7:0] 		    current_state, next_state;
   dff8$(BUS_CLK, next_state, current_state, , RST, SET);

   //GENERATE NEXT STATE
   ctrler_gen_n_state(next_state, current_state, EN, BG, MY_ID, DEST, DONE);


   //GENERATE CTRL SIGNALS


   


endmodule // bus_controller


module  ctrler_gen_n_state(output [7:0] next_state,
			   input [7:0] current_state,
			   input EN, BG,
			   input [2:0] MY_ID, DEST,
			   input DONE);



endmodule // ctrler_gen_n_state
   








module arbitrator(input BUS_CLK,
		  input [2:0] BR,
		  output [2:0] BG);



endmodule // arbitrator

		      