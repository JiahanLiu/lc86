module bus_controller(input BUS_CLK,
		      input MY_ID,
		      inout [31:0] D,
		      inout [15:0] A,
		      inout [2:0] MASTER,
		      inout [2:0] DEST,
		      inout [11:0] SIZE,
		      inout RW,
		      inout ACK,
		      output BR,
		      input BG);


endmodule // bus_controller


module arbitrator(input BUS_CLK,
		  input [2:0] BR,
		  output [2:0] BG);



endmodule // arbitrator

		      