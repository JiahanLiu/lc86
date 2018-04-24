module bus();
   //signals on the bus!
   wire BUS_CLK, RW, ACK;
   wire [31:0] D;
   wire [15:0] A;
   wire [2:0]  MASTER, DEST;
   wire [11:0] SIZE;

   //bus grant and write signals
   wire [5:0]  BR, BG;
   wire        SET, RST;
   
   
   bus_controller bus_c_u(BUS_CLK,
			  RST, SET,
		      D,
		      A,
		      MASTER,
		      DEST,
		      SIZE,
		      RW,
		      ACK,
		      BR[0],
		      BG[0],
			  );

   arbitrator arb_u(BUS_CLK,
		    BR,
		    BG);
		    





endmodule // bus
