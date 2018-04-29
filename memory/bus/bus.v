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
   

   wire        MOD_EN;
   wire        MOD_WR;
   wire [15:0] MOD_A;
   wire [127:0] MOD_WRITE_DATA;
   wire [127:0] MOD_READ_DATA;
   wire 	MOD_R;
   

   bus_controller bus_c_u(BUS_CLK,
			  RST, SET,
			  3'b001,			  
			  D,
			  A,
			  MASTER,
			  DEST,
			  SIZE,
			  RW,
			  ACK,
			  BR[0],
			  BG[0],
			  MOD_EN,
			  MOD_WR,
			  MOD_A,
			  MOD_WRITE_DATA,
			  MOD_READ_DATA,
			  MOD_R
			  );

   arbitrator arb_u(BUS_CLK,
		    RST, SET,
		    BR,
		    BG);
		    





endmodule // bus
