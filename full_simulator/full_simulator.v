 `timescale 1ns/1ps

module FULL_SIMULATOR(input CLK,
		      input BUS_CLK,
		      input RST, SET);

   //DCACHE WIRES
   wire 		    DC_EN; 
   wire 		    DC_WR;
   wire [15:0] 		    DC_A;
   wire [127:0] 	    DC_WRITE_DATA;
   wire [127:0] 	    DC_READ_DATA;
   wire 		    DC_R;


   //ICACHE WIRES
   wire 		    IC_EN; 
   wire 		    IC_WR;
   wire [15:0] 		    IC_A;
   wire [127:0] 	    IC_WRITE_DATA;
   wire [127:0] 	    IC_READ_DATA;
   wire 		    IC_R;

   //INTERRUPT WIRES
   wire 		    INTR_EN; 
   wire 		    INTR_WR;
   wire [15:0] 		    INTR_A;
   wire [127:0] 	    INTR_WRITE_DATA;
   wire [127:0] 	    INTR_READ_DATA;
   wire 		    INTR_R;
   wire 		    INTERRUPT;
   assign INTR_EN = 0;
      
   //THE FULL MEMORY MODULE
   FULL_MEMORY u_full_memory (
			     DC_EN,
			     DC_WR,
			     DC_A,
			     DC_WRITE_DATA,
			     DC_READ_DATA,
			     DC_R,
		             
			     IC_EN,
			     IC_WR,
			     IC_A,
			     IC_WRITE_DATA,
			     IC_READ_DATA,
			     IC_R,
			     
			     INTR_EN, 
			     INTR_WR,
			     INTR_A,
			     INTR_WRITE_DATA,
			     INTR_READ_DATA,
			     INTR_R,
			      INTERRUPT,

			     BUS_CLK,
			     RST, SET);


   //TODO: add wiring for interrupts
   //THE FULL PIPELINE MODULE
PIPELINE u_pipeline ( CLK, RST, SET,
		     IC_WR, IC_EN,
		     IC_A,
		     IC_WRITE_DATA,
		     IC_R,
		     IC_READ_DATA,

		     DC_WR, DC_EN,
		     DC_A,
		     DC_WRITE_DATA,
		     DC_R,
		     DC_READ_DATA,
		      INTERRUPT);



endmodule // FULL_SIMULATOR
