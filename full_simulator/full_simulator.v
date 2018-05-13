 `timescale 1ns/1ps

module FULL_SIMULATOR(input CLK,
		      input BUS_CLK,
		      input RST, SET);

   //DCACHE WIRES
   wire 		    DC_EN, DC_IO_EN; 
   wire 		    DC_WR;
   wire [15:0] 		    DC_A;
   wire [15:0] 		    DC_STEADY_A;
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

   and3$ MEM_IO(INTR_SEL, DC_A[12], DC_A[13], DC_A[14]);
   inv1$ DC_SEL_U(DC_SEL, INTR_SEL);
   and2$ DC_EN_DRIVER(DC_EN, DC_SEL, DC_IO_EN);
   and2$ INTR_EN_DRIVER(INTR_EN, INTR_SEL, DC_IO_EN);

   //selecting return data based on adress
   wire [127:0] 	    DC_IO_READ_DATA;
   mux4_128$ DATA_SEL(DC_IO_READ_DATA,
	     DC_READ_DATA,DC_READ_DATA,
	     INTR_READ_DATA, INTR_READ_DATA,
	     INTR_SEL, INTR_SEL);
   or2$ READY_DRIV(DC_IO_R, INTR_R, DC_R);
      
   assign INTR_WR = DC_WR;
   assign INTR_A = DC_A;
   assign INTR_WRITE_DATA = DC_WRITE_DATA;
   wire [15:0] 		    DC_A_ALIGNED, IC_A_ALIGNED;
   
   assign DC_A_ALIGNED = {DC_A[15:4], 4'b0};
   assign IC_A_ALIGNED = {IC_A[15:4], 4'b0};
   
   //THE FULL MEMORY MODULE
   FULL_MEMORY u_full_memory (
			     DC_EN,
			     DC_WR,
			     DC_A_ALIGNED,
			     DC_WRITE_DATA,
			     DC_READ_DATA,
			     DC_R,
		             
			     IC_EN,
			     IC_WR,
			     IC_A_ALIGNED,
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

		     DC_WR, DC_IO_EN,
		     DC_A,
		      DC_STEADY_A,
		     DC_WRITE_DATA,
		     DC_IO_R,
		     DC_IO_READ_DATA,
		      INTERRUPT);



endmodule // FULL_SIMULATOR
