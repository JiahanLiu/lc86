`timescale 1ns/1ps

module  FULL_MEMORY(//lines between dcache bus controller and dcache
		    input DC_EN, //simple signal saying we have a request
		    input DC_WR,
		    input [15:0] DC_A,
		    input [127:0] DC_WRITE_DATA,
		    output [127:0] DC_READ_DATA,
		    output DC_R,//Note this is a signal telling the DC
		               //that the Bus is ready

		    //lintes between icache bus controller and icache
		    input IC_EN, //simple signal saying we have a request
		    input IC_WR,
		    input [15:0] IC_A,
		    input [127:0] IC_WRITE_DATA,
		    output [127:0] IC_READ_DATA,
		    output IC_R,

		    //lines between interrupt controller and processor
		    input INTR_EN, //simple signal saying we have a request
		    input INTR_WR,
		    input [15:0] INTR_A,
		    input [127:0] INTR_WRITE_DATA,
		    output [127:0] INTR_READ_DATA,
		    output INTR_R,


		    //The Bus clock and other signals
		    input BUS_CLK,
		    input RST, SET);
   
   


    //THE BUS!
   wire [31:0] 		  D;
   wire [15:0] 		  A;
   wire [11:0] 		  SIZE;
   wire 		  RW;
   
    //interface with arbitrator
   wire [5:0] BR;
   wire [5:0] BG;
   wire [5:0] ACK_OUT;
   wire       ACK_IN;

   //destination wires
   //memory accesses
   wire       DC_to_MEM, IC_to_MEM;
   wire       MEM_to_DC, MEM_to_IC;
   //IO to mem
   wire       DMA_to_MEM, KBD_to_MEM;
   //Interrupt stuff
   wire       DMA_to_INTR, KBD_to_INTR;
   //Caches writing to IO
   wire       DC_to_DMA, DC_to_KBD;

   //the arbitrator!
   arbitrator arbitrator_u(BUS_CLK,
		  RST, SET,
		  BR,
		  BG,
		  ACK_OUT,
		  ACK_IN);

   //ICACHE PORT
   cache_bus_controller ICACHE_PORT(BUS_CLK,
				    RST, SET,
				    D,
				    A,
				    SIZE,
				    RW,
				    BR[0],
				    BG[0],
				    ACK_OUT[0],
				    ACK_IN,
				    //NEED TO MAKE MODULE HAVE DEST LOGIC
				    DEST_OUT,
				    DEST_IN,
				    IC_EN,
				    IC_WR,
				    IC_A,
				    IC_WRITE_DATA,
				    IC_READ_DATA,
				    IC_R
				    );

   //DCACHE PORT
   cache_bus_controller DCACHE_PORT(BUS_CLK,
				    RST, SET,
				    D,
				    A,
				    SIZE,
				    RW,
				    BR[1],
				    BG[1],
				    ACK_OUT[1],
				    ACK_IN,
				    //NEED TO MAKE MODULE HAVE DEST LOGIC
				    DEST_OUT,
				    DEST_IN,
				    DC_EN,
				    DC_WR,
				    DC_A,
				    DC_WRITE_DATA,
				    DC_READ_DATA,
				    DC_R
				    );

   //Main Memory Bus Controller
   //Will insert when confident ports are correct

   //KBD controller
   //will insert when confident ports are correct
   
   //DMA controller
   //Will insert when confident ports are correct

   //Interrupt Bus port
   //Will insert when confident ports are correct


endmodule


