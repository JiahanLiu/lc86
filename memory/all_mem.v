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
		    output INTERRUPT,


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
   wire       DMA_to_MEM;
   
   //Interrupt stuff
   wire       DMA_to_INTR, KBD_to_INTR;
   wire       INTR_to_DMA, INTR_to_KBD;
   //assign DMA_to_MEM = 0;
      
   //the arbitrator!
//   assign BR[5:3] = 0;
//   assign ACK_OUT[5:3] =0;
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
				    DC_to_MEM,
				    MEM_to_DC,
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
				    IC_to_MEM,
				    MEM_to_IC,
				    DC_EN,
				    DC_WR,
				    DC_A,
				    DC_WRITE_DATA,
				    DC_READ_DATA,
				    DC_R
				    );

   //Main Memory Bus Controller
   //signals between main memory bus port and the main mem itself
   wire       MEM_EN;
   wire       MEM_WR;//Will always be one
   wire [14:0] MEM_A;
   wire [255:0] MEM_INOUT;
   wire [2:0] 	MEM_WR_SIZE;
   wire 	MEM_R;
   mem_bus_controller mem_bus_controller_u(//interface with bus
		      BUS_CLK,
		      RST, SET,
		      D,
		      A,
		      SIZE,
		      RW,
		      //interface with arbitrator and other controllers
		      BR[2],
		      BG[2],
		      ACK_OUT[2],
		      ACK_IN,
		      MEM_to_IC,
		      MEM_to_DC,
		      IC_to_MEM,
		      DC_to_MEM,
		      DMA_to_MEM,
		      //interface with work unit
			  MEM_A,
			  MEM_WR, MEM_EN,
			  MEM_WR_SIZE,
			  MEM_INOUT
		      );


   main_memory main_memory_u (
    MEM_A,
    MEM_WR, MEM_EN,
    MEM_WR_SIZE,
    MEM_INOUT
);
   

   //KBD controller
   kbd_bus_controller KBD_CTRLR_U(
		      BUS_CLK,
		      RST, SET,
		      D,
		      A,
		      SIZE,
		      RW,

		      BR[3],
		      BG[3],
		      ACK_OUT[3],
		      ACK_IN,
		      KBD_to_INTR,
		      INTR_to_KBD
		      );


   
   //DMA controller
   wire [31:0] DISK_ADDR;
   wire [11:0] DISK_SIZE;
   wire        DISK_RST, DISK_EN, DISK_WE;
   wire [32767:0] DISK_DATA;
   DMA_bus_controller DMA_CTRLR_U(
				  BUS_CLK,
				  RST, SET,
				  D,
				  A,
				  SIZE,
				  RW,

				  BR[4],
				  BG[4],
				  ACK_OUT[4],
				  ACK_IN,
				  DMA_to_MEM,
				  DMA_to_INTR,
				  INTR_to_DMA,//always the INTERRUPT port
			  
			  DISK_ADDR, 
			    // Size is from 0 to (2^12)-1
			    DISK_SIZE,  
			    DISK_RST,
			    DISK_WE,
			    DISK_EN, 
			    DISK_DATA);
   //DISK itself
   disk  DISK_U(
    BUS_CLK,
    DISK_ADDR, 
    DISK_SIZE,  
    DISK_RST,
    DISK_WE,
    DISK_EN, 
    DISK_DATA);



   //Interrupt Bus port
   intr_bus_controller INTR_CTRLR_U(
				    BUS_CLK,
				    RST, SET,
				    D,
				    A,
				    SIZE,
				    RW,

				    BR[5],
				    BG[5],
				    ACK_OUT[5],
				    ACK_IN,
				    INTR_to_DMA,
				    INTR_to_KBD,
				    DMA_to_INTR,
				    KBD_to_INTR,

				    INTR_EN,
				    INTR_WR,
				    INTR_A,
				    INTR_WRITE_DATA,
				    INTR_READ_DATA,
				    INTR_R,
				    INTERRUPT
		       );



endmodule


