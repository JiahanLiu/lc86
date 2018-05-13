//DMA has extre logic for the buffers
module DMA_bus_controller(//interface with bus
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
			    output DEST_MEM,
			  output DEST_INTR,
			  input DEST_IN,//always the INTERRUPT port
			  
			  output [31:0] addr, 
			    // Size is from 0 to (2^12)-1
			    output [11:0] size,  
			    output DISK_RST,
			    output WE,
			    output EN, 
			    input [32767:0] data_out

			    
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
   gen_ctrl_bus gen_ctrl_bus_u(current_state, CTRL_TRI_EN, D_TRI_EN, ACK_OUT_BAR, BR, SIZE_DECR, RD_BUS_CTRL);
   //TRI_EN is active low!
   inv1$ DEST_DRIVER (DEST_OUT, CTRL_TRI_EN);
   inv1$ ACK_DRIVER (ACK_OUT, ACK_OUT_BAR);
   
   wire 		    DONE;

   //pending read latch
   wire 		    UPD_EN;
   wire 		    MOD_MASK_OUT, MOD_EN_MASK;
   wire [6:0] 		    filler;
   //updating the pending write latch when request initiated, and when writing/reading
   //TODO: drive this signal!
   reg 		    MOD_EN;
   initial
     begin
	MOD_EN = 0;
     end
   
   ctrler_gen_n_state ctrler_gen_n_state_u(next_state, current_state, MOD_EN, BG, ACK_IN, RW, DEST_IN, DONE);


   
   wire [2:0] 		    amnt_decr;
   wire [15:0] 		    current_size, current_size_in, next_size;
   assign next_size[15:12] = 0;
   size_decrement size_decrement_u(next_size[11:0], amnt_decr, DONE, current_size[11:0], A);


   //REGISTERS FOR THE CONTROLLER
   //The size can either decrement, or it can be loaded from the bus, otherwise stay the same
//   mux4_16$ mux_size_u(current_size_in, opt0, opt1,
//		       opt2, opt3,
//		       sel0, sel1);
   reg 			    interrupt;
   mux2_16$ mux_size_u(current_size_in, 16'h0010 , next_size, SIZE_DECR);
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
   wire [6:0] 			    filler1;
   ioreg8$ READY_REG(BUS_CLK, {7'b0, DONE}, {filler1,MOD_R}, , RST, SET);
   
   

   //REGISTERS FOR THE DMA UNIT ITSELF
   //NEED A STABLE ADDRESS
   wire [15:0] 			    A_IN, A_OUT;
   mux2_16$ A_SEL(A_IN, A_OUT, A, current_state[4]);
   ioreg16$ A_REG(BUS_CLK, A_IN, A_OUT, , RST, SET);
   
   
   wire [31:0] 			    DISK_A_IN, DISK_A_OUT;
   wire [31:0] 			    MEM_A_IN, MEM_A_OUT;
   wire [31:0] 			    SIZE_IN, SIZE_OUT;
   wire [31:0]			    ENABLE_IN, ENABLE_OUT;
   wire [7:0] 			    A_DEC, A_DEC_MASK;
   decoder3_8$ DEST_SEL(A_OUT[4:2], A_DEC, );
   and3$ MASKING [7:0] (A_DEC_MASK, A_DEC, DONE, current_state[5]);
   and2$ FINISHED_WRITING(DONE_WR, DONE, current_state[3]);
      
   //simple
   mux32_2way DISK_A_SEL(DISK_A_IN, DISK_A_OUT, data_buffer_out[31:0],
     A_DEC_MASK[1]);//x7004 disk address

   wire [31:0] add1_out, add2_out, SIZE_OUT_B;
   inv1$ inv1_size[31:0] (SIZE_OUT_B, SIZE_OUT);
   //needs to increment by 4 each cycle
   adder32_w_carry_in add1 (add1_out, , MEM_A_OUT, 32'd4, 1'b0);
   adder32_w_carry_in add2 (add2_out, , SIZE_OUT_B, 32'd4, 1'b1);
   mux32_4way MEM_A_SEL(MEM_A_IN, MEM_A_OUT, data_buffer_out[31:0],
			add1_out, add1_out,
    {DONE_WR,A_DEC_MASK[2]});//x7008 memaddress

   //needs to decrement by 4 each cycle
   mux32_4way SIZE_DMA_SEL(SIZE_IN, SIZE_OUT, data_buffer_out[31:0],
			   add2_out, add2_out,
     {DONE_WR,A_DEC_MASK[3]});//x700C size

   //needs to reset when the DISK finishes
   mux32_4way ENABLE_SEL (ENABLE_IN, ENABLE_OUT, data_buffer_out[31:0],
			  32'b0, 32'b0,
     {DONE_WR,A_DEC_MASK[4]});//x7010 enable
      
   
   ioreg128$ DMA_REGS(BUS_CLK,
		      {DISK_A_IN, MEM_A_IN, SIZE_IN, ENABLE_IN},
		      {DISK_A_OUT, MEM_A_OUT, SIZE_OUT, ENABLE_OUT},
		       , RST, SET);


   //DRIVING THE DISK
   

   assign DISK_RST = 0;
   assign WE = 0;
   assign size = SIZE_OUT[11:0];
   assign addr = DISK_A_OUT;
   assign EN = ENABLE_OUT[0];
   
   reg [32767:0] 			    data_buf;

   always
	      @(posedge EN)
     begin
	#(950)
	data_buf = data_out;
	MOD_EN = 1;
     end

   always
	  @(posedge DONE)
     begin
	if(interrupt)
	  begin
	     #5
	     MOD_EN = 0;
	     interrupt = 0;
	  end
		
	if(SIZE_OUT === 0)
	  begin
	     #200
	    interrupt = 1;
	  end
	
	#(26)
	data_buf  =  data_buf >> 128;
     end
   
      
   
   //TRISTATE BUFFERS FOR THE BUS
   wire [31:0] 			    D_TRI_IN;
   assign D_TRI_IN = data_buf[31:0];
   tristate_bus_driver32$ D_TRI(D_TRI_EN, D_TRI_IN, D);
   
    wire 		    A_TRI_EN;
   assign A_TRI_EN = CTRL_TRI_EN;
   wire [15:0] 		    MOD_A;
   assign MOD_A = MEM_A_OUT[15:0];
   tristate_bus_driver16$ A_TRI(A_TRI_EN, MOD_A, A);
   

   wire [11:0] 		    SIZE_TRI_IN;
   assign SIZE_TRI_IN = 12'h0004; //Always sending 16 bytes on the bus
   //at a single time
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
   assign RW_TRI_IN = 1'b1;//the DMA always writes
   assign ACK_TRI_IN = 1'b1;
   tristate_bus_driver1$ RW_TRI(RW_TRI_EN, RW_TRI_IN, RW);
   //tristate_bus_driver1$ ACK_TRI(ACK_TRI_EN, ACK_TRI_IN, ACK);
   
   //Driving the dest out logic
   //TODO: drive this with real values
   and2$ DEST_MEM_DRIVER(DEST_MEM, DEST_OUT, ~interrupt);
   and2$ DEST_INTR_DRIVER(DEST_INTR, DEST_OUT, interrupt);
      

endmodule // DMA_bus_controller



