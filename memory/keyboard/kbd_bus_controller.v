
//I believe this works
//Cache bus controller closely follows the template
module kbd_bus_controller(//interface with bus
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
		      output DEST_OUT,//wire goes directly to RAM
		      input DEST_IN
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
   or3$ UPD_EN_DRIVER(UPD_EN, current_state[2], current_state[3], current_state[5]);

   //TODO: switch to behavioral for interrupt test case
   reg 		    MOD_EN;

   initial
     begin
	MOD_EN = 0;
	#(1003)
	MOD_EN = 0;//set to 1 for the keyboard test case
	#(30)
	MOD_EN = 0;
     end

   ctrler_gen_n_state ctrler_gen_n_state_u(next_state, current_state, MOD_EN, BG, ACK_IN, RW, DEST_IN, DONE);
   wire [2:0] 		    amnt_decr;
   wire [15:0] 		    current_size, current_size_in, next_size;
   assign next_size[15:12] = 0;
   size_decrement size_decrement_u(next_size[11:0], amnt_decr, DONE, current_size[11:0], A);


   //REGISTERS FOR THE CONTROLLER
   //SIZE REGISTER: muxed between the decremented value or 16
   mux2_16$ mux_size_u(current_size_in, 16'h0004, next_size, SIZE_DECR);
   ioreg16$ size_reg(BUS_CLK, current_size_in, current_size, , RST, SET);

   //DATA BUFFER
   //NOT NEEDED FOR THE KEYBOARD

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

   //DONE BUFFER FOR MAIN UNIT
   wire [6:0] 			    filler1;
   ioreg8$ READY_REG(BUS_CLK, {7'b0, DONE}, {filler1,MOD_R}, , RST, SET);
   
      
   //TRISTATE BUFFERS FOR THE BUS
   wire [31:0] 			    D_TRI_IN;
   //TODO: drive this with an ascii characher
   assign D_TR_IN = 32'hFEEDBEEF;
   tristate_bus_driver32$ D_TRI(D_TRI_EN, D_TRI_IN, D);
   
    wire 		    A_TRI_EN;
   assign A_TRI_EN = CTRL_TRI_EN;
   wire [15:0] 		    MOD_A;
   assign MOD_A = 0;
   //NOT SURE WHAT TO DO WITH THE ADDRESS WHEN TALKING TO INTERRUPT
   tristate_bus_driver16$ A_TRI(A_TRI_EN, MOD_A, A);
   

   wire [11:0] 		    SIZE_TRI_IN;
   assign SIZE_TRI_IN = 12'h010; //Always sending 16 bytes on the bus
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
   assign RW_TRI_IN = 1'b1;
   assign ACK_TRI_IN = 1'b1;
   tristate_bus_driver1$ RW_TRI(RW_TRI_EN, RW_TRI_IN, RW);
   //tristate_bus_driver1$ ACK_TRI(ACK_TRI_EN, ACK_TRI_IN, ACK);
   

endmodule // bus_controller


