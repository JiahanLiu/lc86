

//Cache bus controller closely follows the template
module cache_bus_controller(//interface with bus
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
		      input DEST_IN,
		      //interface with work unit
		      //needs to be modifed for each unit
		      input MOD_EN, //simple signal saying we have a request
		      input MOD_WR,
		      input [15:0] MOD_A,
		      input [127:0] MOD_WRITE_DATA,
		      output [127:0] MOD_READ_DATA,
		      output MOD_R

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
   
   mux2$ MASK_SEL(MASK_IN, MOD_MASK_OUT, current_state[2], UPD_EN);   
   ioreg8$ MASK_REG(BUS_CLK, {7'b0,MASK_IN},{filler, MOD_MASK_OUT}, {filler,MOD_EN_MASK},RST,SET);
   and2$ MASKED_MOD_EN(MASKED_EN, MOD_EN_MASK, MOD_EN);
   ctrler_gen_n_state ctrler_gen_n_state_u(next_state, current_state, MASKED_EN, BG, ACK_IN, RW, DEST_IN, DONE);
   wire [2:0] 		    amnt_decr;
   wire [15:0] 		    current_size, current_size_in, next_size;
   assign next_size[15:12] = 0;
   size_decrement size_decrement_u(next_size[11:0], amnt_decr, DONE, current_size[11:0], A);


   //REGISTERS FOR THE CONTROLLER
   //SIZE REGISTER: muxed between the decremented value or 16
   mux2_16$ mux_size_u(current_size_in, 16'h0010, next_size, SIZE_DECR);
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
   
      
   //TRISTATE BUFFERS FOR THE BUS
   wire [31:0] 			    D_TRI_IN;
   mux4_32 D_DRIV_SEL(D_TRI_IN, MOD_WRITE_DATA[31:0], MOD_WRITE_DATA[63:32],
	    MOD_WRITE_DATA[95:64], MOD_WRITE_DATA[127:96],
	    next_size_bar[0], next_size_bar[1]);
   tristate_bus_driver32$ D_TRI(D_TRI_EN, D_TRI_IN, D);



//DEST, ACK, and MASTER IS NO LONGER USED, NOW USING DIRECT CONNECTIONS
/*   wire [2:0] 		    DEST_TRI_IN, MASTER_TRI_IN;
   wire 		    DEST_TRI_EN, MASTER_TRI_EN;
   assign MASTER_TRI_IN = MY_ID;
   assign DEST_TRI_EN = CTRL_TRI_EN;
   assign MASTER_TRI_EN = CTRL_TRI_EN;
   tristate_bus_driver1$ DEST2_TRI(DEST_TRI_EN, DEST_TRI_IN[2], DEST[2]);
   tristate_bus_driver1$ DEST1_TRI(DEST_TRI_EN, DEST_TRI_IN[1], DEST[1]);
   tristate_bus_driver1$ DEST0_TRI(DEST_TRI_EN, DEST_TRI_IN[0], DEST[0]);
   tristate_bus_driver1$ MAS2_TRI(MASTER_TRI_EN, MASTER_TRI_IN[2], MASTER[2]);
   tristate_bus_driver1$ MAS1_TRI(MASTER_TRI_EN, MASTER_TRI_IN[1], MASTER[1]);
   tristate_bus_driver1$ MAS0_TRI(MASTER_TRI_EN, MASTER_TRI_IN[0], MASTER[0]);*/
   
    wire 		    A_TRI_EN;
   assign A_TRI_EN = CTRL_TRI_EN;
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
   assign RW_TRI_IN = MOD_WR;
   assign ACK_TRI_IN = 1'b1;
   tristate_bus_driver1$ RW_TRI(RW_TRI_EN, RW_TRI_IN, RW);
   //tristate_bus_driver1$ ACK_TRI(ACK_TRI_EN, ACK_TRI_IN, ACK);
   

endmodule // bus_controller


