
//IMPORTANT: This module is the template bus controller
//EACH Memory module has a slightly specialized version of this controller
module mem_bus_controller(//interface with bus
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
		      output DEST_OUT_IC,
		      output DEST_OUT_DC,
		      input DEST_IC,
			  input DEST_DC,
			  input DEST_DMA,
		      //interface with work unit
			  output [14:0] MEM_ADDR,
			  output MEM_WR, MEM_EN,
			  output [2:0] WRITE_SIZE,
			  inout [255:0] MEM_INOUT
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
   //TODO debug Pending BR
   //PENDING BR IS A TIME DELAYED PEND_RD
   wire 		    PENDING_BR;
   wire 		    DEST_IN;
   or3$ any_dest_in(DEST_IN, DEST_IC, DEST_DC, DEST_DMA);
   ctrler_gen_n_state gen_n_state_u(next_state, current_state, PENDING_BR, BG, ACK_IN, RW, DEST_IN, DONE);
   



   //GENERATE CTRL SIGNALS
   gen_ctrl_bus gen_ctrl_bus_u(current_state, CTRL_TRI_EN, D_TRI_EN, ACK_OUT_BAR, BR_STATE, SIZE_DECR, RD_BUS_CTRL);
   //TRI_EN is active low!
   inv1$ DEST_DRIVER (DEST_OUT, CTRL_TRI_EN);
   inv1$ ACK_DRIVER (ACK_OUT, ACK_OUT_BAR);


   wire [2:0] 		    amnt_decr;
   wire [15:0] 		    current_size, current_size_in, next_size;
   assign next_size[15:12] = 0;
   size_decrement size_decrement_u(next_size[11:0], amnt_decr, DONE, current_size[11:0], A);

   //CTRL SIGNALS FOR THE PORT TO MAIN MEMORY
   wire 		    PEND_RD;
   or2$ BR_DRIVER(BR, BR_STATE, PENDING_BR);
   wire 		    LD_WR_LATCHES, LD_RD_LATCHES,
			    CLR_WR_LATCHES, CLR_RD_LATCHES;
   

   ////////////////////////////////
   //REGISTERS FOR THE CONTROLLER//
   ///////////////////////////////
	
   //BUS SIZE REGISTER: muxed between the decremented value or 16
   mux2_16$ mux_size_u(current_size_in, 16'h0010, next_size, SIZE_DECR);
   ioreg16$ size_reg(BUS_CLK, current_size_in, current_size, , RST, SET);
   
   //WRITE DATA BUFFER
   wire [127:0] 		    data_buffer_bus, data_buffer_in, data_buffer_out;
   wire [3:0]			    SIZE_SELECT;
   wire [1:0] 			    next_size_bar;
   wire [3:0] 			    RD_BUS;
   //as size goes down, buffer location goes up
   inv1$ siz_bar_u_0(next_size_bar[0], next_size[2]);
   inv1$ siz_bar_u_1(next_size_bar[1], next_size[3]);
   decoder2_4$ size_decode(next_size_bar, SIZE_SELECT, );
   and2$ rd_0(RD_BUS[0], SIZE_SELECT[0], RD_BUS_CTRL);
   and2$ rd_1(RD_BUS[1], SIZE_SELECT[1], RD_BUS_CTRL);
   and2$ rd_2(RD_BUS[2], SIZE_SELECT[2], RD_BUS_CTRL);
   and2$ rd_3(RD_BUS[3], SIZE_SELECT[3], RD_BUS_CTRL);
   //muxes select between updating reading from bus or staying same
   mux32_2way mux_u_0(data_buffer_in[31:0],data_buffer_out[31:0] , D, RD_BUS[0]);
   mux32_2way mux_u_1(data_buffer_in[63:32],data_buffer_out[63:32] , D, RD_BUS[1]);
   mux32_2way mux_u_2(data_buffer_in[95:64],data_buffer_out[95:64] , D, RD_BUS[2]);
   mux32_2way mux_u_3(data_buffer_in[127:96],data_buffer_out[127:96] , D, RD_BUS[3]);
   ioreg128$ write_data_buffer(BUS_CLK, data_buffer_in, data_buffer_out, , RST, SET);
   
   //READ DATA BUFFER
   wire [127:0] 		    rd_data_buffer_in, rd_data_buffer_out,
				    mem_val, non_mem_val;
   wire [15:0]			    RD_A;
   
   //TODO: debug the PEND_RD signal
   //READ DATA CAN BE UPDATED FROM READING
   //mux2_128 rd_buf_upd(non_mem_val, rd_data_buffer_out, data_buffer_out,
   //LD_RD_LATCHES);
   mux2_128 mem_select(mem_val, MEM_INOUT[127:0], MEM_INOUT[255:128],
		       RD_A[4]);

   mux4_128 rd_buf_sel(rd_data_buffer_in, rd_data_buffer_out, mem_val,
		       data_buffer_out, data_buffer_out,
		       PEND_RD, LD_RD_LATCHES);
   //   mux4_128 rd_buf_sel(rd_data_buffer_in, non_mem_val, non_mem_val,
//		       MEM_INOUT[127:0], MEM_INOUT[255:128],
//		       RD_A[4], PEND_RD);
   //OR FROM THE WRITE LATCHES
   ioreg128$ read_data_buffer(BUS_CLK, rd_data_buffer_in, rd_data_buffer_out, , RST, SET);
   
   //addresses
   wire [15:0] 			    WR_A, WR_A_IN, RD_A_IN;
   wire 			    UPD_WR_A, UPD_RD_A;

   assign UPD_WR_A = LD_WR_LATCHES;
   assign UPD_RD_A = LD_RD_LATCHES;
   
   mux16_2way WR_A_SEL(WR_A_IN, WR_A, A, UPD_WR_A);   
   ioreg16$ WR_ADDRESS(BUS_CLK, WR_A_IN, WR_A, , RST, SET);
   mux16_2way RD_A_SEL(RD_A_IN, RD_A, WR_A, UPD_RD_A);   
   ioreg16$ RD_ADDRESS(BUS_CLK, RD_A_IN, RD_A, , RST, SET);

   

   //source, and valid registers registers
   wire [2:0] 			    WR_SRC, WR_SRC_IN, RD_SRC, RD_SRC_IN;
   wire 			    UPD_WR_SRC, UPD_RD_SRC;
   wire [2:0]			    BUS_SRC;
   wire 			    WR_V_IN, WR_V_OUT, RD_V_IN, RD_V_OUT;
    			    
   assign BUS_SRC = {DEST_DMA, DEST_DC,  DEST_IC};
   assign UPD_WR_SRC = LD_WR_LATCHES;
   assign UPD_RD_SRC = LD_RD_LATCHES;
   mux4$ WR_V_SEL(WR_V_IN, WR_V_OUT, 1'b1, 1'b0, 1'b1,
		  LD_WR_LATCHES, CLR_WR_LATCHES);
   mux4$ RD_V_SEL(RD_V_IN, RD_V_OUT, WR_V_OUT, 1'b0, WR_V_OUT,
		  LD_RD_LATCHES, CLR_RD_LATCHES);
   
   mux2$ WR_SRC_SEL [2:0] (WR_SRC_IN, WR_SRC, BUS_SRC, UPD_WR_SRC);
   mux2$ RD_SRC_SEL [2:0] (RD_SRC_IN, RD_SRC, WR_SRC, UPD_RD_SRC);
   ioreg8$ SRC_REG(BUS_CLK, {WR_SRC_IN, WR_V_IN, RD_V_IN, RD_SRC_IN},
		   {WR_SRC, WR_V_OUT, RD_V_OUT, RD_SRC},, RST, SET);

   //size, reading, and pending_write registers
   wire [2:0] 			    WR_SIZE, WR_SIZE_IN, RD_SIZE, RD_SIZE_IN;
   wire 			    UPD_WR_SIZE, UPD_RD_SIZE;
   wire [2:0]			    BUS_SIZE;
   wire 			    WR_RW_IN, WR_RW_OUT;
   wire  			    RD_RW_IN, RD_RW_OUT;
   wire 			    UPD_WR_RW, UPD_RD_RW;
   assign BUS_SIZE = SIZE[2:0];
   assign UPD_WR_RW = LD_WR_LATCHES;
   assign UPD_RD_RW = LD_RD_LATCHES;
   assign UPD_WR_SIZE = LD_WR_LATCHES;
   assign UPD_RD_SIZE = LD_RD_LATCHES;

   mux2$ WR_RW_SEL (WR_RW_IN, WR_RW_OUT, RW , UPD_WR_RW);
   mux2$ RD_RW_SEL (RD_RW_IN, RD_RW_OUT, WR_RW_OUT, UPD_RD_RW);
   mux2$ WR_SIZE_SEL [2:0] (WR_SIZE_IN, WR_SIZE, BUS_SIZE, UPD_WR_SIZE);
   mux2$ RD_SIZE_SEL [2:0] (RD_SIZE_IN, RD_SIZE, WR_SIZE, UPD_RD_SIZE);
   ioreg8$ SIZE_RD_REG (BUS_CLK,
			{WR_SIZE_IN, WR_RW_IN, RD_RW_IN, RD_SIZE_IN},
			{WR_SIZE, WR_RW_OUT, RD_RW_OUT, RD_SIZE}, , RST, SET);

   
   
   //TIMER FOR MEMORY
   //each clock cycle will increase the number of 1 bits in the done register
   wire [7:0] 			    MEM_DONE_IN, MEM_DONE_OUT;
   wire 			    TIMER_RESET;
   inv1$ RD_V_INV(RD_V_BAR, RD_V_OUT);
   or2$ TIMER_RESET_DRIVER (TIMER_RESET, CLR_RD_LATCHES, RD_V_BAR);
   mux2_8$ MEM_DONE_SEL(MEM_DONE_IN,  {MEM_DONE_OUT[6:0], 1'b1}, 8'b01,TIMER_RESET);
   ioreg8$ MEM_DONE_REG(BUS_CLK, MEM_DONE_IN, MEM_DONE_OUT, , RST, SET);

   //Driving control signals
   inv1$ WR_V_INV(WR_V_BAR, WR_V_OUT);
   inv1$ RD_RD_DRIV(RD_RD, RD_RW_OUT);   
   and2$ NXT_STE_DRIVER(PENDING_BR, MEM_DONE_OUT[4], PEND_RD);
   and3$ PEND_RD_DRIV (PEND_RD, RD_RD, RD_V_OUT, MEM_DONE_OUT[1]);
   and2$ PEND_WR_DRIV (PEND_WR, RD_RW_OUT, RD_V_OUT);

   //We load the WR latches on Ack if a read
   //We load the WR latches on Done if a write
   inv1$ BUS_RW_INV (RW_BAR, RW);
   or2$ WR_LATCHES_OPEN(WR_V_OPEN, WR_V_BAR, CLR_WR_LATCHES);
   
   //STEVEN: removed WR_BAR as 
   and3$ LD_WR_DRIV_RD (LD_WR_LATCHES_RD, WR_V_OPEN,
			ACK_OUT, RW_BAR);
   and3$ LD_WR_DRIV_WR (LD_WR_LATCHES_WR, WR_V_OPEN,
			current_state[5], DONE);
   or2$ LD_WR_DRIV (LD_WR_LATCHES, LD_WR_LATCHES_RD, LD_WR_LATCHES_WR);
//   and2$ LD_WR_DRIV (LD_WR_LATCHES, ACK_OUT, WR_V_BAR);
   assign CLR_WR_LATCHES = LD_RD_LATCHES;
   or2$ RD_EMPTY (RD_EMP, RD_V_BAR, CLR_RD_LATCHES);
   and2$ LD_RD_DRIV (LD_RD_LATCHES, WR_V_OUT, RD_EMP);
   //Clearing RD latches when either a write finishes accessing memory
   //or when we have taken control of the bus (Returning read data)
   and2$ WR_DONE_DRIVER (WR_DONE, PEND_WR, MEM_DONE_OUT[6]);
   and3$ RD_DONE_DRIVER (RD_DONE, PEND_RD, DONE, current_state[3]); //bit two is for master state
   or2$ CLR_RD_DRIVER(CLR_RD_LATCHES, WR_DONE, RD_DONE);
   
   
   //DRIVING THE MAIN MEMORY
   
   wire [127:0] 		    write_data_shifted;
   shiftleft leftshifter_u(write_data_shifted, rd_data_buffer_out, RD_A[3:0]);
   
   tristate_bus_driver32$ IO_LOW [3:0] (RD_RD, write_data_shifted, MEM_INOUT[127:0]);
      tristate_bus_driver32$ IO_HIGH [3:0] (RD_RD, write_data_shifted, MEM_INOUT[255:128]);
   assign MEM_ADDR = RD_A[14:0];
   assign WRITE_SIZE = RD_SIZE;
   and2$ MEM_WR_EN(MEM_WR, MEM_DONE_OUT[2],RD_RW_OUT);
   assign MEM_EN = MEM_DONE_OUT[3];

   
   //DRIVING THE DESTINATION WIRE
   and2$ IC_DEST_DRIVER(DEST_OUT_IC, DEST_OUT, RD_SRC[0] );
   and2$ DC_DEST_DRIVER(DEST_OUT_DC, DEST_OUT, RD_SRC[1] );
   
         
   //TRISTATE BUFFERS FOR THE BUS
   wire [31:0] 			    D_TRI_IN;
   mux4_32 D_DRIV_SEL(D_TRI_IN,
		      rd_data_buffer_in[31:0], rd_data_buffer_in[63:32],
		      rd_data_buffer_in[95:64], rd_data_buffer_in[127:96],
		      next_size_bar[0], next_size_bar[1]);
   tristate_bus_driver32$ D_TRI(D_TRI_EN, D_TRI_IN, D);

   wire 			    A_TRI_EN;
   assign A_TRI_EN = CTRL_TRI_EN;
   tristate_bus_driver16$ A_TRI(A_TRI_EN, RD_A, A);
   
   
   wire [11:0] 		    SIZE_TRI_IN;
   assign SIZE_TRI_IN = 12'h010; //Always sending 16 bytes on the bus
   wire 		    SIZE_TRI_EN;
   assign SIZE_TRI_EN = CTRL_TRI_EN;
   tristate_bus_driver8$ SIZE8_TRI(SIZE_TRI_EN, SIZE_TRI_IN[11:4], SIZE[11:4]);
   tristate_bus_driver1$ SIZE3_TRI(SIZE_TRI_EN, SIZE_TRI_IN[3], SIZE[3]);
   tristate_bus_driver1$ SIZE2_TRI(SIZE_TRI_EN, SIZE_TRI_IN[2], SIZE[2]);
   tristate_bus_driver1$ SIZE1_TRI(SIZE_TRI_EN, SIZE_TRI_IN[1], SIZE[1]);
   tristate_bus_driver1$ SIZE0_TRI(SIZE_TRI_EN, SIZE_TRI_IN[0], SIZE[0]);
   
   wire 		    RW_TRI_IN;
   wire 		    RW_TRI_EN;
   assign RW_TRI_EN = CTRL_TRI_EN;
   assign RW_TRI_IN = 1'b1;//MEMORY NEVER INITIATES A READ
   tristate_bus_driver1$ RW_TRI(RW_TRI_EN, RW_TRI_IN, RW);

   

endmodule // bus_controller



module buffer_io (
    input [127:0] bus_read,
    inout [255:0] ram_out,
    input WR, CLK,
    input CLR, PRE,
    input section_sel,
    input [3:0] shift_amount,
    output [127:0] BUS_OUT
);

// Connect DIO to buffer for write
// Bus is connected to the low 31 bits of the buffer
// While writing to the memory, always read from low 31 bits of buffer
// While reading from memory, fill all 256 bits of buffer
// column_address[5] will determine whether to read from low 128 or high 128

wire [255:0] Q_OUT, DIN;
wire [255:0] BUF_OUT;

mux2_128 mux_out (BUS_OUT, Q_OUT[127:0], Q_OUT[255:128], section_sel);

mux2_128 mux_in1 (DIN[127:0], ram_out[127:0], bus_read[127:0], WR);
mux2_128 mux_in2 (DIN[255:128], ram_out[255:128], bus_read[127:0], WR);
// Low 128
ioreg16$ ioreg0 (CLK, DIN[15:0], Q_OUT[15:0], , CLR, PRE);
ioreg16$ ioreg1 (CLK, DIN[31:16], Q_OUT[31:16], , CLR, PRE);
ioreg16$ ioreg2 (CLK, DIN[47:32], Q_OUT[47:32], , CLR, PRE);
ioreg16$ ioreg3 (CLK, DIN[63:48], Q_OUT[63:48], , CLR, PRE);
ioreg16$ ioreg4 (CLK, DIN[79:64], Q_OUT[79:64], , CLR, PRE);
ioreg16$ ioreg5 (CLK, DIN[95:80], Q_OUT[95:80], , CLR, PRE);
ioreg16$ ioreg6 (CLK, DIN[111:96], Q_OUT[111:96], , CLR, PRE);
ioreg16$ ioreg7 (CLK, DIN[127:112], Q_OUT[127:112], , CLR, PRE);

// High 128
ioreg16$ ioreg8 (CLK, DIN[143:128], Q_OUT[143:128], , CLR, PRE);
ioreg16$ ioreg9 (CLK, DIN[159:144], Q_OUT[159:144], , CLR, PRE);
ioreg16$ ioreg10 (CLK, DIN[175:160], Q_OUT[175:160], , CLR, PRE);
ioreg16$ ioreg11 (CLK, DIN[191:176], Q_OUT[191:176], , CLR, PRE);
ioreg16$ ioreg12 (CLK, DIN[207:192], Q_OUT[207:192], , CLR, PRE);
ioreg16$ ioreg13 (CLK, DIN[223:208], Q_OUT[223:208], , CLR, PRE);
ioreg16$ ioreg14 (CLK, DIN[239:224], Q_OUT[239:224], , CLR, PRE);
ioreg16$ ioreg15 (CLK, DIN[255:240], Q_OUT[255:240], , CLR, PRE);

//shiftleft u_shifterleft1 (BUF_OUT[127:0], Q_OUT[127:0], shift_amount);
//shiftleft u_shifterleft2 (BUF_OUT[255:128], Q_OUT[255:128], shift_amount);

// Connect DIO to buffer for read
// in is buffer out and out is DATA_BUF
inv1$ inv_tri_en (en1_b, WR);

// Low 128
tristate16L$ buf0 (en1_b, BUF_OUT[15:0], ram_out[15:0]);
tristate16L$ buf1 (en1_b, BUF_OUT[31:16], ram_out[31:16]);
tristate16L$ buf2 (en1_b, BUF_OUT[47:32], ram_out[47:32]);
tristate16L$ buf3 (en1_b, BUF_OUT[63:48], ram_out[63:48]);
tristate16L$ buf4 (en1_b, BUF_OUT[79:64], ram_out[79:64]);
tristate16L$ buf5 (en1_b, BUF_OUT[95:80], ram_out[95:80]);
tristate16L$ buf6 (en1_b, BUF_OUT[111:96], ram_out[111:96]);
tristate16L$ buf7 (en1_b, BUF_OUT[127:112], ram_out[127:112]);

// High 128
tristate16L$ buf8 (en1_b, BUF_OUT[143:128], ram_out[143:128]);
tristate16L$ buf9 (en1_b, BUF_OUT[159:144], ram_out[159:144]);
tristate16L$ buf10 (en1_b, BUF_OUT[175:160], ram_out[175:160]);
tristate16L$ buf11 (en1_b, BUF_OUT[191:176], ram_out[191:176]);
tristate16L$ buf12 (en1_b, BUF_OUT[207:192], ram_out[207:192]);
tristate16L$ buf13 (en1_b, BUF_OUT[223:208], ram_out[223:208]);
tristate16L$ buf14 (en1_b, BUF_OUT[239:224], ram_out[239:224]);
tristate16L$ buf15 (en1_b, BUF_OUT[255:240], ram_out[255:240]);


endmodule 


module mem_shiftleft(
    output [127:0] Dout,
    input [127:0] Din,
    input [3:0] amnt

);


wire [127:0] array [15:0];
wire [127:0] mux_array [3:0];
   wire [127:0] zero = 127'h0000_0000_0000_0000;
   
genvar i;
generate
for(i=1;i<16;i=i+1)
  begin : shifter
  //Allowed since i is constant when the loop is unrolled
  assign array[i] = {Din[127-i*8:0], zero[127:127-i*8+1]};
  end
    endgenerate
   assign array[0] = Din;
   
//muxes to select shifted value, first round of muxes
mux4_128 mux1 (mux_array[0],array[0],array[1],array[2],array[3],amnt[0],amnt[1]);
mux4_128 mux2 (mux_array[1],array[4],array[5],array[6],array[7],amnt[0],amnt[1]);
mux4_128 mux3 (mux_array[2],array[8],array[9],array[10],array[11],amnt[0],amnt[1]);
mux4_128 mux4 (mux_array[3],array[12],array[13],array[14],array[15],amnt[0],amnt[1]);

//last round of muxes
mux4_128 mux5 (Dout,mux_array[0],mux_array[1],mux_array[2],mux_array[3],amnt[2],amnt[3]);
	

endmodule
