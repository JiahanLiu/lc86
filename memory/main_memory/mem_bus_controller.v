
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
			  output [14:0] ADDR,
			  output MEM_WR, MEM_EN,
			  output [2:0] WRITE_SIZE,
			  inout [255:0] MEM_INOUT
		      );

   //TODO: logic for selecting which buffer to write too
   //TODO: logic for done is more complex
   //TODO: logic for initiating a write after read
   //TODO: registers for saving address and size for each source



   
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
   gen_ctrl_bus gen_ctrl_bus_u(current_state, CTRL_TRI_EN, D_TRI_EN, ACK_TRI_EN, BR_EN, SIZE_DECR, RD_BUS_CTRL);
   wire 		    DONE;
   ctrler_gen_n_state ctrler_gen_n_state_u(next_state, current_state, MOD_EN, BG, ACK_IN, RW, DEST_IN, DONE);
   wire [2:0] 		    amnt_decr;
   wire [15:0] 		    current_size, current_size_in, next_size;
   assign next_size[15:12] = 0;
   size_decrement size_decrement_u(next_size[11:0], amnt_decr, DONE, current_size[11:0], A);


   //REGISTERS FOR THE CONTROLLER
   //SIZE REGISTER: muxed between the decremented value or 16
   mux2_16$ mux_size_u(current_size_in, 16'h0010, next_size, SIZE_DECR);
   ioreg16$ size_reg(BUS_CLK, current_size_in, current_size, , RST, SET);

   //DATA BUFFERS
   
   //WRITE DATA BUFFER
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
   ioreg128$ write_data_buffer(BUS_CLK, data_buffer_in, data_buffer_out, , RST, SET);
   assign MOD_READ_DATA = data_buffer_out;
   
   //READ DATA BUFFER
   wire [127:0] 		    rd_data_buffer_in, rd_data_buffer_out;
   //READ BUFFER CAN TAKE LOW OF HIGH HALVE OF MEM_INOUT
   //OR STAY THE SAME
   mux4_128 rd_buf_sel(rd_data_buffer_in, rd_data_buffer_out, rd_data_buffer_out, MEM_INOUT[127:0], MEM_INOUT[127:0], RD_BUF_EN, rd_address[5]);
   ioreg128$ read_data_buffer(BUS_CLK, rd_data_buffer_in, rd_data_buffer_out, , RST, SET);
   


   //DONE BUFFER FOR MAIN UNIT
   wire [7:0] 			    MOD_DONE_IN, MOD_DONE_OUT;
   mux2_8$ READY_SEL(MOD_DONE_IN, 8'b0, 8'HFF, DONE);
   assign 		       MOD_R = MOD_DONE_OUT[0];
   ioreg8$ READY_REG(BUS_CLK, MOD_DONE_IN, MOD_DONE_OUT, , RST, SET);

      
   //TRISTATE BUFFERS FOR THE BUS
   wire [31:0] 			    D_TRI_IN;
   mux4_32 D_DRIV_SEL(D_TRI_IN, MOD_WRITE_DATA[31:0], MOD_WRITE_DATA[63:32],
	    MOD_WRITE_DATA[95:64], MOD_WRITE_DATA[127:96],
	    next_size_bar[0], next_size_bar[1]);
   tristate_bus_driver32$ D_TRI(D_TRI_EN, D_TRI_IN, D);
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
   assign RW_TRI_IN = 1'b1;//MEMORY NEVER INITIATES A READ
   assign ACK_TRI_IN = 1'b1;
   tristate_bus_driver1$ RW_TRI(RW_TRI_EN, RW_TRI_IN, RW);
   tristate_bus_driver1$ ACK_TRI(ACK_TRI_EN, ACK_TRI_IN, ACK);
   

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

shiftleft u_shifterleft1 (BUF_OUT[127:0], Q_OUT[127:0], shift_amount);
shiftleft u_shifterleft2 (BUF_OUT[255:128], Q_OUT[255:128], shift_amount);

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