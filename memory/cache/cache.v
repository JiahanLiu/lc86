module cache( //interface with the processor
    input CLK, SET, RST,
    input [127:0] data_write,
    input RW,
    input enable,
    input [15:0] addr,
    input [3:0] size,
    output [127:0] data_read_out,
    output ready,

    output BUS_WR,
    output BUS_EN,
    output [15:0] BUS_ADDR,
    output [127:0] BUS_WRITE,
    input BUS_R,
    input [127:0] BUS_READ
);

    wire [15:0] addr1, addr2, addr3, addr4, address;
    bufferH1024$ buf1 [15:0] (addr1, addr);
    bufferH1024$ buf2 [15:0] (addr2, addr1);
    bufferH1024$ buf3 [15:0] (addr3, addr2);
    bufferH1024$ buf4 [15:0] (addr4, addr3);
    bufferH1024$ buf5 [15:0] (address, addr4);
   //STATE MACHINE ENCODING 00000000
   parameter IDLE  = 16'b0000_0000_0000_0001,
	       RD = 16'b0000_0000_0000_0010,
	       RDHIT = 16'b0000_0000_0000_0100,
	       RDMISS = 16'b0000_0000_0000_1000,
	       RDEVICT = 16'b0000_0000_0001_0000,
	       WR = 16'b0000_0000_0010_0000,
	       WRHIT = 16'b0000_0000_0100_0000,
	       WRMISS = 16'b0000_0000_1000_0000,
	       WREVICT = 16'b0000_0001_0000_0000;
   wire [15:0] 	     current_state, next_state;
   dff16$ state (CLK, next_state, current_state, , RST, SET);
   
   //GENERATING NEXT STATE SIGNAL
   wire 	     evict;
   gen_n_state gen_n_state_u(next_state, current_state, enable, RW, HIT,
			     BUS_R, evict);
   

   
   //GENERATING CONTROL SIGNALS BASED ON STATE
   wire 	     OE, CACHE_WR, TS_WR, d_mux;
   gen_ctrl gen_ctrl_u(current_state, OE, CACHE_WR, BUS_WR, BUS_EN, TS_WR, ready, d_mux);
   
   wire [127:0] data_read;

   //ACCESSING THE DATA LINE
   wire [15:0] 	     DC_WR;
   wire [127:0] out1b, out2b;
   write_masker write_masker_u(DC_WR, CACHE_WR, size, address[3:0]);

   wire [127:0]      data_write_shifted, data_read_shifted, dcache_input, dcache_input_t;
   shiftleft leftshifter_u(data_write_shifted, data_write, address[3:0]);
   mux4_128 data_sel(dcache_input_t, data_write_shifted, data_write_shifted, BUS_READ, BUS_READ, d_mux, d_mux);
   bufferH256$ buf1d [127:0] (out1b, dcache_input_t);
   bufferH16$ buf2d [127:0] (out2b, out1b);
   bufferH16$ buf3d [127:0] (dcache_input, out2b);

   assign data_read_out = data_read_shifted;

   wire [15:0] 	     dcache_wrmask_input;
   mux2_16$ mask_sel(dcache_wrmask_input, DC_WR, 16'h0000, d_mux);
      //accessing the datacache
   full_cache_d data_u (address[8:4], //bits 8 to 4 in the phys address
		     dcache_input,
		     OE,
		     dcache_wrmask_input,
		     data_read);
   shiftright rightshifter_u(data_read_shifted, data_read, address[3:0]);


   //ACCESSING THE TAGSTORE
   wire 	     tagstore_V, tagstore_D;
   wire [6:0] 	     tagstore_tag;
   wire 	     valid = 1;//I don't see any situation to invalidate a cache line
   wire 	     TS_WR_INV;
   inv1$ TS_INVER(TS_WR_INV, TS_WR);
   full_tagstore tagstore_u (address[8:4],
		      valid,
			    RW ,//the line is dirty if we are writing to the line
		      address[15:9],
			     TS_WR,//if we are not writing to TAG store, then read
			     TS_WR_INV,
		      CLK, RST, SET,//used for the valid bits
		      {tagstore_V, tagstore_D,tagstore_tag});

   //CHECKING FOR A HIT
   wire 	     MATCH;
   wire 	     INVALID = 1'b0;
   equalitycheck equalitycheck_u(MATCH, tagstore_tag, address[15:9]);
   mux2$ mux_hit(HIT, INVALID, MATCH, tagstore_V);
   
   //CHECKING FOR AN EVICT
   wire 	     MATCH_INV;
   inv1$ MATCH_INVER(MATCH_INV, MATCH);
   mux2$ mux_evict(evict, INVALID, MATCH_INV, tagstore_V);
   
   
   


   //DRIVING THE BUS WIRES
   assign BUS_ADDR = {address[15:4], 4'b0000};
   assign BUS_WRITE = data_read;
endmodule

//each cacheline is 128 bits (16 cells)
//each byte can individually be written to
module eight_cachelines_d (input [2:0] A,
			   input [127:0] DIN,
			   input OE,
			   input [15:0] WR,
			   output [127:0] DOUT);
//genvar i;
//generate
//   for(i=0;i<15;i=i+1)
//   begin : cachebyte
//   //Allowed since i is constant when the loop is unrolled
//         ram8b8w$ small_dline(A,//corresponds to bits [6:4] in phys address
//			  DIN[(i+1)*8-1:i*8],//which byte on the line?
//			  OE,
//			  WR[i],//each line can be writtern on its own
//			  DOUT[(i+1)*8-1:i*8]);//which byte on the line?
//   end
//endgenerate
    ram8b8w$ ram0 (A, DIN[7:0], OE, WR[0], DOUT[7:0]);
    ram8b8w$ ram1 (A, DIN[15:8], OE, WR[1], DOUT[15:8]);
    ram8b8w$ ram2 (A, DIN[23:16], OE, WR[2], DOUT[23:16]);
    ram8b8w$ ram3 (A, DIN[31:24], OE, WR[3], DOUT[31:24]);
    ram8b8w$ ram4 (A, DIN[39:32], OE, WR[4], DOUT[39:32]);
    ram8b8w$ ram5 (A, DIN[47:40], OE, WR[5], DOUT[47:40]);
    ram8b8w$ ram6 (A, DIN[55:48], OE, WR[6], DOUT[55:48]);
    ram8b8w$ ram7 (A, DIN[63:56], OE, WR[7], DOUT[63:56]);
    ram8b8w$ ram8 (A, DIN[71:64], OE, WR[8], DOUT[71:64]);
    ram8b8w$ ram9 (A, DIN[79:72], OE, WR[9], DOUT[79:72]);
    ram8b8w$ ram10 (A, DIN[87:80], OE, WR[10], DOUT[87:80]);
    ram8b8w$ ram11 (A, DIN[95:88], OE, WR[11], DOUT[95:88]);
    ram8b8w$ ram12 (A, DIN[103:96], OE, WR[12], DOUT[103:96]);
    ram8b8w$ ram13 (A, DIN[111:104], OE, WR[13], DOUT[111:104]);
    ram8b8w$ ram14 (A, DIN[119:112], OE, WR[14], DOUT[119:112]);
    ram8b8w$ ram15 (A, DIN[127:120], OE, WR[15], DOUT[127:120]);
endmodule // eight_cachelines_d


module full_cache_d (input [4:0] A, //bits 8 to 4 in the phys address
    input [127:0] DIN,//data to write to the cacheline
    input OE,
    input [15:0] WR,
    output [127:0] DOUT
);

    wire [127:0] DOUT_ARRAY [3:0];
    wire [127:0] DOUT_ARRAY0, DOUT_ARRAY1, DOUT_ARRAY2, DOUT_ARRAY3;

    // Assign because arrays are not visible in waveforms
    assign DOUT_ARRAY0 = DOUT_ARRAY[0];
    assign DOUT_ARRAY1 = DOUT_ARRAY[1];
    assign DOUT_ARRAY2 = DOUT_ARRAY[2];
    assign DOUT_ARRAY3 = DOUT_ARRAY[3];

   //decoding the address
   wire [3:0] 	a_dec, a_dec_inv;
   decoder2_4$ A_dec(A[4:3], a_dec, );
   inv1$ a_dec_inv_u[3:0](a_dec_inv, a_dec);
   wire [15:0] 	wr0,wr1,wr2,wr3;
   or2$ wr_mask0[15:0](wr0, WR, a_dec_inv[0]);
   or2$ wr_mask1[15:0](wr1, WR, a_dec_inv[1]);
   or2$ wr_mask2[15:0](wr2, WR, a_dec_inv[2]);
   or2$ wr_mask3[15:0](wr3, WR, a_dec_inv[3]);
   

   
    eight_cachelines_d data_line0 (A[2:0], DIN, 1'b0, wr0, DOUT_ARRAY[0]);
    eight_cachelines_d data_line1 (A[2:0], DIN, 1'b0, wr1, DOUT_ARRAY[1]);
    eight_cachelines_d data_line2 (A[2:0], DIN, 1'b0, wr2, DOUT_ARRAY[2]);
    eight_cachelines_d data_line3 (A[2:0], DIN, 1'b0, wr3, DOUT_ARRAY[3]);

    //need to select between the four possible d_cache lines
    mux4_128 dout_mux (DOUT,DOUT_ARRAY[0],DOUT_ARRAY[1],DOUT_ARRAY[2],DOUT_ARRAY[3],A[3],A[4]);

endmodule // full_cache_d

module full_tagstore (input [4:0] A,
    input valid,
    input dirty,
    input [6:0] tag,
    input OE,
    input WR,
    input CLK, CLR, PRE,//used for the valid bits
    output [8:0] DOUT
);

    wire [7:0] ram_outs [3:0];
    wire [7:0] ram_outs0, ram_outs1, ram_outs2, ram_outs3;
    wire out1r, out2r, out3r, out4r, out5r, out6r, out7r, out8r;
    wire out9r, out10r, out11r;
    wire [31:0] s_valid;

    assign ram_outs0 = ram_outs[0];
    assign ram_outs1 = ram_outs[1];
    assign ram_outs2 = ram_outs[2];
    assign ram_outs3 = ram_outs[3];

   //decoder for the rams
   wire [3:0] 	a_dec, a_dec_inv, a_wr_dec;
   decoder2_4$ A_dec(A[4:3], a_dec, );
   inv1$ a_dec_inv_u[3:0](a_dec_inv, a_dec);
   or2$ write_gen[3:0](a_wr_dec, a_dec_inv, WR);
      
    ram8b8w$ u_tag_ram0 (A[2:0], {dirty,tag}, OE, a_wr_dec[0], ram_outs[0]);
    ram8b8w$ u_tag_ram1 (A[2:0], {dirty,tag}, OE, a_wr_dec[1], ram_outs[1]);
    ram8b8w$ u_tag_ram2 (A[2:0], {dirty,tag}, OE, a_wr_dec[2], ram_outs[2]);
    ram8b8w$ u_tag_ram3 (A[2:0], {dirty,tag}, OE, a_wr_dec[3], ram_outs[3]);

    mux4_8$ dout_mux (DOUT[7:0],ram_outs[0],ram_outs[1],ram_outs[2],ram_outs[3],A[3],A[4]);

   //the valid bit is seperate for convenience
   wire [31:0] valid_in, valid_out, valid_mask;//the current state of the valid bits
   decoder5to32 u_decoder5to32 (valid_mask, A);
   
   or32_2way masker (valid_in, valid_out, valid_mask);
   wire WR_bar;//WR is active low, but registers are active high
   inv1$ WR_INV(WR_bar, WR);
   reg32e$ valid_store(CLK, valid_in, valid_out, , CLR, PRE,WR_bar);

   // modified for assigning valid signal - Apurv
   and2$ and_v[31:0] (s_valid, valid_out, valid_mask);
   or4$ or1 (out1r, s_valid[0], s_valid[1], s_valid[2], s_valid[3]);
   or4$ or2 (out2r, s_valid[4], s_valid[5], s_valid[6], s_valid[7]);
   or4$ or3 (out3r, s_valid[8], s_valid[9], s_valid[10], s_valid[11]);
   or4$ or4 (out4r, s_valid[12], s_valid[13], s_valid[14], s_valid[15]);
   or4$ or5 (out5r, s_valid[16], s_valid[17], s_valid[18], s_valid[19]);
   or4$ or6 (out6r, s_valid[20], s_valid[21], s_valid[22], s_valid[23]);
   or4$ or7 (out7r, s_valid[24], s_valid[25], s_valid[26], s_valid[27]);
   or4$ or8 (out8r, s_valid[28], s_valid[29], s_valid[30], s_valid[31]);
   or4$ or9 (out9r, out1r, out2r, out3r, out4r);
   or4$ or10 (out10r, out5r, out6r, out7r, out8r);
   or2$ or11 (out11r, out9r, out10r);

   assign DOUT[8] = out11r;
   // assign DOUT[8] = 0;
   // Apurv 

       
   
endmodule // full_tagstore


module equalitycheck(
	output HIT,
	input [6:0] A,
	input [6:0] B
	);

	equalitycheck7 u_equalitycheck7 (HIT, A, B);

endmodule // equalitycheck


module gen_n_state(
	output [15:0] next_state,
	input [15:0] current_state,
	input enable, 
	input RW, 
	input HIT, 
	input BUS_R,
	input EV
	);
   assign next_state[15:9] = 8'b0000_0000;
   
	wire enable_not, RW_not, HIT_not, BUS_R_not, EV_not;

	inv1$ u_not_enable_en(enable_not, enable);	
	inv1$ u_not_enable_RW(RW_not, RW);	
	inv1$ u_not_enable_HIT(HIT_not, HIT);	
	inv1$ u_not_enable_BUSR(BUS_R_not, BUS_R);	
	inv1$ u_not_enable_EV(EV_not, EV);
	
	wire s0_ENnot; //0
	wire s1_HIT, s3_BUSR; //2
	wire s1_HITnot_EVnot, s4_BUSR, s3_BUSRnot; //3
	wire s1_HITnot_EV, s4_BUSRnot; //4
	wire s5_HIT, s7_BUSR; //6
	wire s5_HITnot_EVnot, s7_BUSRnot, s8_BUSR; //7
	wire s5_HITnot_EV, s8_BUSRnot;  //8

	and2$ u_s0_ENnot(s0_ENnot, current_state[0], enable_not); //0
	and2$ u_s1_HIT(s1_HIT, current_state[1], HIT);
	and2$ u_s3_BUSR(s3_BUSR, current_state[3], BUS_R); //2
	and3$ u_s1_HITnot_EVnot(s1_HITnot_EVnot, current_state[1], HIT_not, EV_not);
	and2$ u_s4_BUSR(s4_BUSR, current_state[4], BUS_R);
	and2$ u_s3_BUSRnot(s3_BUSRnot, current_state[3], BUS_R_not); //3
	and3$ u_s1_HITnot_EV(s1_HITnot_EV, current_state[1], HIT_not, EV);
	and2$ u_s4_BUSRnot(s4_BUSRnot, current_state[4], BUS_R_not); //4
	and2$ u_s5_HIT(s5_HIT, current_state[5], HIT);
	and2$ u_s7_BUSR(s7_BUSR, current_state[7], BUS_R); //6
	and3$ u_s5_HITnot_EVnot(s5_HITnot_EVnot, current_state[5], HIT_not, EV_not);
	and2$ u_s7_BUSRnot(s7_BUSRnot, current_state[7], BUS_R_not);
	and2$ u_s8_BUSR(s8_BUSR, current_state[8], BUS_R); //7
	and3$ u_s5_HITnot_EV(s5_HITnot_EV, current_state[5], HIT_not, EV);
	and2$ u_s8_BUSRnot(s8_BUSRnot, current_state[8], BUS_R_not);

	or3$ u_s0(next_state0_1, current_state[6], current_state[2], s0_ENnot);
	and3$ u_s1(next_state[1], current_state[0], enable, RW_not); 
	or2$ u_s2(next_state[2], s1_HIT, s3_BUSR);
	or3$ u_s3(next_state[3], s1_HITnot_EVnot, s4_BUSR, s3_BUSRnot);
	or2$ u_s4(next_state[4], s1_HITnot_EV, s4_BUSRnot);
	and3$ u_s5(next_state[5], current_state[0], enable, RW);
	or2$ u_s6(next_state[6], s5_HIT, s7_BUSR);
	or3$ u_s7(next_state[7], s5_HITnot_EVnot, s7_BUSRnot, s8_BUSR);
	or2$ u_s8(next_state[8], s5_HITnot_EV, s8_BUSRnot);

   wire      temp_or;
   or1_6way any_state (temp_or,  next_state[6], next_state[7], next_state[8],
		       next_state[5], next_state[4], next_state[3]);
   nor3$ any_state_again(next_state0_2, temp_or, next_state[2], next_state[1]);
   or2$ u_s0_mask(next_state[0], next_state0_1, next_state0_2);
   
   

endmodule // gen_n_state

//D_MUX=0 for sourcing from processor
//D_MUX=1 for sourcing from bus
//   parameter IDLE  = 16'b0000_0000_0000_0001,
//	       RD = 16'b0000_0000_0000_0010,
//	       RDHIT = 16'b0000_0000_0000_0100,
//	       RDMISS = 16'b0000_0000_0000_1000,
//	       RDEVICT = 16'b0000_0000_0001_0000,
//	       WR = 16'b0000_0000_0010_0000,
//	       WRHIT = 16'b0000_0000_0100_0000,
//	       WRMISS = 16'b0000_0000_1000_0000,
//	       WREVICT = 16'b0000_0001_0000_0000;
module  gen_ctrl(input [15:0] current_state,
		  output OE, D_WR, BUS_WR, BUS_EN, TS_WR, R, D_MUX);
   wire IDLE = current_state[0];
   wire RD = current_state[1];
   wire RDHIT = current_state[2];
   wire   RDMISS = current_state[3];
   wire RDEVICT = current_state[4];
   wire WR = current_state[5];
   wire WRHIT = current_state[6];
   wire WRMISS = current_state[7];
   wire WREVICT = current_state[8];

   nor3$ OE_ctrl(OE, RDHIT, WREVICT, RDEVICT);
 
   or3$ WR_or(D_WR, RDMISS, WRHIT, WRMISS);
   or2$ bus_wr_out(BUS_WR, RDEVICT, WREVICT);
   or4$ bus_en_out(BUS_EN, RDMISS, RDEVICT, WRMISS, WREVICT);
   or2$ ts_wr_out(TS_WR, RDHIT, WRHIT);
   or2$ ready_out(R, RDHIT, WRHIT);
   or2$ dmux_out(D_MUX, RDMISS, WRMISS);
   
   
endmodule // gen_ctrl


//we assume that the size is a power of 2
//so 1, 2, 4, 8, or 16
module  write_masker(output [15:0] DC_WR,
		     input CACHE_WR,
		     input [3:0] size,
		     input [3:0] address);
   wire 		[15:0]	 nowrite = 0;
   wire [15:0] 			 allwrite = 16'hFFFF;
   wire [15:0] 			 mask;
   //mask will be 0001, 0003, 0007, 007F, or FFFF
   assign mask[0] = 1;
   or4$ i1(mask[1], size[1], size[2], size[3],1'b0);
   or2$ i2(mask[2], size[2], size[3]);
   assign mask[3] = mask[2];
   assign mask[4] = size[3];
   assign mask[5] = mask[4];
   assign mask[6] = mask[4];
   assign mask[7] = mask[4];
   assign mask[15:8] = 8'b00000000;
   wire [15:0] 			 shifted_mask;
   shifter16bit u_shifter16bit (shifted_mask, mask, address);
   wire [15:0] 			 complete_mask;
   wire 			 size_full;
   nor4$ and_u(size_full, size[3], size[2], size[1], size[0]);
   mux2_16$ mux2_u(complete_mask, shifted_mask, allwrite, size_full);
   wire [15:0] 			 DC_WR_REG;
//   mux2_16$ mux2_u2(DC_WR_REG, nowrite, complete_mask, CACHE_WR);
   and2$ clearing [15:0] (DC_WR_REG, complete_mask, CACHE_WR);
   not16_1way not_u(DC_WR, DC_WR_REG);

   
   
   
/* BAD INITIAL attempt   
   wire [31:0] 			 decoder_out;
   decoder5to32(decoder_out, {1'b0,address});
   wire 	[15:0]		 spot = decoder_out[15:0];

   
   wire [15:0] 			 out2, out4, out8;
 bad implementation
   genvar i;
   generate
      for(i=3;i<7;i=i+1)
	begin : shifter
	   //Allowed since i is constant when the loop is unrolled
	   or2$(out2[i], spot[i], spot[i-1]);
	   or4$(out4[i], spot[i], spot[i-1], spot[i-2], spot[i-3]);
	   
	end

      for(i=7;i<16;i=i+1)
	begin : shifter
	   //Allowed since i is constant when the loop is unrolled
	   or2$(out2[i], spot[i], spot[i-1]);
	   or4$(out4[i], spot[i], spot[i-1], spot[i-2], spot[i-3]);
	   or1_6way(out8[i], out4[i], spot[i-4], spot[i-5], spot[i-6],spot[i-7],1'b0);
	end
   endgenerate*/


   

endmodule // write_masker

module shifter16bit(
    output [15:0] shifted_mask,
    input [15:0] Din,
    input [3:0] amnt
);

    wire [15:0] array [15:0];
    wire [15:0] mux_array[3:0];
    wire [15:0] zero = 16'b0000000000000000;
       
    //genvar i;
    //generate
    //for(i=2;i<16;i=i+1)
    //  begin : shifter
    //  //Allowed since i is constant when the loop is unrolled
    //  assign array[i] = {Din[15-i:0], zero[i-1:0]};
    //  end
    //    endgenerate

    assign array[2] = {Din[13:0], zero[1:0]};
    assign array[3] = {Din[12:0], zero[2:0]};
    assign array[4] = {Din[11:0], zero[3:0]};
    assign array[5] = {Din[10:0], zero[4:0]};
    assign array[6] = {Din[9:0], zero[5:0]};
    assign array[7] = {Din[8:0], zero[6:0]};
    assign array[8] = {Din[7:0], zero[7:0]};
    assign array[9] = {Din[6:0], zero[8:0]};
    assign array[10] = {Din[5:0], zero[9:0]};
    assign array[11] = {Din[4:0], zero[10:0]};
    assign array[12] = {Din[3:0], zero[11:0]};
    assign array[13] = {Din[2:0], zero[12:0]};
    assign array[14] = {Din[1:0], zero[13:0]};
    assign array[15] = {Din[0], zero[14:0]};
        
    assign array[0] = Din;
    assign array[1] = {Din[14:0],zero[0]};
       
    //muxes to select shifted value, first round of muxes
    mux4_16$ mux1 (mux_array[0],array[0],array[1],array[2],array[3],amnt[0],amnt[1]);
    mux4_16$ mux2 (mux_array[1],array[4],array[5],array[6],array[7],amnt[0],amnt[1]);
    mux4_16$ mux3 (mux_array[2],array[8],array[9],array[10],array[11],amnt[0],amnt[1]);
    mux4_16$ mux4 (mux_array[3],array[12],array[13],array[14],array[15],amnt[0],amnt[1]);

    //last round of muxes
    mux4_16$ mux5 (shifted_mask,mux_array[0],mux_array[1],mux_array[2],mux_array[3],amnt[2],amnt[3]);
       

endmodule // shifter16bit




module shiftleft(
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

module shiftright(
    output [127:0] Dout,
    input [127:0] Din,
    input [3:0] amnt
);


//wire [127:0] array [15:0];
//wire [127:0] mux_array [3:0];
//   wire [127:0] zero = 0;
//   
//genvar i;
//generate
//for(i=1;i<16;i=i+1)
//  begin : shifter
//  //Allowed since i is constant when the loop is unrolled
//  assign array[i] = {zero[127:i*8], Din[127:127-i*8+1]};
//  end
//    endgenerate
//   assign array[0] = Din;
//   
//
//
////muxes to select shifted value, first round of muxes
//mux4_128$ mux1 (mux_array[0],array[0],array[1],array[2],array[3],amnt[0],amnt[1]);
//mux4_128$ mux2 (mux_array[1],array[4],array[5],array[6],array[7],amnt[0],amnt[1]);
//mux4_128$ mux3 (mux_array[2],array[8],array[9],array[10],array[11],amnt[0],amnt[1]);
//mux4_128$ mux4 (mux_array[3],array[12],array[13],array[14],array[15],amnt[0],amnt[1]);
//
////last round of muxes
//mux4_128$ mux5 (Dout,mux_array[0],mux_array[1],mux_array[2],mux_array[3],amnt[2],amnt[3]);
	
   wire [127:0] ind0, ind1, ind2, ind3, ind4, ind5;

   mux2$
     mux0[127:0] (ind0, Din, {64'b0, {Din[127:64]}}, amnt[3]),
     mux1[127:0] (ind1, ind0, {32'b0, {ind0[127:32]}}, amnt[2]),
     mux2[127:0] (ind2, ind1, {16'b0, {ind1[127:16]}}, amnt[1]),
     mux3[127:0] (ind3, ind2, {8'b0, {ind2[127:8]}}, amnt[0]),
     mux4[127:0] (ind4, ind3, {4'b0, {ind3[127:4]}}, 1'b0),
     mux5[127:0] (ind5, ind4, {2'b0, {ind4[127:2]}}, 1'b0),
     mux6[127:0] (Dout, ind4, {1'b0, {ind5[127:1]}}, 1'b0);


endmodule
