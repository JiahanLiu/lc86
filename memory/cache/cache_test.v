module cache( //interface with the processor
    input CLK, SET, RST,
    input [127:0] data_write,
    input RW,
    input enable,
    input [15:0] address,
    input [3:0] size,
    output [127:0] data_read,
    output ready,

    output BUS_WR,
    output BUS_EN,
    output [15:0] BUS_ADDR,
    output [127:0] BUS_WRITE,
    input BUS_R,
    input [127:0] BUS_READ
);


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
   wire 	     OE, CACHE_WR, TS_WR;
   gen_ctrl gen_ctrl_u(current_state, OE, CACHE_WR, BUS_WR, BUS_EN, TS_WR, ready);
   
   

   //ACCESSING THE DATA LINE
   wire [15:0] 	     DC_WR;
   write_masker write_masker_u(DC_WR, CACHE_WR, size);
  

   wire [127:0]      data_write_shifted, data_read_shifted;
   leftshifter leftshifter_u(data_write_shifted, data_write, address[3:0]);
   //accessing the datacache
   full_cache_d data_u (address[8:4], //bits 8 to 4 in the phys address
		     data_write_shifted,
		     OE,
		     DC_WR,
		     data_read);
   rightshifter rightshifter_u(data_read_shifted, data_read, address[3:0]);


   //ACCESSING THE TAGSTORE
   wire 	     tagstore_WR; //needs to be generated
   wire 	     tagstore_V, tagstore_D;
   wire [6:0] 	     tagstore_tag;
   wire 	     valid = 1;//I don't see any situation to invalidate a cache line
   full_tagstore tagstore_u (address[8:4],
		      valid,
		      RW,//the line is dirty if we are writing to the line
		      address[15:9],
		      OE,
		      tagstore_WR,
		      CLK, RST, SET,//used for the valid bits
		      {tagstore_V, tagstore_D,tagstore_tag});

   //CHECKING FOR A HIT
   equalitycheck equalitycheck_u(HIT, tagstore_tag, address[15:9]);
   



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
       
    //genvar i;
    //generate
    //   for(i=0;i<4;i=i+1)
    //   begin : cache_datalines
    //   //Allowed since i is constant when the loop is unrolled
    //         eight_cachelines_d data_line(A[2:0],//corresponds to bits [6:4] in phys address
    //			  DIN,//no modifications needed
    //			  OE,
    //			  WR,//this signal needs to be gated with a match
    //			  DOUT_ARRAY[i]);//only one DOUT will be needed
    //   end
    //endgenerate

    eight_cachelines_d data_line0 (A[2:0], DIN, OE, WR, DOUT_ARRAY[0]);
    eight_cachelines_d data_line1 (A[2:0], DIN, OE, WR, DOUT_ARRAY[1]);
    eight_cachelines_d data_line2 (A[2:0], DIN, OE, WR, DOUT_ARRAY[2]);
    eight_cachelines_d data_line3 (A[2:0], DIN, OE, WR, DOUT_ARRAY[3]);

    //need to select between the four possible d_cache lines
    mux4_128$ dout_mux (DOUT,DOUT_ARRAY[0],DOUT_ARRAY[1],DOUT_ARRAY[2],DOUT_ARRAY[3],A[3],A[4]);

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

    assign ram_outs0 = ram_outs[0];
    assign ram_outs1 = ram_outs[1];
    assign ram_outs2 = ram_outs[2];
    assign ram_outs3 = ram_outs[3];
       
    //genvar i;
    //generate
    //   for(i=0;i<4;i=i+1)
    //   begin : tagstore
    //   //Allowed since i is constant when the loop is unrolled
    //               ram8b8w$ ram8(A[2:0],//corresponds to bits [6:4] in phys address
    //			  {dirty,tag},
    //			  OE,
    //			  WR,//this needs to be gated
    //			 ram_outs[i]);//output will be muxed 
    //   end
    //endgenerate

    mux4_8$ dout_mux (DOUT[7:0],ram_outs[0],ram_outs[1],ram_outs[2],ram_outs[3],A[3],A[4]);

    //the valid bit is seperate for convenience
    wire [31:0] valid_in, valid_out;//the current state of the valid bits
    wire [31:0] valid_mask = 32'hFFFFFFFF;//TODO: this needs to be a 5:32 decoder
    or32_2way masker (valid_in, valid_out, valid_mask);
    wire WR_bar;//WR is active low, but registers are active high
    inv1$ WR_INV(WR_bar, WR);
    reg32e$ valid_store(CLK, valid_in, valid_out, , CLR, PRE,WR_bar);

    //TODO: need a 32 bit logical or circuit
    assign DOUT[8] = 0;
       
   
endmodule // full_tagstore

//amnt is in terms of bytes.
module  leftshifter(output [127:0] data_write_shifted,
		    input [127:0] data_write,
		    input [3:0] amnt);


endmodule // leftshifter

//amnt is in terms of bytes.
module  rightshifter(output [127:0] data_write_shifted,
		    input [127:0] data_write,
		    input [3:0] amnt);


endmodule // leftshifter



module equalitycheck(
	output HIT,
	input [6:0] A,
	input [6:0] B
	);

	equalitycheck7 u (HIT, A, B);

endmodule // equalitycheck


module gen_n_state(
	output [7:0] next_state,
	input [7:0] current_state,
	input enable, 
	input RW, 
	input HIT, 
	input BUS_R,
	input EV
	);
	
	wire enable_not, RW_not, HIT_not, BUS_R_not, EV_not;

	inv1$ u_not_enable1(enable_not, enable);	
	inv1$ u_not_enable2(RW_not, RW);	
	inv1$ u_not_enable3(HIT_not, HIT);	
	inv1$ u_not_enable4(BUS_R_not, BUS_R);	
	inv1$ u_not_enable5(EV_not, EV);
	
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

	or3$ u_s0(next_state[0], current_state[6], current_state[2], s0_ENnot);
	and3$ u_s1(next_state[1], current_state[0], enable, RW_not); 
	or2$ u_s2(next_state[2], s1_HIT, s3_BUSR);
	or3$ u_s3(next_state[3], s1_HITnot_EVnot, s4_BUSR, s3_BUSRnot);
	or2$ u_s4(next_state[4], s1_HITnot_EV, s4_BUSRnot);
	and3$ u_s5(next_state[5], current_state[0], enable, WR);
	or2$ u_s6(next_state[6], s5_HIT, s7_BUSR);
	or3$ u_s7(next_state[7], s5_HITnot_EVnot, s7_BUSRnot, s8_BUSR);
	or2$ u_s8(next_state[8], s5_HITnot_EV, s8_BUSRnot);	

endmodule // gen_n_state


module   gen_ctrl(input [7:0] current_state,
		  output OE, WR, BUS_WR, BUS_EN, TS_WR, R);

endmodule // gen_ctrl



module  write_masker(output [15:0] DC_WR,
		     input CACHE_WR,
		     input [3:0] size);


endmodule // write_masker
