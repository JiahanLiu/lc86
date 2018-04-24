module TOP;
   reg clk, rst;

`define half_cycle 50
   initial 
     begin
	clk = 1'b0;
	rst = 1'b0;
     end
   
   always #(`half_cycle) clk = ~clk;

   // Run simulation.  
   initial #(`half_cycle*50*2) $finish;

   // Dump all waveforms
   initial
      begin


	 $vcdplusfile("lsu.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin
endmodule

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
genvar i;
generate
   for(i=0;i<15;i=i+1)
   begin : cachebyte
   //Allowed since i is constant when the loop is unrolled
         ram8b8w$ small_dline(A,//corresponds to bits [6:4] in phys address
			  DIN[(i+1)*8-1:i*8],//which byte on the line?
			  OE,
			  WR[i],//each line can be writtern on its own
			  DOUT[(i+1)*8-1:i*8]);//which byte on the line?
   end
endgenerate
endmodule // eight_cachelines_d


module full_cache_d (input [4:0] A, //bits 8 to 4 in the phys address
		     input [127:0] DIN,//data to write to the cacheline
		     input OE,
		     input [15:0] WR,
		     output [127:0] DOUT);
   wire [127:0] 	    DOUT_ARRAY [3:0];
   
genvar i;
generate
   for(i=0;i<4;i=i+1)
   begin : cache_datalines
   //Allowed since i is constant when the loop is unrolled
         eight_cachelines_d data_line(A[2:0],//corresponds to bits [6:4] in phys address
			  DIN,//no modifications needed
			  OE,
			  WR,//this signal needs to be gated with a match
			  DOUT_ARRAY[i]);//only one DOUT will be needed
   end
endgenerate


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
		      output [8:0] DOUT);
   wire [7:0] 			   ram_outs [3:0];
   
genvar i;
generate
   for(i=0;i<4;i=i+1)
   begin : tagstore
   //Allowed since i is constant when the loop is unrolled
               ram8b8w$ ram8(A[2:0],//corresponds to bits [6:4] in phys address
			  {dirty,tag},
			  OE,
			  WR,//this needs to be gated
			 ram_outs[i]);//output will be muxed 
   end
endgenerate

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

module  leftshifter(output [127:0] data_write_shifted,
		    input [127:0] data_write,
		    input [3:0] amnt);


endmodule // leftshifter

module  rightshifter(output [127:0] data_write_shifted,
		    input [127:0] data_write,
		    input [3:0] amnt);


endmodule // leftshifter



module   equalitycheck(output HIT,
		       input [6:0] A,
		       input [6:0] B);



endmodule // equalitycheck


module gen_n_state(
	output [7:0] next_state,
	input [7:0] current_state,
	input enable, 
	input RW, 
	input HIT, 
	input BUS_R
	);
	
	wire enable_not, RW_not, HIT_not, BUS_R_not;

	inv1$ u_not_enable(enable_not, enable);	
	inv1$ u_not_enable(RW_not, RW);	
	inv1$ u_not_enable(HIT_not, HIT);	
	inv1$ u_not_enable(BUS_R_not, BUS_R);	
	
	wire s0_ENnot; //0
	wire s1_HIT, s3_BUSR; //2
	wire s1_HITnot_EVnot, s4_BUSR, s3_BUSRnot; //3
	wire s1_HITnot_EV, s4_BUSRnot; //4
	wire s5_HIT, s7_BUSR; //6
	wire s5_HITnot_EVnot, s7_BUSRnot, s8_BUSR; //7
	wire s5_HITnot_EV, s8_BUSRnot;  //8



endmodule // gen_n_state


module   gen_ctrl(input [7:0] curprent_state,
		  output OE, WR, BUS_WR, BUS_EN, TS_WR, R);

endmodule // gen_ctrl



module  write_masker(output [15:0] DC_WR,
		     input CACHE_WR,
		     input [3:0] size);


endmodule // write_masker
