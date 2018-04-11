`define CS_LIMIT_REGISTER 20'h04fff
`define DS_LIMIT_REGISTER 20'h011ff
`define SS_LIMIT_REGISTER 20'h04000
`define ES_LIMIT_REGISTER 20'h003ff
`define FS_LIMIT_REGISTER 20'h003ff
`define GS_LIMIT_REGISTER 20'h007ff

/*
ES = 000
CS = 001
SS = 010 // no checking for SS
DS = 011
FS = 100
GS  = 101
*/

// first_addr <= seg_limit - (size-1)
module segment_limit_check (
   input V, MEM_RD, MEM_WR,
   input [1:0] CS_MUX_MEM_RD, CS_MUX_MEM_WR,
   input [2:0] SEG1_ID,
   input [1:0] DATA_SIZE,
   input [31:0] ADD_BASE_DISP, MUX_SIB_SI, 

   output EXC
);

   wire [31:0] mux_seg1_out, mux_seg2_out, mux_seg_out;
   wire [31:0] add_sib_si_out, mux_data_size_out, add_limit_out;

   wire or_v_out, mag_comp32_limit_out;
   wire nor_rd_out, nor_wr_out, and_rd_out, and_wr_out;
   
   mux4$
      mux_seg1 [31:0] (mux_seg1_out, {12'h000, `ES_LIMIT_REGISTER}, {12'h000, `CS_LIMIT_REGISTER}, 32'hFFFFFFFF, {12'h000, `DS_LIMIT_REGISTER}, SEG1_ID[0], SEG1_ID[1]),
      mux_seg2 [31:0] (mux_seg2_out, {12'h000, `FS_LIMIT_REGISTER}, {12'h000, `GS_LIMIT_REGISTER}, 32'hFFFFFFFF, 32'hFFFFFFFF, SEG1_ID[0], SEG1_ID[1]);;
   mux2$
      mux_seg [31:0] (mux_seg_out, mux_seg1_out, mux_seg2_out, SEG1_ID[2]);

   // select to subtract 0, 1, 3, 7 from segment limit
   mux4$ mux_data_size [31:0] (mux_data_size_out, 32'h00000000, 32'hFFFFFFFF, 32'hFFFFFFFD, 32'hFFFFFFF9, DATA_SIZE[0], DATA_SIZE[1]);

   adder32_w_carry_in
      add_sib_si (add_sib_si_out, , ADD_BASE_DISP, MUX_SIB_SI, 1'b0),
      add_limit (add_limit_out, , mux_seg_out, mux_data_size_out, 1'b0);
 
   // assume invalid segment register ID not given
   mag_comp32
      mag_comp32_limit (add_sib_si_out, add_limit_out, mag_comp32_limit_out, , );

   nor2$ 
     nor_rd (nor_rd_out, CS_MUX_MEM_RD[0], CS_MUX_MEM_RD[1]),
     nor_wr (nor_wr_out, CS_MUX_MEM_WR[0], CS_MUX_MEM_WR[1]);

   and3$
     and_rd (and_rd_out, V, nor_rd_out, MEM_RD),
     and_wr (and_wr_out, V, nor_wr_out, MEM_WR);
   
   or2$ or_v (or_v_out, and_rd_out, and_wr_out);

   and2$ and_exc (EXC, mag_comp32_limit_out, or_v_out);

endmodule
 
