`define CS_LIMIT_REGISTER 20'h04fff
`define DS_LIMIT_REGISTER 20'h011ff
`define SS_LIMIT_REGISTER 20'h04000
`define ES_LIMIT_REGISTER 20'h003ff
`define FS_LIMIT_REGISTER 20'h003ff
`define GS_LIMIT_REGISTER 20'h007ff

/*
ES = 000
CS = 001
SS = 010
DS = 011
FS = 100
GS  = 101
*/

module segment_limit_check (
   input [2:0] SEG1_ID,
 
   input [31:0] ADD_BASE_DISP, MUX_SIB_SI, 
);

   mux4$
      mux_seg1 [31:0] (mux_seg1_out, {12'h000, `ES_LIMIT_REGISTER}, {12'h000, `CS_LIMIT_REGISTER}, 32'hFFFFFFFF, {12'h000, `DS_LIMIT_REGISTER}, SEG1_ID[1:0]),
      mux_seg2 [31:0] (mux_seg2_out, {12'h000, `FS_LIMIT_REGISTER}, {12'h000, `GS_LIMIT_REGISTER}, 32'hFFFFFFFF, 32'hFFFFFFFF, SEG1_ID[1:0]);
   mux2$
      mux_seg [31:0] (mux_seg_out, mux_seg1_out, mux_seg2_out, SEG1_ID[2]);
   inv1$
      inv_seg [31:0] (seg_limit_bar, mux_seg_out);

   mux4$ mux_data_size [2:0] (mux_data_size_out, 3'b000, 3'b001, 3'b011, 3'b111);

   adder32
      add_sib_si (add_sib_si_out, , ADD_BASE_DISP, MUX_SIB_SI),
      add_seg (add_seg_out, , seg_limit_bar, mux_data_size_out),
      add_limit (add_limit_out, , add_sib_si_out, add_seg_out);
endmodule
   
