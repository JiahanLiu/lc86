module mem_dependency_check (
   input V,

   input RD_ADDR1_V,
   input [31:0] RD_ADDR1,
   input [3:0] RD_SIZE1,

   input RD_ADDR2_V,
   input [31:0] RD_ADDR2,
   input [3:0] RD_SIZE2,

   input ME_V,
   input ME_WR_ADDR1_V,
   input [31:0] ME_WR_ADDR1,
   input [3:0] ME_WR_SIZE1,

   input ME_WR_ADDR2_V,
   input [31:0] ME_WR_ADDR2,
   input [3:0] ME_WR_SIZE2,

   input EX_V,
   input EX_WR_ADDR1_V,
   input [31:0] EX_WR_ADDR1,
   input [3:0] EX_WR_SIZE1,

   input EX_WR_ADDR2_V,
   input [31:0] EX_WR_ADDR2,
   input [3:0] EX_WR_SIZE2,

   output MEM_DEP_STALL_OUT
);

   wire [31:0] add_rd_addr1_out, add_rd_addr2_out,
               add_me_wr_addr1_out, add_me_wr_addr2_out,
               add_ex_wr_addr1_out, add_ex_wr_addr2_out;

   adder32_w_carry_in add_rd_addr1 (add_rd_addr1_out, , RD_ADDR1, {28'b0, RD_SIZE1}, 1'b0); 
   adder32_w_carry_in add_rd_addr2 (add_rd_addr2_out, , RD_ADDR2, {28'b0, RD_SIZE2}, 1'b0); 
   adder32_w_carry_in add_me_wr_addr1 (add_me_wr_addr1_out, , ME_WR_ADDR1, {28'b0, ME_WR_SIZE1}, 1'b0); 
   adder32_w_carry_in add_me_wr_addr2 (add_me_wr_addr2_out, , ME_WR_ADDR2, {28'b0, ME_WR_SIZE2}, 1'b0); 
   adder32_w_carry_in add_ex_wr_addr1 (add_ex_wr_addr1_out, , EX_WR_ADDR1, {28'b0, EX_WR_SIZE1}, 1'b0); 
   adder32_w_carry_in add_ex_wr_addr2 (add_ex_wr_addr2_out, , EX_WR_ADDR2, {28'b0, EX_WR_SIZE2}, 1'b0); 

// rd_addr1 >= me_addr1_end
// rd_addr1_end <= me_addr1_start
//
// rd_addr1 >= me_addr2_end
// rd_addr1_end <= me_addr2_start
//

   wire stall_rd1_me1_end, stall_rd1_end_me1, stall_rd1_me2_end, stall_rd1_end_me2,
        stall_rd1_ex1_end, stall_rd1_end_ex1, stall_rd1_ex2_end, stall_rd1_end_ex2,
        stall_rd2_me1_end, stall_rd2_end_me1, stall_rd2_me2_end, stall_rd2_end_me2,
        stall_rd2_ex1_end, stall_rd2_end_ex1, stall_rd2_ex2_end, stall_rd2_end_ex2;

   mag_comp32
      u_comp_rd1_me1_end (RD_ADDR1, add_me_wr_addr1_out, , stall_rd1_me1_end, ),
      u_comp_rd1_end_me1 (add_rd_addr1_out, ME_WR_ADDR1, stall_rd1_end_me1, , ),

      u_comp_rd1_me2_end (RD_ADDR1, add_me_wr_addr2_out, , stall_rd1_me2_end, ),
      u_comp_rd1_end_me2 (add_rd_addr1_out, ME_WR_ADDR2, stall_rd1_end_me2, , ),

      u_comp_rd1_ex1_end (RD_ADDR1, add_ex_wr_addr1_out, , stall_rd1_ex1_end, ),
      u_comp_rd1_end_ex1 (add_rd_addr1_out, EX_WR_ADDR1, stall_rd1_end_ex1, , ),

      u_comp_rd1_ex2_end (RD_ADDR1, add_ex_wr_addr2_out, , stall_rd1_ex2_end, ),
      u_comp_rd1_end_ex2 (add_rd_addr1_out, EX_WR_ADDR2, stall_rd1_end_ex2, , ),

      u_comp_rd2_me1_end (RD_ADDR2, add_me_wr_addr1_out, , stall_rd2_me1_end, ),
      u_comp_rd2_end_me1 (add_rd_addr2_out, ME_WR_ADDR1, stall_rd2_end_me1, , ),

      u_comp_rd2_me2_end (RD_ADDR2, add_me_wr_addr2_out, , stall_rd2_me2_end, ),
      u_comp_rd2_end_me2 (add_rd_addr2_out, ME_WR_ADDR2, stall_rd2_end_me2, , ),

      u_comp_rd2_ex1_end (RD_ADDR2, add_ex_wr_addr1_out, , stall_rd2_ex1_end, ),
      u_comp_rd2_end_ex1 (add_rd_addr2_out, EX_WR_ADDR1, stall_rd2_end_ex1, , ),

      u_comp_rd2_ex2_end (RD_ADDR2, add_ex_wr_addr2_out, , stall_rd2_ex2_end, ),
      u_comp_rd2_end_ex2 (add_rd_addr2_out, EX_WR_ADDR2, stall_rd2_end_ex2, , );

// stall_rd1_me1_end_v = V && RD_ADDR1_V && ME_V && ME_WR_ADDR1_V
   and2$
      and_rd_addr1_v (and_rd_addr1_v_out, V, RD_ADDR1_V),
      and_rd_addr2_v (and_rd_addr2_v_out, V, RD_ADDR2_V),

      and_me_addr1_v (and_me_addr1_v_out, ME_V, ME_WR_ADDR1_V),
      and_me_addr2_v (and_me_addr2_v_out, ME_V, ME_WR_ADDR2_V),

      and_ex_addr1_v (and_ex_addr1_v_out, EX_V, EX_WR_ADDR1_V),
      and_ex_addr2_v (and_ex_addr2_v_out, EX_V, EX_WR_ADDR2_V);

   wire and_rd1_me1_v_out, and_rd1_me2_v_out, and_rd1_ex1_v_out, and_rd1_ex2_v_out,
        and_rd2_me1_v_out, and_rd2_me2_v_out, and_rd2_ex1_v_out, and_rd2_ex2_v_out;

   and2$
      and_rd1_me1_v (and_rd1_me1_v_out, and_rd_addr1_v_out, and_me_addr1_v_out),
      and_rd1_me2_v (and_rd1_me2_v_out, and_rd_addr1_v_out, and_me_addr2_v_out),

      and_rd1_ex1_v (and_rd1_ex1_v_out, and_rd_addr1_v_out, and_ex_addr1_v_out),
      and_rd1_ex2_v (and_rd1_ex2_v_out, and_rd_addr1_v_out, and_ex_addr2_v_out),

      and_rd2_me1_v (and_rd2_me1_v_out, and_rd_addr2_v_out, and_me_addr1_v_out),
      and_rd2_me2_v (and_rd2_me2_v_out, and_rd_addr2_v_out, and_me_addr2_v_out),

      and_rd2_ex1_v (and_rd2_ex1_v_out, and_rd_addr2_v_out, and_ex_addr1_v_out),
      and_rd2_ex2_v (and_rd2_ex2_v_out, and_rd_addr2_v_out, and_ex_addr2_v_out);

   bufferH16$
      buf_rd_addr1_v (buf_rd_addr1_v_out, and_rd_addr1_v_out),
      buf_rd_addr2_v (buf_rd_addr2_v_out, and_rd_addr2_v_out);

   wire and_rd1_me1_stall_out;
   wire and_rd1_me2_stall_out;
   wire and_rd1_ex1_stall_out;
   wire and_rd1_ex2_stall_out;
   wire and_rd2_me1_stall_out;
   wire and_rd2_me2_stall_out;
   wire and_rd2_ex1_stall_out;
   wire and_rd2_ex2_stall_out;

   and3$
      and_rd1_me1_stall (and_rd1_me1_stall_out, and_rd1_me1_v_out, stall_rd1_me1_end, stall_rd1_end_me1),
      and_rd1_me2_stall (and_rd1_me2_stall_out, and_rd1_me2_v_out, stall_rd1_me2_end, stall_rd1_end_me2),

      and_rd1_ex1_stall (and_rd1_ex1_stall_out, and_rd1_ex1_v_out, stall_rd1_ex1_end, stall_rd1_end_ex1),
      and_rd1_ex2_stall (and_rd1_ex2_stall_out, and_rd1_ex2_v_out, stall_rd1_ex2_end, stall_rd1_end_ex2),

      and_rd2_me1_stall (and_rd2_me1_stall_out, and_rd2_me1_v_out, stall_rd2_me1_end, stall_rd2_end_me1),
      and_rd2_me2_stall (and_rd2_me2_stall_out, and_rd2_me2_v_out, stall_rd2_me2_end, stall_rd2_end_me2),

      and_rd2_ex1_stall (and_rd2_ex1_stall_out, and_rd2_ex1_v_out, stall_rd2_ex1_end, stall_rd2_end_ex1),
      and_rd2_ex2_stall (and_rd2_ex2_stall_out, and_rd2_ex2_v_out, stall_rd2_ex2_end, stall_rd2_end_ex2);

   wire or0_out, or1_out, or2_out, or3_out;

   or3$
      or0 (or0_out, and_rd1_me1_stall_out, and_rd1_me2_stall_out, and_rd1_ex1_stall_out),
      or1 (or1_out, and_rd1_ex2_stall_out, and_rd2_me1_stall_out, and_rd2_me2_stall_out);
   or2$ or2 (or2_out, and_rd2_ex1_stall_out, and_rd2_ex2_stall_out);
   or3$ or3 (or3_out, or0_out, or1_out, or2_out);

   assign MEM_DEP_STALL_OUT = or3_out;

endmodule

