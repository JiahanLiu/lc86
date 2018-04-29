module memory_stage1 (
   input CLK, RST, SET, V,

   // inputs from previous stage
   input [31:0] MEM_RD_ADDR, MEM_WR_ADDR,
   input [1:0] D2_MEM_SIZE_WB,

   input D2_MEM_RD_ME, D2_MEM_WR_WB,

   // inputs for dependency check
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

   // outputs to next stage latches
   output [31:0] MEM_WR_ADDR_OUT,
   output [1:0] D2_MEM_SIZE_WB_OUT,

   output D2_MEM_WR_WB_OUT,

   output RD_ADDR1_V_OUT,
   output [31:0] RA_RD_ADDR1_OUT,
   output [3:0] RA_RD_SIZE1_OUT,

   output RD_ADDR2_V_OUT,
   output [31:0] RA_RD_ADDR2_OUT,
   output [3:0] RA_RD_SIZE2_OUT,

   output WR_ADDR1_V_OUT,
   output [31:0] RA_WR_ADDR1_OUT,
   output [3:0] RA_WR_SIZE1_OUT,

   output WR_ADDR2_V_OUT,
   output [31:0] RA_WR_ADDR2_OUT,
   output [3:0] RA_WR_SIZE2_OUT,

   output PAGE_FAULT_EXC_OUT,
   output GPROT_EXC_OUT,
   output MEM_DEP_STALL_OUT
);
//`include "./control_store/control_store_wires.v"
//`include "./control_store/control_store_signals.v"

   wire v_mem_rd, v_mem_wr;
   wire lsu_rd_addr1_v_out, lsu_rd_addr2_v_out,
        lsu_wr_addr1_v_out, lsu_wr_addr2_v_out;
   wire [31:0] lsu_ra_rd_addr1_out, lsu_ra_rd_addr2_out,
               lsu_ra_wr_addr1_out, lsu_ra_wr_addr2_out;
   wire [3:0] lsu_ra_rd_size1_out, lsu_ra_rd_size2_out,
              lsu_ra_wr_size1_out, lsu_ra_wr_size2_out;
   wire lsu_rd_page_fault_exc_out, lsu_wr_page_fault_exc_out;
   wire lsu_gprot_exc_out;

   and2$
      and_v_mem_rd (v_mem_rd, V, D2_MEM_RD_ME),
      and_v_mem_wr (v_mem_wr, V, D2_MEM_WR_WB);

   lsu u_lsu (v_mem_rd, MEM_RD_ADDR, D2_MEM_SIZE_WB,
              v_mem_wr, MEM_WR_ADDR, D2_MEM_SIZE_WB,

              lsu_rd_addr1_v_out, lsu_ra_rd_addr1_out, lsu_ra_rd_size1_out,
              lsu_rd_addr2_v_out, lsu_ra_rd_addr2_out, lsu_ra_rd_size2_out,

              lsu_wr_addr1_v_out, lsu_ra_wr_addr1_out, lsu_ra_wr_size1_out,
              lsu_wr_addr2_v_out, lsu_ra_wr_addr2_out, lsu_ra_wr_size2_out,

              lsu_rd_page_fault_exc_out, lsu_wr_page_fault_exc_out,
              lsu_gprot_exc_out);

   assign RD_ADDR1_V_OUT = lsu_rd_addr1_v_out;
   assign RA_RD_ADDR1_OUT = lsu_ra_rd_addr1_out;
   assign RA_RD_SIZE1_OUT = lsu_ra_rd_size1_out;
   assign RD_ADDR2_V_OUT = lsu_rd_addr2_v_out;
   assign RA_RD_ADDR2_OUT = lsu_ra_rd_addr2_out;
   assign RA_RD_SIZE2_OUT = lsu_ra_rd_size2_out;

   assign WR_ADDR1_V_OUT = lsu_wr_addr1_v_out;
   assign RA_WR_ADDR1_OUT = lsu_ra_wr_addr1_out;
   assign RA_WR_SIZE1_OUT = lsu_ra_wr_size1_out;
   assign WR_ADDR2_V_OUT = lsu_wr_addr2_v_out;
   assign RA_WR_ADDR2_OUT = lsu_ra_wr_addr2_out;
   assign RA_WR_SIZE2_OUT = lsu_ra_wr_size2_out;

   or2$ or0 (PAGE_FAULT_EXC_OUT, lsu_rd_page_fault_exc_out, lsu_wr_page_fault_exc_out);
   assign GPROT_EXC_OUT = lsu_gprot_exc_out;

   mem_dependency_check
      u_mem_dependency_check (V,
                              lsu_rd_addr1_v_out, lsu_ra_rd_addr1_out, lsu_ra_rd_size1_out,
                              lsu_rd_addr2_v_out, lsu_ra_rd_addr2_out, lsu_ra_rd_size2_out,

                              ME_V,
                              ME_WR_ADDR1_V, ME_WR_ADDR1, ME_WR_SIZE1,
                              ME_WR_ADDR2_V, ME_WR_ADDR2, ME_WR_SIZE2,

                              EX_V,
                              EX_WR_ADDR1_V, EX_WR_ADDR1, EX_WR_SIZE1,
                              EX_WR_ADDR2_V, EX_WR_ADDR2, EX_WR_SIZE2,

                              MEM_DEP_STALL_OUT);

   assign MEM_WR_ADDR_OUT = MEM_WR_ADDR;
   assign D2_MEM_SIZE_WB_OUT = D2_MEM_SIZE_WB;
   assign D2_MEM_WR_WB_OUT = D2_MEM_WR_WB;

endmodule
