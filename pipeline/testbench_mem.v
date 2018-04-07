module testbench_mem;

   reg CLK, CLR, PRE, V;

   wire [31:0] ME_PS_NEIP;
   wire [15:0] ME_PS_NCS, ME_PS_NCS_NC;
   wire [127:0] ME_PS_CONTROL_STORE;

   wire [31:0] ME_PS_A, ME_PS_B;
   wire [63:0] ME_PS_MM_A, ME_PS_MM_B;
   wire [31:0] ME_PS_SP_XCHG_DATA;

   wire [31:0] ME_PS_MEM_RD_ADDR, ME_PS_MEM_WR_ADDR;
   wire [1:0] ME_PS_DATA_SIZE;

   wire [2:0] ME_PS_D2_ALUK_EX;
   wire [2:0] ME_PS_DRID1, ME_PS_DRID2;

   wire ME_PS_D2_MEM_RD_ME, ME_PS_D2_MEM_WR_WB, ME_PS_D2_LD_GPR1_WB, ME_PS_D2_LD_MM_WB;

   // Signals not from latches
   wire [63:0] DCACHE_DATA;
   wire DCACHE_READY;

   wire ME_DCACHE_EN;

   wire [31:0] ME_NEIP_OUT;
   wire [15:0] ME_NCS_OUT;
   wire [127:0] ME_CONTROL_STORE_OUT;

   wire [31:0] ME_A_OUT, ME_B_OUT;
   wire [63:0] ME_MM_A_OUT, ME_MM_B_OUT;
   wire [31:0] ME_SP_XCHG_DATA_OUT;

   wire [31:0] ME_MEM_RD_ADDR_OUT, ME_MEM_WR_ADDR_OUT;
   wire [1:0] ME_DATA_SIZE_OUT;

   wire [2:0] ME_D2_ALUK_EX_OUT;
   wire [2:0] ME_DRID1_OUT, ME_DRID2_OUT;

   wire ME_D2_MEM_WR_WB_OUT, ME_D2_LD_GPR1_WB_OUT, ME_D2_LD_MM_WB_OUT;

   wire [31:0] AG_OUT1_ME_PS, ME_PS_IN1;

   reg 	       LD_ME;
   
   reg [31:0] AG_NEIP_OUT;
   reg [15:0] AG_NCS_OUT;
   reg [127:0] AG_CONTROL_STORE_OUT;
   
   reg [31:0] AG_A_OUT, AG_B_OUT;
   reg [63:0] AG_MM_A_OUT, AG_MM_B_OUT;
   reg [31:0] AG_SP_XCHG_DATA_OUT;
   reg [31:0] AG_MEM_RD_ADDR_OUT, AG_MEM_WR_ADDR_OUT;
   
   reg [2:0]  AG_D2_ALUK_EX_OUT;
   reg [2:0]  AG_DRID1_OUT, AG_DRID2_OUT;

   reg        AG_D2_MEM_RD_ME_OUT, AG_D2_MEM_WR_WB_OUT;
   reg        AG_D2_LD_GPR1_WB_OUT, AG_D2_LD_MM_WB_OUT;

   reg32e$
     u_reg_me_ps_neip (CLK, AG_NEIP_OUT, ME_PS_NEIP, , CLR, PRE, LD_ME),
     u_reg_me_ps_cs (CLK, {16'b0, AG_NCS_OUT}, {ME_PS_NCS_NC, ME_PS_NCS}, , CLR, PRE, LD_ME);

   reg64e$
     u_reg_me_ps_control_store0 (CLK, AG_CONTROL_STORE_OUT[127:64], ME_PS_CONTROL_STORE[127:64], , CLR, PRE, LD_ME),
     u_reg_me_ps_control_store1 (CLK, AG_CONTROL_STORE_OUT[63:0], ME_PS_CONTROL_STORE[63:0], , CLR, PRE, LD_ME);

   reg32e$
     u_reg_me_ps_a (CLK, AG_A_OUT, ME_PS_A, , CLR, PRE, LD_ME),
     u_reg_me_ps_b (CLK, AG_B_OUT, ME_PS_B, , CLR, PRE, LD_ME);

   reg64e$
     u_reg_me_ps_mm_a (CLK, AG_MM_A_OUT, ME_PS_MM_A, , CLR, PRE, LD_ME),
     u_reg_me_ps_mm_b (CLK, AG_MM_B_OUT, ME_PS_MM_B, , CLR, PRE, LD_ME);

   reg32e$
     u_reg_me_ps_sp_xchg_data (CLK, AG_SP_XCHG_DATA_OUT, ME_PS_SP_XCHG_DATA, , CLR, PRE, LD_ME),
     u_reg_me_mem_rd_addr (CLK, AG_MEM_RD_ADDR_OUT, ME_PS_MEM_RD_ADDR, , CLR, PRE, LD_ME),
     u_reg_me_mem_wr_addr (CLK, AG_MEM_WR_ADDR_OUT, ME_PS_MEM_WR_ADDR, , CLR, PRE, LD_ME);

   assign AG_OUT1_ME_PS[31:22] = {
          AG_D2_ALUK_EX_OUT, AG_DRID1_OUT, AG_DRID2_OUT, AG_D2_MEM_RD_ME_OUT, AG_D2_MEM_WR_WB_OUT,
	  AG_D2_LD_GPR1_WB_OUT, AG_D2_LD_MM_WB_OUT };

   assign { ME_PS_D2_ALUK_EX, ME_PS_DRID1, ME_PS_DRID2, ME_PS_D2_MEM_RD_ME, ME_PS_D2_MEM_WR_WB,
            ME_PS_D2_LD_GPR1_WB, ME_PS_D2_LD_MM_WB } = ME_PS_IN1[31:22];

   reg32e$
     u_reg_me_ps_in1 (CLK, AG_OUT1_ME_PS, ME_PS_IN1, , CLR, PRE, LD_ME);
   
   memory_stage me_stage (CLK, CLR, PRE, V,
                          ME_PS_NEIP, ME_PS_NCS, ME_PS_CONTROL_STORE,
                          ME_PS_A, ME_PS_B, ME_PS_MM_A, ME_PS_MM_B, ME_PS_SP_XCHG_DATA,
                          ME_PS_MEM_RD_ADDR, ME_PS_MEM_WR_ADDR, ME_PS_DATA_SIZE,
                          ME_PS_D2_ALUK_EX, ME_PS_DRID1, ME_PS_DRID2,
                          ME_PS_D2_MEM_RD_ME, ME_PS_D2_MEM_WR_WB, ME_PS_D2_LD_GPR1_WB, ME_PS_D2_LD_MM_WB,

                          DCACHE_DATA, DCACHE_READY,

                          // output
                          ME_DCACHE_EN, 

                          // outputs to next stage latches
                          ME_NEIP_OUT, ME_NCS_OUT, ME_CONTROL_STORE_OUT,
                          ME_A_OUT, ME_B_OUT, ME_MM_A_OUT, ME_MM_B_OUT, ME_SP_XCHG_DATA_OUT,
                          ME_MEM_RD_ADDR_OUT, ME_MEM_WR_ADDR_OUT, ME_DATA_SIZE_OUT, ME_DE_ALUK_EX_OUT,
                          ME_DRID1_OUT, ME_DRID2_OUT, ME_D2_MEM_WR_WB_OUT, ME_D2_LD_GPR1_WB_OUT, ME_D2_LD_MM_WB_OUT);

endmodule

