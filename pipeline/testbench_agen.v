module testbench_agen;

   reg CLK, SET, RST, NextV;

   wire [31:0] AG_PS_EIP;
   wire [15:0] AG_PS_CS, AG_PS_CS_NC;
   
   wire [63:0] AG_PS_CONTROL_STORE;

   wire [1:0] AG_PS_DATA_SIZE;
   wire AG_PS_D2_SR1_NEEDED_AG, AG_PS_D2_SEG1_NEEDED_AG, AG_PS_D2_MM1_NEEDED_AG;

   wire AG_PS_D2_MEM_RD_ME, AG_PS_D2_MEM_WR_ME;
   wire [2:0] AG_PS_D2_ALUK_EX;
   wire AG_PS_D2_LD_GPR1_WB, AG_PS_D2_LD_MM_WB;

   wire [2:0] AG_PS_SR1, AG_PS_SR2, AG_PS_SR3, AG_PS_SIB_I, AG_PS_SEG1, AG_PS_SEG2;
   wire [31:0] AG_PS_IMM32, AG_PS_DISP32;

   wire AG_PS_DE_SIB_EN_AG, AG_PS_DE_DISP_EN_AG, AG_PS_DE_BASE_REG_EN_AG;
   wire AG_PS_DE_MUX_SEG_AG, AG_PS_DE_CMPXCHG_AG;
   wire [1:0] AG_PS_DE_SIB_S_AG;

   wire [31:0] SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA;
   wire [15:0] SEG1_DATA, SEG2_DATA;
   wire [63:0] MM1_DATA, MM2_DATA;

   wire [3:0] DE_EXC_CODE_AG;

   // Signals to register file
   wire [2:0] AG_SR1_OUT, AG_SR2_OUT, AG_SEG1_OUT, AG_SEG2_OUT, AG_MM1_OUT, AG_MM2_OUT;
   wire [1:0] AG_DATA_SIZE_OUT;
   
   // Signals for next stage latches
   wire [31:0] AG_NEIP_OUT;
   wire [15:0] AG_NCS_OUT;
   wire [63:0] AG_CONTROL_STORE_OUT;
   
   wire [31:0] AG_A_OUT, AG_B_OUT;
   wire [63:0] AG_MM_A_OUT, AG_MM_B_OUT;
   wire [31:0] AG_SP_XCHG_DATA_OUT;
   wire [31:0] AG_MEM_RD_ADDR_OUT, AG_MEM_WR_ADDR_OUT;
   
   wire [2:0]  AG_D2_ALUK_EX_OUT;
   wire [2:0]  AG_DRID1_OUT, AG_DRID2_OUT;

   wire        AG_D2_MEM_RD_ME_OUT, AG_D2_MEM_WR_WB_OUT;
   wire        AG_D2_LD_GPR1_WB_OUT, AG_D2_LD_MM_WB_OUT;
   wire        AG_DEP_STALL_OUT, AG_SEG_LIMIT_EXC_OUT;
   
   wire [31:0] D2_OUT1_AG_PS, D2_OUT2_AG_PS, AG_PS_IN1, AG_PS_IN2;

   reg [31:0]  D2_EIP_OUT;
   reg [15:0]  D2_CS_OUT;
   reg [63:0]  D2_CONTROL_STORE_OUT;
   reg [1:0]   D2_DATA_SIZE_AG_OUT;
   reg 	       D2_SR1_NEEDED_AG_OUT, D2_SEG1_NEEDED_AG_OUT, D2_MM1_NEEDED_AG_OUT, D2_MEM_RD_ME_OUT, D2_MEM_WR_ME_OUT;
   reg [2:0]   D2_ALUK_EX_OUT;
   reg 	       D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT;
   reg [2:0]   D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT, D2_SEG1_OUT, D2_SEG2_OUT;
   reg [31:0]  D2_IMM32_OUT, D2_DISP32_OUT;
   reg 	       D2_SIB_EN_AG, D2_DISP_EN_AG, D2_BASE_REG_EN_AG, D2_MUX_SEG_AG, D2_CMPXCHG_AG;
   reg [1:0]   D2_SIB_S_AG;

   reg 	       LD_AG;
   
   reg 	       CLR, PRE;

   reg [2:0]   AG_DRID1, AG_DRID2;
   reg 	       V_AG_LD_GPR1, V_AG_LD_GPR2, V_AG_LD_SEG, V_AG_LD_CSEG, V_AG_LD_MM;
   reg [2:0]   ME_DRID1, ME_DRID2;
   reg 	       V_ME_LD_GPR1, V_ME_LD_GPR2, V_ME_LD_SEG, V_ME_LD_CSEG, V_ME_LD_MM;
   reg [2:0]   EX_DRID1, EX_DRID2;
   reg 	       V_EX_LD_GPR1, V_EX_LD_GPR2, V_EX_LD_SEG, V_EX_LD_CSEG, V_EX_LD_MM;
   
   initial CLK = 1'b0;
   
   always #(`half_cycle) CLK = ~CLK;

   initial
     begin
	CLR = 1'b1;
	PRE = 1'b1;

	NextV = 1'b1;
	
	LD_AG = 1'b1;
	AG_DRID1 = 3'b000;
	AG_DRID2 = 3'b000;
	V_AG_LD_GPR1 = 1'b1;
	V_AG_LD_GPR2 = 1'b0;
	V_AG_LD_SEG = 1'b0;
	V_AG_LD_CSEG = 1'b0;
	V_AG_LD_MM = 1'b0;

	ME_DRID1 = 3'b000;
	ME_DRID2 = 3'b000;
	V_ME_LD_GPR1 = 1'b0;
	V_ME_LD_GPR2 = 1'b0;
	V_ME_LD_SEG = 1'b0;
	V_ME_LD_CSEG = 1'b0;
	V_ME_LD_MM = 1'b0;

	EX_DRID1 = 3'b000;
	EX_DRID2 = 3'b000;
	V_EX_LD_GPR1 = 1'b0;
	V_EX_LD_GPR2 = 1'b0;
	V_EX_LD_SEG = 1'b0;
	V_EX_LD_CSEG = 1'b0;
	V_EX_LD_MM = 1'b0;
     end // initial begin
   
   initial 
     begin	
	D2_EIP_OUT = 32'h00000000;
	D2_CS_OUT = 16'h0000;
	D2_CONTROL_STORE_OUT = 64'b0001000111010010000000001010000001000000000000000000000000001100;
	D2_DATA_SIZE_AG_OUT = 2'b11;
	D2_SR1_NEEDED_AG_OUT = 1'b1;
	D2_SEG1_NEEDED_AG_OUT = 1'b0;
	D2_MM1_NEEDED_AG_OUT = 1'b0;
	D2_MEM_RD_ME_OUT = 1'b0;
	D2_MEM_WR_ME_OUT = 1'b0;
	D2_ALUK_EX_OUT = 3'b000;
	D2_LD_GPR1_WB_OUT = 1'b1;
	D2_LD_MM_WB_OUT = 1'b0;
	D2_SR1_OUT = 3'b000;
	D2_SR2_OUT = 3'b000;
	D2_SR3_OUT = 3'b000;
	D2_SIB_I_OUT = 3'b000;
	D2_SEG1_OUT = 3'b000;
	D2_SEG2_OUT = 3'b00;
	D2_IMM32_OUT = 32'h55555555;
	D2_DISP32_OUT = 32'h33333333;
	D2_SIB_EN_AG = 1'b0;
	D2_DISP_EN_AG = 1'b0;
	D2_BASE_REG_EN_AG = 1'b0;
	D2_MUX_SEG_AG = 1'b0;
	D2_CMPXCHG_AG = 1'b0;
	D2_SIB_S_AG = 2'b00;

	#(`half_cycle*10)
	$stop;
     end // initial begin

   initial
      begin
         $vcdplusfile("dump.vpd");
         $vcdpluson(0, testbench_agen);
      end
   
   reg32e$
      u_reg_ag_ps_eip (CLK, D2_EIP_OUT, AG_PS_EIP, , CLR, PRE, LD_AG),
      u_reg_ag_ps_cs (CLK, {16'b0, D2_CS_OUT}, {AG_PS_CS_NC, AG_PS_CS}, , CLR, PRE, LD_AG);

   reg64e$
      u_reg_ag_ps_control_store (CLK, D2_CONTROL_STORE_OUT, AG_PS_CONTROL_STORE, , CLR, PRE, LD_AG);

   // [31:2]
   assign D2_OUT1_AG_PS[31:2] = { 
          D2_DATA_SIZE_AG_OUT, D2_SR1_NEEDED_AG_OUT, D2_SEG1_NEEDED_AG_OUT, D2_MM1_NEEDED_AG_OUT,
          D2_MEM_RD_ME_OUT, D2_MEM_WR_ME_OUT, D2_ALUK_EX_OUT, D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT,
          D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT, D2_SEG1_OUT, D2_SEG2_OUT };

   assign { AG_PS_DATA_SIZE, AG_PS_D2_SR1_NEEDED_AG, AG_PS_D2_SEG1_NEEDED_AG, AG_PS_D2_MM1_NEEDED_AG,
            AG_PS_D2_MEM_RD_ME, AG_PS_D2_MEM_WR_ME, AG_PS_D2_ALUK_EX, AG_PS_D2_LD_GPR1_WB, AG_PS_D2_LD_MM_WB,
            AG_PS_SR1, AG_PS_SR2, AG_PS_SR3, AG_PS_SIB_I, AG_PS_SEG1, AG_PS_SEG2 } = AG_PS_IN1[31:2];
											       
   reg32e$
      u_reg_ag_ps_in1 (CLK, D2_OUT1_AG_PS, AG_PS_IN1, , CLR, PRE, LD_AG),
      u_reg_ag_ps_imm32 (CLK, D2_IMM32_OUT, AG_PS_IMM32, , CLR, PRE, LD_AG),
      u_reg_ag_ps_disp32 (CLK, D2_DISP32_OUT, AG_PS_DISP32, , CLR, PRE, LD_AG);

   // [31:25]
   assign D2_OUT2_AG_PS[31:25] = { D2_SIB_EN_AG, D2_DISP_EN_AG, D2_BASE_REG_EN_AG, D2_MUX_SEG_AG,
                                   D2_CMPXCHG_AG, D2_SIB_S_AG };
   assign { AG_PS_DE_SIB_EN_AG, AG_PS_DE_DISP_EN_AG, AG_PS_DE_BASE_REG_EN_AG,
            AG_PS_DE_MUX_SEG_AG, AG_PS_DE_CMPXCHG_AG, AG_PS_DE_SIB_S_AG } = AG_PS_IN2[31:25];
   reg32e$
      u_reg_ag_ps_in2 (CLK, D2_OUT2_AG_PS, AG_PS_IN2, , CLR, PRE, LD_AG);
      
   address_generation ag_stage (CLK, SET, RST, NextV,

                                // inputs from pipestage latches
                                AG_PS_EIP, AG_PS_CS, AG_PS_CONTROL_STORE,
                                AG_PS_DATA_SIZE, AG_PS_D2_SR1_NEEDED_AG, AG_PS_D2_SEG1_NEEDED_AG, AG_PS_D2_MM1_NEEDED_AG,
                                AG_PS_D2_MEM_RD_ME, AG_PS_D2_MEM_WR_ME,
                                AG_PS_D2_ALUK_EX, AG_PS_D2_LD_GPR1_WB, AG_PS_D2_LD_MM_WB,
                                AG_PS_SR1, AG_PS_SR2, AG_PS_SR3, AG_PS_SIB_I, AG_PS_SEG1, AG_PS_SEG2,
                                AG_PS_IMM32, AG_PS_DISP32,
                                AG_PS_DE_SIB_EN_AG, AG_PS_DE_DISP_EN_AG, AG_PS_DE_BASE_REG_EN_AG,
                                AG_PS_DE_MUX_SEG_AG, AG_PS_DE_CMPXCHG_AG,
                                AG_PS_DE_SIB_S_AG,

                                // inputs from register file
                                SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA,
                                SEG1_DATA, SEG2_DATA, MM1_DATA, MM2_DATA,

                                // inputs from exception/interrupt logic
                                DE_EXC_CODE_AG,

                                // dependency check inputs
                                AG_DRID1, AG_DRID2,
                                V_AG_LD_GPR1, V_AG_LD_GPR2, V_AG_LD_SEG, V_AG_LD_CSEG, V_AG_LD_MM,
                                ME_DRID1, ME_DRID2,
                                V_ME_LD_GPR1, V_ME_LD_GPR2, V_ME_LD_SEG, V_ME_LD_CSEG, V_ME_LD_MM,
                                EX_DRID1, EX_DRID2,
                                V_EX_LD_GPR1, V_EX_LD_GPR2, V_EX_LD_SEG, V_EX_LD_CSEG, V_EX_LD_MM,

                                // outputs to register file
                                AG_SR1_OUT, AG_SR2_OUT, AG_SEG1_OUT, AG_SEG2_OUT, AG_MM1_OUT, AG_MM2_OUT,
                                AG_DATA_SIZE_OUT,

                                // outputs to next stage
                                AG_NEIP_OUT, AG_NCS_OUT, AG_CONTROL_STORE_OUT,
                                AG_A_OUT, AG_B_OUT, AG_MM_A_OUT, AG_MM_B_OUT, AG_SP_XCHG_DATA_OUT,
                                AG_MEM_RD_ADDR_OUT, AG_MEM_WR_ADDR_OUT,
                                AG_D2_ALUK_EX_OUT, AG_DRID1_OUT, AG_DRID2_OUT,
                                AG_D2_MEM_RD_ME_OUT, AG_D2_MEM_WR_WB_OUT,
                                AG_D2_LD_GPR1_WB_OUT, AG_D2_LD_MM_WB_OUT,

                                // other outputs
                                AG_DEP_STALL_OUT, AG_SEG_LIMIT_EXC_OUT);

endmodule

