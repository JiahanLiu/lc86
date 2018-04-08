module TOP;
//this module is used to debug the basic functionality of the simulator
//the clk cycle used to drive the entire system
   reg clk, clr, pre;
   integer clk_cycle = 5;
   always  #(clk_cycle)  clk = ~clk;
   //SIMULATOR u_SIMULATOR(clk, clr, pre);
   
   initial
     begin
	clk = 0;
	clr = 1;
	pre = 1;
	# clk_cycle
	clr = 0;
	# (clk_cycle -2)
	clr = 1;
	# (clk_cycle - 3)
	# (clk_cycle * 2);
     end 

   PIPELINE u_pipeline(clk, clr, pre);

   initial #(29 * clk_cycle) $finish;
   
   initial
     begin
	$vcdplusfile("pipeline.dump.vpd");
	$vcdpluson(0, TOP);
     end

   initial
     begin
	$readmemb("../control_store/rom0_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom1);
     end
   
endmodule

module PIPELINE(CLK, CLR, PRE);
   //inputs to this simulator
   input CLK, CLR, PRE;
   assign EN = 1;//placeholder until stalls are working correctly
   
   //signals from WB
   wire [2:0] Out_DR1, Out_DR2, Out_DR3;
   wire [31:0] Out_DR1_Data, Out_DR2_Data, Out_DR3_Data; 
   wire        out_v_de_ld_gpr1_wb, out_v_cs_ld_gpr2_wb, out_v_cs_ld_gpr3_wb;
   wire [1:0]  out_de_datasize;
   
   wire [31:0] Out_Dcache_Data, Out_Dcache_Address;
   
//*******REGISTER FILE*******//
register_file u_register_file (CLK, 
		      SEG_DIN, SEGID1, SEGID2, WRSEGID, SEGWE,
		      MM_DIN, MMID1, MMID2, WRMMID, MMWE, 
		      GPR_DIN0, GPR_DIN1, GPR_DIN2, 
		      GPRID0, GPRID1, GPRID2, GPRID3,
		      GPR_RE0, GPR_RE1, GPR_RE2, GPR_RE3,
		      WRGPR0, WRGPR1, WRGPR2, GPRWE0, GPRWE1, GPRWE2,
	              WE0, WE1, WE2,
		      CS_DIN, EIP_DIN, EFLAGS_DIN,
		      LD_CS, LD_EIP, LD_EFLAGS,
		      SEGDOUT1, SEGDOUT2, MMDOUT1, MMDOUT2,
		      GPRDOUT0, GPRDOUT1, GPRDOUT2, GPRDOUT3,
		      CSDOUT, EIPDOUT, EFLAGSDOUT, RST);
   
//Latches between fetch and decode
wire [31:0] DE_V_OUT_T, DE_V_OUT_T_BAR, DE_OP_CS_OUT_T, DE_OP_CS_OUT_T_BAR, MOD_SIB_OUT, MOD_SIB_OUT_BAR;	//temp wires
wire [127:0] IR_OUT, IR_BAR_OUT;
reg32e$ MOD_SIB(CLK, {16'b0, DE_MODRM_IN, DE_SIB_IN}, MOD_SIB_OUT, MOD_SIB_OUT_BAR, CLR, PRE, EN);
reg32e$ IR_3(CLK, IR_IN[127:96], IR_OUT[127:96], IR_BAR_OUT[127:96], CLR, PRE, EN);
reg32e$ IR_2(CLK, IR_IN[95:64], IR_OUT[95:64], IR_BAR_OUT[95:64], CLR, PRE, EN);
reg32e$ IR_1(CLK, IR_IN[63:32], IR_OUT[63:32], IR_BAR_OUT[63:32], CLR, PRE, EN);
reg32e$ IR_0(CLK, IR_IN[31:0], IR_OUT[31:0], IR_BAR_OUT[31:0], CLR, PRE, EN);
reg32e$ DE_EIP(CLK, DE_EIP_IN, DE_EIP_OUT, DE_EIP_OUT_BAR, CLR, PRE, EN);
reg32e$ DE_V(CLK, {1'b0, DE_DISP_PRES_IN, DE_DISP_SIZE_IN, DE_OFFSET_PRES_IN, DE_OP_SIZE_IN, DE_PRE_PRES_IN, DE_SEG_OVR_IN, DE_OP_OVR_IN, DE_RE_PRE_IN, DE_MODRM_PRES_IN, 
			DE_IMM_PRES_IN, DE_SIB_PRES_IN, DE_IMM_SEL_IN, DE_DISP_SEL_IN, DE_SEGID_IN, DE_MODRM_SEL_IN, DE_IMM_SIZE_IN, DE_OFFSET_SIZE, DE_PRE_SIZE_IN,DE_V_IN}, DE_V_OUT_T, DE_V_OUT_T_BAR, CLR, PRE, EN);	//used for various values 
reg32e$ DE_OP_CS(CLK, {DE_OPCODE_IN, DE_CS_IN}, DE_OP_CS_OUT_T, DE_OP_CS_OUT_T_BAR, CLR, PRE, EN); 
wire DE_V_OUT = DE_V_OUT_T[0];
wire [1:0] DE_PRE_SIZE_OUT = DE_V_OUT_T[2:1];
wire [1:0] DE_OFFSET_SIZE_OUT = DE_V_OUT_T[4:3];
wire [1:0] DE_IMM_SIZE_OUT = DE_V_OUT_T[6:5];
wire [2:0] DE_MODRM_SEL_OUT = DE_V_OUT_T[9:7];
wire [2:0] DE_SEGID_OUT = DE_V_OUT_T[12:10];
wire [2:0] DE_DISP_SEL_OUT = DE_V_OUT_T[15:13];
wire [3:0] DE_IMM_SEL_OUT = DE_V_OUT_T[19:16];
wire DE_SIB_PRES_OUT = DE_V_OUT_T[20];
wire DE_IMM_PRES_OUT = DE_V_OUT_T[21]; 
wire DE_MODRM_PRES_OUT = DE_V_OUT_T[22];
wire DE_RE_PRE_OUT = DE_V_OUT_T[23]; 
wire DE_OP_OVR_OUT = DE_V_OUT_T[24]; 
wire DE_SEG_OVR_OUT = DE_V_OUT_T[25];
wire DE_PRE_PRES_OUT = DE_V_OUT_T[26]; 
wire DE_OP_SIZE_OUT = DE_V_OUT_T[27]; 
wire DE_OFFSET_PRES_OUT = DE_V_OUT_T[28];
wire DE_DISP_SIZE_OUT = DE_V_OUT_T[29]; 
wire DE_DISP_PRES_OUT = DE_V_OUT_T[30];
wire [7:0] DE_SIB_OUT = MOD_SIB_OUT[7:0];
wire DE_MODRM_OUT = MOD_SIB_OUT[15:8];

wire [15:0] DE_OPCODE_OUT = DE_OP_CS_OUT_T[31:16];
wire [15:0] DE_CS_OUT = DE_OP_CS_OUT_T[15:0];

   // Outputs from Decode Stage 2
   wire [31:0]  D2_EIP_OUT;
   wire [15:0]  D2_CS_OUT;
   wire [127:0] D2_CONTROL_STORE_OUT;

   wire [47:0] 	 D2_OFFSET_OUT;
   
   wire [1:0]   D2_DATA_SIZE_AG_OUT;
   wire 	D2_SR1_NEEDED_AG_OUT, D2_SEG1_NEEDED_AG_OUT, D2_MM1_NEEDED_AG_OUT, D2_MEM_RD_ME_OUT, D2_MEM_WR_ME_OUT;
   wire [2:0]   D2_ALUK_EX_OUT;
   wire 	D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT;
   wire [2:0]   D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT, D2_SEG1_OUT, D2_SEG2_OUT;
   wire [31:0]  D2_IMM32_OUT, D2_DISP32_OUT;
   wire 	D2_SIB_EN_AG, D2_DISP_EN_AG, D2_BASE_REG_EN_AG, D2_MUX_SEG_AG, D2_CMPXCHG_AG;
   wire [1:0]   D2_SIB_S_AG;

   wire 	LD_AG;

   wire [2:0] 	AG_DRID1, AG_DRID2;
   wire 	V_AG_LD_GPR1, V_AG_LD_GPR2, V_AG_LD_SEG, V_AG_LD_CSEG, V_AG_LD_MM;
   wire [2:0] 	ME_DRID1, ME_DRID2;
   wire 	V_ME_LD_GPR1, V_ME_LD_GPR2, V_ME_LD_SEG, V_ME_LD_CSEG, V_ME_LD_MM;
   wire [2:0] 	EX_DRID1, EX_DRID2;
   wire 	V_EX_LD_GPR1, V_EX_LD_GPR2, V_EX_LD_SEG, V_EX_LD_CSEG, V_EX_LD_MM;
   
//*******DECODE STAGE 2*******//
decode_stage2 u_decode_stage2(
    CLK, PRE, CLR,
    IR_OUT, 
    DE_EIP_OUT,
    DE_CS_OUT,
    DE_OPCODE_OUT, 
    DE_PRE_SIZE_OUT,
    DE_PRE_PRES_OUT, DE_SEG_OVR_OUT, DE_OP_OVR_OUT, DE_RE_PRE_OUT, 
    DE_MODRM_PRES_OUT, DE_IMM_PRES_OUT,
    DE_IMM_SIZE_OUT,
    DE_SIB_PRES_OUT, DE_DISP_PRES_OUT, DE_DISP_SIZE_OUT,
    DE_IMM_SEL_OUT,
    DE_DISP_SEL_OUT,
    DE_MODRM_SEL_OUT,
    DE_OFFSET_PRES_OUT,
    DE_OP_SIZE_OUT, 
    DE_OFFSET_SIZE_OUT,
    DE_SEGID_OUT,
    DE_MODRM_OUT, DE_SIB_OUT,

    D2_EIP_OUT, 
    D2_CS_OUT,
    D2_CONTROL_STORE_OUT,
    D2_OFFSET_OUT,
			      
    D2_DATA_SIZE_AG_OUT,
    D2_SR1_NEEDED_AG_OUT, D2_SEG1_NEEDED_AG_OUT, D2_MM1_NEEDED_AG_OUT,

    D2_MEM_RD_ME_OUT, D2_MEM_WR_ME_OUT, 
    D2_ALUK_EX_OUT,
    D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT,

    D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT, D2_SEG1_OUT, D2_SEG2_OUT,
    D2_IMM32_OUT, D2_DISP32_OUT,

    D2_SIB_EN_AG, D2_DISP_EN_AG, D2_BASE_REG_EN_AG,
    D2_MUX_SEG_AG, D2_CMPXCHG_AG,
    D2_SIB_S_AG

);

   wire [31:0] AG_PS_EIP;
   wire [15:0] AG_PS_CS, AG_PS_CS_NC;
   
   wire [127:0] AG_PS_CONTROL_STORE;
   wire [47:0] 	AG_PS_OFFSET;
   
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
   wire [2:0] AG_SR1_OUT, AG_SR2_OUT, AG_SR3_OUT, AG_SIB_I_OUT, AG_SEG1_OUT, AG_SEG2_OUT, AG_MM1_OUT, AG_MM2_OUT;
   wire [1:0] AG_DATA_SIZE_OUT;
   
   // Signals for next stage latches
   wire [31:0] AG_NEIP_OUT;
   wire [15:0] AG_NCS_OUT;
   wire [127:0] AG_CONTROL_STORE_OUT;

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

   reg32e$
      u_reg_ag_ps_eip (CLK, D2_EIP_OUT, AG_PS_EIP, , CLR, PRE, LD_AG),
      u_reg_ag_ps_cs (CLK, {16'b0, D2_CS_OUT}, {AG_PS_CS_NC, AG_PS_CS}, , CLR, PRE, LD_AG);

   reg64e$
      u_reg_ag_ps_control_store0 (CLK, D2_CONTROL_STORE_OUT[127:64], AG_PS_CONTROL_STORE[127:64], , CLR, PRE, LD_AG),
     u_reg_ag_ps_control_store1 (CLK, D2_CONTROL_STORE_OUT[63:0], AG_PS_CONTROL_STORE[63:0], , CLR, PRE, LD_AG);

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
      
   address_generation u_address_generation (CLK, PRE, CLR, NextV,

                                // inputs from pipestage latches
                                AG_PS_EIP, AG_PS_CS, AG_PS_CONTROL_STORE, AG_PS_OFFSET,
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
                                AG_SR1_OUT, AG_SR2_OUT, AG_SR3_OUT, AG_SIB_I_OUT, AG_SEG1_OUT, AG_SEG2_OUT, AG_MM1_OUT, AG_MM2_OUT,
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