module TOP;
//this module is used to debug the basic functionality of the simulator
//the clk cycle used to drive the entire system
reg clk, clr, pre;
integer     clk_cycle = 5;
always  #(clk_cycle)  clk = ~clk;
SIMULATOR u_SIMULATOR(clk, clr, pre);
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

   
   
initial #(29 * clk_cycle) $finish;
initial
begin
	$vcdplusfile("pipeline.dump.vpd");
	$vcdpluson(0, TOP);
end
endmodule

module PIPELINE(CLK, CLR, PRE);
//inputs to this simulator
input CLK, CLR, PRE;
assign EN = 1;//placeholder until stalls are working correctly

//signals from WB
wire [2:0] Out_DR1, Out_DR2, Out_DR3,
wire [31:0] Out_DR1_Data, Out_DR2_Data, Out_DR3_Data, 
wire out_v_de_ld_gpr1_wb, out_v_cs_ld_gpr2_wb, out_v_cs_ld_gpr3_wb,
wire [1:0] out_de_datasize,
wire [31:0] Out_Dcache_Data, Out_Dcache_Address
//*******REGISTER FILE*******//
register_file (CLK, 
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

//*******CACHE FILES*******//
//Cache file systems to be used by the system
wire [127:0] IC_DOUT, DC_IN, DC_DOUT;
wire [31:0] IC_PADDR, DC_PADDR;
wire IC_EN, DC_WE, IC_R, DC_R;	//IC_EN needs to be included
icache u_icache (CLK, RST, IC_PADDR, IC_R, IC_DOUT);
dcache u_dcache(CLK, RST, DC_PADDR, DC_DIN, DC_SIZE, DC_WE, DC_R, DC_DOUT);


 
//*******FETCH STAGE*******//
wire [31:0] FE_EIP_IN;	//this signal should be coming out of WB, does not need a latch
wire [31:0] FE_JMP_FP, FE_TRAP_FP;//not sure where these signals come from yet
wire [1:0] FE_FP_MUX;//not sure where this signal comes from yet
wire FE_LD_EIP;//update the EIP!
wire FE_SEG_LIM_EXC;//The fetch unit has an exception, needs more support

wire DE_PRE_PRES_IN, DE_SEG_OVR_IN, DE_OP_OVR_IN, DE_RE_PRE_IN, DE_MODRM_PRES_IN, DE_IMM_PRES_IN, DE_SIB_PRES_IN;
wire DE_DISP_PRES_IN, DE_DISP_SIZE_IN, DE_OFFSET_PRES_IN, DE_OP_SIZE_IN;
wire [1:0] DE_IMM_SIZE_IN, DE_OFFSET_SIZE, DE_PRE_SIZE_IN;
wire [2:0] DE_DISP_SEL_IN, DE_SEGID_IN, DE_MODRM_SEL_IN;
wire [3:0] DE_IMM_SEL_IN;
wire [7:0] DE_MODRM_IN, DE_SIB_IN;
wire [15:0] DE_OPCODE_IN, DE_CS_IN;
wire [31:0] DE_EIP_IN, DE_EIP_OUT, DE_EIP_OUT_BAR;
wire [127:0] IR_IN;
fetch u_fetch(CLK, PRE, CLR, FE_EIP_IN, IC_DOUT, IC_R,
    FE_JMP_FP, FE_TRAP_FP,
    CSDOUT,
    FE_FP_MUX,
    FE_LD_EIP,

    DE_EIP_IN,
    DE_CS_IN,
    IC_EN,
    IC_PADDR,
    FE_SEG_LIM_EXC,
    IR_IN
);  
    
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
wire DE_SIB_OUT = MOD_SIB_OUT[7:0];
wire DE_MODRM_OUT = MOD_SIB_OUT[15:8];

wire [15:0] DE_OPCODE_OUT = DE_OP_CS_OUT_T[31:16];
wire [15:0] DE_CS_OUT = DE_OP_CS_OUT_T[15:0];

   // Outputs from Decode Stage 2
   wire [31:0]  D2_EIP_OUT;
   wire [15:0]  D2_CS_OUT;
   wire [127:0]  D2_CONTROL_STORE_OUT;
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
     DR, SR, base, index,
     MM_DR, MM_SR,
     seg_SR, seg_DR,
    d2_data_size_AG_OUT, 
     imm, disp,

     operation, MM_operation,
     type_A, MM_type_A,
     type_B, MM_type_B,
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
                          ME_MEM_RD_ADDR_OUT, ME_MEM_WR_ADDR_OUT, ME_DATA_SIZE_OUT, ME_D2_ALUK_EX_OUT,
                          ME_DRID1_OUT, ME_DRID2_OUT, ME_D2_MEM_WR_WB_OUT, ME_D2_LD_GPR1_WB_OUT, ME_D2_LD_MM_WB_OUT);
   
//register between ME and EX
//reg32e$(CLK, Din, Q, QBAR, CLR, PRE,en);
//reg32e$ REG_DEST_COM(CLK, {{31{1'b0}},REG_DEST_COM_IN}, D_REG_DEST, D_3, CLR, PRE, EN);
//EX inputs
wire EX_V_next = 1'b1; // TODO
wire [31:0] EX_V_out; 
reg32e$ u_ex_v_latch(CLK, {{31{1'b0}}, EX_V_next}, EX_V_out, ,CLR,PRE,EN); 
wire EX_V;
assign EX_V = EX_V_out[0]; 

wire [31:0] EX_NEIP_next = ME_NEIP_OUT;
reg32e$ u_ex_neip_latch(CLK, EX_NEIP_next, EX_NEIP, ,CLR,PRE,EN);
wire [31:0] EX_NEIP;

wire [15:0] EX_NCS_next = ME_NCS_OUT;
wire [31:0] EX_NCS_out; 
reg32e$ u_ex_ncs_latch(CLK, {{16{1'b0}}, EX_NCS_next}, EX_NCS_out, ,CLR,PRE,EN); 
wire [15:0] EX_NCS;
assign EX_NCS = EX_NCS_out[15:0]; 

wire [127:0] EX_CONTROL_STORE_next = ME_CONTROL_STORE_OUT;
reg64e$ u_ex_control_store_latch(CLK, EX_CONTROL_STORE_next, EX_CONTROL_STORE, ,CLR,PRE,EN);
wire [127:0] EX_CONTROL_STORE;

wire [1:0] EX_de_datasize_all_next = ME_DATA_SIZE_OUT; 
wire [31:0] EX_de_datasize_all_out;
reg32e$ u_ex_de_datasize_all_all(CLK, EX_de_datasize_all_next, EX_de_datasize_all_out, ,CLR,PRE,EN);
wire [1:0] EX_de_datasize_all;
assign EX_de_datasize_all = EX_de_datasize_all_out[1:0]; 

wire [2:0] EX_de_aluk_ex_next = ME_D2_ALUK_EX_OUT;
wire [31:0] EX_de_aluk_ex_out;
reg32e$ u_ex_de_aluk_ex_latch(CLK, EX_de_aluk_ex_next, EX_de_aluk_ex_out, ,CLR,PRE,EN);
wire [2:0] EX_de_aluk_ex; 
assign EX_de_aluk_ex = EX_de_aluk_ex_out[2:0]; 

wire EX_de_ld_gpr1_wb_next = ME_D2_LD_GPR1_WB_OUT;
wire [31:0] EX_de_ld_gpr1_wb_out;
reg32e$ u_ex_de_aluk_ex_latch(CLK, EX_de_ld_gpr1_wb_next, EX_de_ld_gpr1_wb_out, ,CLR,PRE,EN);
wire EX_de_ld_gpr1_wb;
assign EX_de_ld_gpr1_wb = EX_de_ld_gpr1_wb_out[0]; 

wire EX_de_dcache_write_wb_next = ME_D2_MEM_WR_WB_OUT;
wire [31:0] EX_de_dcache_write_wb_out;
reg32e$ u_ex_de_aluk_ex_latch(CLK, EX_de_dcache_write_wb_next, EX_de_dcache_write_wb_out, ,CLR,PRE,EN);
wire EX_de_dcache_write_wb; 
assign EX_de_dcache_write_wb = EX_de_dcache_write_wb_out[0]; 

   wire [31:0] EX_A_next = ME_A_OUT;
   wire [31:0] EX_B_next = ME_B_OUT;
reg32e$ u_ex_a_latch(CLK, EX_A_next, EX_A, ,CLR,PRE,EN);
reg32e$ u_ex_b_latch(CLK, EX_B_next, EX_B, ,CLR,PRE,EN);
wire [31:0] EX_A, EX_B;

wire [31:0] EX_COUNT_next; 
reg32e$ u_ex_count_latch(CLK, EX_COUNT_next, EX_COUNT, ,CLR,PRE,EN);
wire [31:0] EX_COUNT; 

   wire [63:0] EX_MM_A_next = ME_MM_A_OUT;
   wire [63:0] EX_MM_B_next = ME_MM_B_OUT;
reg64e$ u_ex_mm_a_latch(CLK, EX_MM_A_next, EX_MM_A, ,CLR,PRE,EN);
reg64e$ u_ex_mm_b_latch(CLK, EX_MM_B_next, EX_MM_B, ,CLR,PRE,EN);
wire [63:0] EX_MM_A, EX_MM_B;

wire [31:0] EX_ADDRESS_next = ME_MEM_WR_ADDR_OUT;
reg32e$ u_ex_address_latch(CLK, EX_ADDRESS_next, EX_ADDRESS, ,CLR,PRE,EN);
wire [31:0] EX_ADDRESS;

   wire [2:0] EX_DR1_next = ME_DRID1_OUT;
   wire [2:0] EX_DR2_next = ME_DRID2_OUT;
wire [2:0] EX_DR3_next;
wire [31:0] EX_DR1_out, EX_DR2_out, EX_DR3_out;
reg32e$ u_ex_dr1_latch(CLK, EX_DR1_next, EX_DR1_out, ,CLR,PRE,EN);
reg32e$ u_ex_dr2_latch(CLK, EX_DR2_next, EX_DR2_out, ,CLR,PRE,EN);
reg32e$ u_ex_dr3_latch(CLK, EX_DR3_next, EX_DR3_out, ,CLR,PRE,EN);
wire [2:0] EX_DR1, EX_DR2, EX_DR3;
assign EX_DR1 = EX_DR1_out[2:0]; 
assign EX_DR2 = EX_DR2_out[2:0]; 
assign EX_DR3 = EX_DR3_out[2:0]; 

//EX s

//*******EXECUTE STAGE*******.//

execute u_execute(
  CLK, SET, RST, //not uesd SET/RST

  EX_V,
  EX_NEIP,
  EX_NCS,
  EX_CONTROL_STORE,
  //pseudo-control store signals not from control store but generated in decode
  EX_de_datasize_all,
  EX_de_aluk_ex, 
  EX_de_ld_gpr1_wb,
  EX_de_dcache_write_wb, 

  EX_A, EX_B,
  EX_COUNT, 
  EX_MM_A, EX_MM_B,

  EX_ADDRESS,

  [2:0] EX_DR1, EX_DR2, EX_DR3,

  WB_V_next,
  WB_NEIP_next, 
  WB_NCS_next,
  WB_CONTROL_STORE_next,

  WB_de_datasize_all_next,
  WB_de_aluk_ex_next, 
  WB_de_ld_gpr1_wb_next,
  WB_de_dcache_write_wb_next, 
  WB_de_flags_affected_wb_next,

  WB_ALU32_RESULT_next,
  WB_FLAGS_next,
  WB_CMPS_POINTER_next,
  WB_COUNT_next, 

  WB_DR1_next, WB_DR2_next, WB_DR3_next
)


//register between EX and WB
wire WB_V_next;
wire [31:0] WB_V_out; 
reg32e$ u_wb_v_latch(CLK, {{31{1'b0}}, WB_V_next}, WB_V_out, ,CLR,PRE,EN); 
wire WB_V;
assign WB_V = WB_V_out[0]; 

wire [31:0] WB_NEIP_next;
reg32e$ u_wb_neip_latch(CLK, WB_NEIP_next, WB_NEIP, ,CLR,PRE,EN);
input [31:0] WB_NEIP;

wire [15:0] WB_NCS_next;
reg32e$ u_wb_ncs_latch(CLK, WB_NCS_next, WB_NCS, ,CLR,PRE,EN);
input [15:0] WB_NCS;

wire [63:0] WB_CONTROL_STORE_next;
reg64e$ u_wb_control_store_latch(CLK, WB_CONTROL_STORE_next, WB_CONTROL_STORE, ,CLR,PRE,EN);
input [63:0] WB_CONTROL_STORE;

wire [31:0] WB_ALU32_RESULT_next;
reg32e$ u_wb_alu32_result_latch(CLK, WB_ALU32_RESULT_next, WB_ALU32_RESULTS, ,CLR,PRE,EN);
input [31:0] WB_ALU32_RESULTS;

wire [31:0] WB_FLAGS_next;
reg32e$ u_wb_flags_latch(CLK, WB_FLAGS_next, WB_FLAGS, ,CLR,PRE,EN);
input [31:0] WB_FLAGS;


wire [31:0] WB_CMPS_POINTER_next;
reg32e$ u_wb_cmps_pointer_latch(CLK, WB_CMPS_POINTER_next, WB_CMPS_POINTER, ,CLR,PRE,EN);
wire [31:0] WB_CMPS_POINTER;


wire [31:0] WB_COUNT_next; 
reg32e$ u_wb_count_latch(CLK, WB_COUNT_next, WB_COUNT, ,CLR,PRE,EN);
wire [31:0] WB_COUNT; 

wire [2:0] WB_DR1_next, WB_DR2_next, WB_DR3_next;
wire [2:0] WB_DR1_out, WB_DR2_out, WB_DR3_out;
reg32e$ u_wb_dr1_next_latch(CLK, WB_DR1_next, WB_DR1_out, ,CLR,PRE,EN);
reg32e$ u_wb_dr2_next_latch(CLK, WB_DR2_next, WB_DR2_out, ,CLR,PRE,EN);
reg32e$ u_wb_dr3_next_latch(CLK, WB_DR3_next, WB_DR3_out, ,CLR,PRE,EN);
wire [2:0] WB_DR1, WB_DR2, WB_DR3;
assign WB_DR1 = WB_DR1_next[2:0];
assign WB_DR2 = WB_DR2_next[2:0];
assign WB_DR3 = WB_DR3_next[2:0];

//REPNE CMPS is done
wire Out_ex_repne_termination_all; 

//*******WRITE BACK STAGE*******.//
writeback u_writeback(
    CLK, SET, RST, //not uesd SET/RST

    WB_V,
    WB_NEIP,
    WB_NCS,
    WB_CONTROL_STORE,
   //pseudo-control store signals not from control store but generated in decode
    de_datasize_all,
    de_aluk_ex, 
    de_ld_gpr1_wb,
    de_dcache_write_wb, 

    WB_ALU32_RESULTS,
    WB_COUNT, 
    WB_MM_A, WB_MM_B,
    WB_FLAGS,

    WB_CMPS_POINTER,

    WB_ADDRESS,

    WB_DR1, WB_DR2, WB_DR3,

    Out_DR1, Out_DR2, Out_DR3,
    Out_DR1_Data, Out_DR2_Data, Out_DR3_Data, 
    out_v_de_ld_gpr1_wb, out_v_cs_ld_gpr2_wb, out_v_cs_ld_gpr3_wb,
    out_de_datasize,
    Out_Dcache_Data, Out_Dcache_Address, 
    Out_ex_repne_termination_all
);


endmodule