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


//*******REGISTER FILE*******//
register_file (CLK, 
		      SEG_DIN, SEGID1, SEGID2, WRSEGID, SEGWE,
		      MM_DIN, MMID1, MMID2, WRMMID, MMWE, 
		      GPR_DIN0, GPR_DIN1, GPR_DIN2, 
		      GPRID0, GPRID1, GPRID2, GPRID3,
		      GPR_RE0, GPR_RE1, GPR_RE2, GPR_RE3,
		      WRGPR0, WRGPR1, WRGPR2, GPRWE0, GPRWE1, GPRWE2,
		      CS_DIN, EIP_DIN, EFLAGS_DIN,
		      LD_CS, LD_EIP, LD_EFLAGS,
		      SEGDOUT1, SEGDOUT2, MMDOUT1, MMDOUT2,
		      GPRDOUT0, GPRDOUT1, GPRDOUT2, GPRDOUT3,
		      CSDOUT, EIPDOUT, EFLAGSDOUT);

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

    output [31:0] EIP_OUT, 
    output [15:0] CS_OUT,
    output [31:0] control_store,
    output [2:0] DR, SR, base, index,
    output [2:0] MM_DR, MM_SR,
    output [2:0] seg_SR, seg_DR,
    output [1:0] data_size, 
    output [31:0] imm, disp,

    output operation, MM_operation,
    output type_A, MM_type_A,
    output type_B, MM_type_B,
    output [1:0] D2_DATA_SIZE_AG,
   output D2_SR1_NEEDED_AG, D2_SEG1_NEEDED_AG, D2_MM1_NEEDED_AG,

   output D2_MEM_RD_ME, D2_MEM_WR_ME, 
   output [2:0] D2_ALUK_EX,
   output D2_LD_GPR1_WB, D2_LD_MM_WB,

   output [2:0] SR1_OUT, SR2_OUT, SEG1_OUT, SEG2_OUT,
   output [31:0] IMM32_OUT, DISP32_OUT,

   output DE_SIB_EN_AG, DE_DISP_EN_AG, DE_BASE_REG_EN_AG,
   output DE_MUX_SEG_AG, DE_CMPXCHG_AG,
   output [1:0] DE_SIB_S_AG

);

/*	THIS IS HOW FAR WE HAV DEBUGGED THE BASIC PIPELINE
//Latches between decode and address generation
wire [2:0] AG_SR, AG_DR, AG_BASE, AG_INDEX, AG_MM_SR, AG_MM_DR, AG_SEG_SR, AG_SEG_DR;
wire [1:0] AG_SCALE, AG_DATA_SIZE;
assign AG_REGS_IN = {4'b0000, AG_SR, AG_DR, AG_BASE, AG_INDEX, AG_MM_SR, AG_MM_DR, AG_SEG_DR, AG_SEG_DR, AG_SCALE, AG_DATA_SIZE};
wire [31:0] AG_REGS_OUT, AG_REGS_OUT_BAR;
reg32e$ AG_REGS(CLK, AG_REGS_IN, AG_REGS_OUT, AG_REGS_OUT, CLR, PRE, EN);
wire [31:0] AG_IMM_IN, AG_IMM_OUT, AG_IMM_OUT_BAR, AG_DISP_IN, AG_DISP_OUT, AG_DISP_OUT_BAR;
reg32e$ AG_IMM(CLK, AG_IMM_IN, AG_IMM_OUT, AG_IMM_OUT_BAR, CLR, PRE, EN);
reg32e$ AG_DISP(CLK, AG_DISP_IN, AG_DISP_OUT, AG_DISP_OUT_BAR, CLR, PRE, EN);


//*******ADDRESS GENERATION STAGE*******.//
address_generation u_address_generation(
   input CLK, SET, RST, V,

   // Signals to be saved in pipeline latches
   input [31:0] EIP, 
   input [15:0] CS,
   input [63:0] CONTROL_STORE,

   input [1:0] DATA_SIZE,
   input D2_SR1_NEEDED_AG, D2_SEG1_NEEDED_AG, D2_MM1_NEEDED_AG,

   input D2_MEM_RD_ME, D2_MEM_WR_ME,
   input [2:0] D2_ALUK_EX,
   input D2_LD_GPR1_WB, D2_LD_MM_WB,

   input [2:0] SR1, SR2, SR3, SIB_I, SEG1, SEG2,
   input [31:0] IMM32, DISP32,

   input DE_SIB_EN_AG, DE_DISP_EN_AG, DE_BASE_REG_EN_AG,
   input DE_MUX_SEG_AG, DE_CMPXCHG_AG,
   input [1:0] DE_SIB_S_AG,

   input [31:0] SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA,
   input [15:0] SEG1_DATA, SEG2_DATA,
   input [63:0] MM1_DATA, MM2_DATA,

   input [3:0] DE_EXC_CODE_AG,

   // Dependency check inputs
   input [2:0] AG_DRID1, AG_DRID2,
   input V_AG_LD_GPR1, V_AG_LD_GPR2, V_AG_LD_SEG, V_AG_LD_CSEG, V_AG_LD_MM,

   input [2:0] ME_DRID1, ME_DRID2,
   input V_ME_LD_GPR1, V_ME_LD_GPR2, V_ME_LD_SEG, V_ME_LD_CSEG, V_ME_LD_MM,

   input [2:0] EX_DRID1, EX_DRID2,
   input V_EX_LD_GPR1, V_EX_LD_GPR2, V_EX_LD_SEG, V_EX_LD_CSEG, V_EX_LD_MM,

   // Signals to register file
   output [2:0] SR1_OUT, SR2_OUT, SEG1_OUT, SEG2_OUT, MM1_OUT, MM2_OUT,
   output [1:0] DATA_SIZE_OUT,

   // Signals for next stage latches
   output [31:0] NEIP_OUT, 
   output [15:0] NCS_OUT,
   output [63:0] CONTROL_STORE_OUT,

   output [31:0] A_OUT, B_OUT,
   output [63:0] MM_A_OUT, MM_B_OUT,
   output [31:0] SP_XCHG_DATA_OUT,
   output [31:0] MEM_RD_ADDR_OUT, MEM_WR_ADDR_OUT,

   output [2:0] D2_ALUK_EX_OUT,
   output [2:0] DRID1_OUT, DRID2_OUT,

   output D2_MEM_RD_ME_OUT, D2_MEM_WR_WB_OUT,
   output D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT,

   // Other signals
   output DEP_STALL_OUT, SEG_LIMIT_EXC_OUT
);

//register between AG and ME
wire [31:0] A_BAR_OUT, B_BAR_OUT, A_OUT, B_OUT;
reg32e$ A(CLK, A_IN, A_OUT, A_BAR_OUT, CLR, PRE, EN);
reg32e$ B(CLK, B_IN, B_OUT, B_BAR_OUT, CLR, PRE, EN);
wire [31:0] D_REG_DEST, D_ALUK, D_V_COM, D_1, D_2, D_3;
reg32e$ REG_DEST_COM(CLK, {{31{1'b0}},REG_DEST_COM_IN}, D_REG_DEST, D_3, CLR, PRE, EN);
reg32e$ ALUK_COM(CLK, {{31{1'b0}},ALUK_COM_IN}, D_ALUK, D_1, CLR, PRE, EN);
reg32e$ V_COM(CLK, {{31{1'b0}},V_COM_IN}, D_V_COM, D_2, CLR, PRE, EN);
assign REG_DEST_COM_OUT = D_REG_DEST[0];
assign ALUK_COM_OUT = D_ALUK[0];
assign V_COM_OUT = D_V_COM[0];

//*******MEMORY STAGE*******.//
memory_stage u_memory_stage(
   input CLK, SET, RST,

   input [31:0] NEIP,
   input [15:0] NCS,
   input [63:0] CONTROL_STORE,

   input [31:0] A, B,
   input [63:0] MM_A, MM_B,
   input [31:0] SP_XCHG_DATA,

   input [31:0] MEM_RD_ADDR, MEM_WR_ADDR,
   input [1:0] DATA_SIZE,

   input [2:0] DE_ALUK_EX,
   input [2:0] DRID1, DRID2,

   input D2_MEM_RD_ME, D2_MEM_WR_WB, D2_LD_GPR1_WB, D2_LD_MM_WB,

   // Signals not from latches
   input [63:0] DCACHE_DATA,
   input DCACHE_READY,

   output DCACHE_EN,

   output [31:0] NEIP_OUT,
   output [15:0] NCS_OUT,
   output [63:0] CONTROL_STORE_OUT,

   output [31:0] A_OUT, B_OUT,
   output [63:0] MM_A_OUT, MM_B_OUT,
   output [31:0] SP_XCHG_DATA_OUT,

   output [31:0] MEM_RD_ADDR_OUT, MEM_WR_ADDR_OUT,
   output [1:0] DATA_SIZE_OUT,

   output [2:0] DE_ALUK_EX_OUT,
   output [2:0] DRID1_OUT, DRID2_OUT,

   output D2_MEM_WR_WB_OUT, D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT
);

//register between ME and EX



//*******EXECUTE STAGE*******.//
execute u_execute(
   input CLK, SET, RST,

   input V,
   input [31:0] NEIP,
   input [15:0] NCS,
   input [63:0] CONTROL_STORE,

   input [31:0] A, B,
   input [63:0] MM_A, MM_B,
   input [31:0] SP_XCHG_DATA,

   input [31:0] MEM_WR_ADDR,
   input [1:0] DATA_SIZE,

   input [2:0] DE_ALUK_EX,
   input [2:0] DRID1, DRID2,

   input D2_MEM_WR_WB, D2_LD_GPR1_WB, D2_LD_MM_WB,
   input DF_FLAG,

   output [31:0] NEIP_OUT,
   output [15:0] NCS_OUT,
   output [63:0] CONTROL_STORE_OUT,

   output [31:0] SR1_DATA_OUT,
   output [31:0] ALU_RESULT_OUT,
   output [63:0] MM_RESULT_OUT,
   output [31:0] SP_XCHG_DATA_OUT,

   output [31:0] MEM_WR_ADDR_OUT,
   output [1:0] DATA_SIZE_OUT,

   output [2:0] DE_ALUK_EX_OUT,
   output [2:0] DRID1_OUT, DRID2_OUT,

   output D2_MEM_WR_WB_OUT, D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT
);

//register between EX and WB



//*******WRITE BACK STAGE*******.//
writeback u_writeback(
   input CLK, SET, RST,

   input V,
   input [31:0] NEIP,
   input [15:0] NCS,
   input [63:0] CONTROL_STORE,

   input [31:0] SR1_DATA,
   input [31:0] ALU_RESULT,
   input [63:0] MM_RESULT,
   input [31:0] SP_XCHG_DATA,

   input [31:0] MEM_WR_ADDR,
   input [1:0] DATA_SIZE,

   input [1:0] DE_ALUK_EX,
   input [2:0] DRID1, DRID2,

   input D2_MEM_WR_WB, D2_LD_GPR1_WB, D2_LD_MM_WB,

   input [31:0] EFLAGS_DATA,
   input DCACHE_READY,

   output [31:0] EIP_DATA_OUT,

   output [31:0] SR1_DATA_OUT, SR2_DATA_OUT,
   output [63:0] MM_DATA_OUT,
   output [15:0] SEG_DATA_OUT, CSEG_DATA_OUT,
   output [63:0] MEM_DATA_OUT,

   output [1:0] DATA_SIZE_OUT,
   output [2:0] DRID1_OUT, DRID2_OUT,

   output V_LD_EIP, V_LD_CSEG, V_LD_GPR1, V_LD_GPR2,
   output V_LD_SEG, V_LD_MM, 

   output V_MEM_WR, WB_STALL
);
*/

endmodule