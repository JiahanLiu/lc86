module PIPELINE(CLK, CLR, PRE, IR);
   //connect this to simulator
    input CLK, CLR, PRE;
    input [127:0] IR;
    assign EN = 1;//placeholder until stalls are working correctly
   
    wire In_write_ready = 1'b1; //Steven 
   
//*******REGISTER FILE*******//
   wire RST;
   wire [15:0] SEG_DIN;
   wire [2:0] 	SEGID1, SEGID2, WRSEGID;
   wire 	SEGWE;
   wire [63:0] MM_DIN;
   wire [2:0] 	MMID1, MMID2, WRMMID;
   wire 	MMWE;
   wire [31:0] GPR_DIN0, GPR_DIN1, GPR_DIN2;
   wire [2:0] 	GPRID0, GPRID1, GPRID2, GPRID3,	WRGPR0, WRGPR1, WRGPR2;
   wire [1:0] 	GPR_RE0, GPR_RE1, GPR_RE2, GPR_RE3, GPRWE0, GPRWE1, GPRWE2;
   wire WE0, WE1, WE2;     // WRITE ENABLE SIGNALS
   wire [15:0] CS_DIN;
   wire [31:0] EIP_DIN, EFLAGS_DIN;
   wire 	LD_CS, LD_EIP, LD_EFLAGS;
   wire  [15:0] SEGDOUT1, SEGDOUT2;
   wire  [63:0] MMDOUT1, MMDOUT2;
   wire  [31:0] GPRDOUT0, GPRDOUT1, GPRDOUT2, GPRDOUT3;
   wire  [15:0] CSDOUT;
   wire  [31:0] EIPDOUT;
   wire  [31:0] EFLAGSDOUT;
   wire [31:0] SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA;
    wire [2:0] D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT, D2_SEG1_OUT, D2_SEG2_OUT;
    wire [1:0] D2_DATA_SIZE_AG_OUT;

// Make changes to the register file ports in the commented section- TODO
//    register_file u_register_file (CLK, 
//        SEG_DIN, SEGID1, SEGID2, WRSEGID, WB_Final_ld_seg,
//        WB_Final_MM_Data, MMID1, MMID2, WRMMID, WB_Final_ld_mm, 
//        WB_Final_data1, WB_Final_data2, WB_Final_data3,
//        D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT,
//        // For now, all the 4 read datasizes are same
//        2'd2, 2'd2, 2'd2, 2'd2,
//        // D2_DATA_SIZE_AG_OUT, D2_DATA_SIZE_AG_OUT, D2_DATA_SIZE_AG_OUT, D2_DATA_SIZE_AG_OUT,
//        WB_Final_DR1, WB_Final_DR2, WB_Final_DR3, WB_Final_datasize, WB_Final_datasize, WB_Final_datasize,
//        // Enable signals from writeback
//        WB_Final_ld_gpr1, WB_Final_ld_gpr2, WB_Final_ld_gpr3, 
//        CS_DIN, WB_Final_EIP, EFLAGS_DIN,
//        LD_CS, WB_Final_ld_eip, LD_EFLAGS,
//        SEGDOUT1, SEGDOUT2, MMDOUT1, MMDOUT2,
//        SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA,
//        CSDOUT, EIPDOUT, EFLAGSDOUT, CLR
//    );
       

    register_file u_register_file (CLK, 
        SEG_DIN, SEGID1, SEGID2, WRSEGID, SEGWE,
        MM_DIN, MMID1, MMID2, WRMMID, MMWE, 
        GPR_DIN0, GPR_DIN1, GPR_DIN2, 
        D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT,
        // For now, all the 4 read datasizes are same
        2'd2, 2'd2, 2'd2, 2'd2,
        // D2_DATA_SIZE_AG_OUT, D2_DATA_SIZE_AG_OUT, D2_DATA_SIZE_AG_OUT, D2_DATA_SIZE_AG_OUT,
        WRGPR0, WRGPR1, WRGPR2, GPRWE0, GPRWE1, GPRWE2,
        // Enable signals from writeback
        // WE0, WE1, WE2,
        1'b0, 1'b0, 1'b0,
        CS_DIN, EIP_DIN, EFLAGS_DIN,
        LD_CS, LD_EIP, LD_EFLAGS,
        SEGDOUT1, SEGDOUT2, MMDOUT1, MMDOUT2,
        SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA,
        CSDOUT, EIPDOUT, EFLAGSDOUT, CLR
    );

    //*******CACHE FILES*******//
    //Cache file systems to be used by the system
    wire [127:0] IC_DOUT, DC_IN, DC_DOUT;
    wire [31:0] IC_PADDR, DC_PADDR;
    wire IC_EN, DC_WE, IC_R, DC_R;	//IC_EN needs to be included
    //icache u_icache (CLK, RST, IC_PADDR, IC_R, IC_DOUT);
    //dcache u_dcache(CLK, RST, DC_PADDR, DC_DIN, DC_SIZE, DC_WE, DC_R, DC_DOUT);

    wire V_FETCH;
    wire [31:0] FETCH_POINTER;
    wire [4:0] ICACHE_SIZE_OUT;
    wire ICACHE_RW;
    wire ICACHE_RD_STALL;
    wire [127:0] IR_DATA_OUT;
    ifu u_ifu (CLK, CLR, PRE, V_FETCH, FETCH_POINTER, CSDOUT, IC_DOUT, IC_R, IC_PADDR, ICACHE_SIZE_OUT, ICACHE_RW, IC_EN, ICACHE_RD_STALL, IR_DATA_OUT);

    //*******FETCH STAGE*******//
    wire [31:0] FE_EIP_IN;	//this signal should be coming out of WB, does not need a latch
    wire [31:0] FE_JMP_FP, FE_TRAP_FP;//not sure where these signals come from yet
    wire [1:0] FE_FP_MUX;//not sure where this signal comes from yet
    wire FE_LD_EIP;//update the EIP!
    wire FE_SEG_LIM_EXC;//The fetch unit has an exception, needs more support

    wire DE_PRE_PRES_IN, DE_SEG_OVR_IN, DE_OP_OVR_IN, DE_RE_PRE_IN, DE_MODRM_PRES_IN, DE_IMM_PRES_IN, DE_SIB_PRES_IN;
    wire DE_DISP_PRES_IN, DE_DISP_SIZE_IN, DE_OFFSET_PRES_IN, DE_OP_SIZE_IN;
    wire [1:0] DE_IMM_SIZE_IN, DE_OFFSET_SIZE_IN, DE_PRE_SIZE_IN;
    wire [2:0] DE_DISP_SEL_IN, DE_SEGID_IN, DE_MODRM_SEL_IN;
    wire [3:0] DE_IMM_SEL_IN;
    wire [7:0] DE_MODRM_IN, DE_SIB_IN;
    wire [15:0] DE_OPCODE_IN;
    // Placeholder for now
    wire [15:0] DE_CS_IN = 16'h1A;
    wire [31:0] DE_EIP_IN = 32'hA;
    wire [31:0] DE_EIP_OUT, DE_EIP_OUT_BAR;
    wire [127:0] IR_IN;
    //Debug - change reg to wire
    //wire [127:0] IR;
    //reg [127:0] IR = 128'h83c00a00000000000000000000000000;
    wire [3:0] DE_INSTR_LENGTH_UPDT_IN;
    wire [3:0] DE_INSTR_LENGTH_UPDT_OUT; 
    wire [31:0] DE_INSTR_LENGTH_UPDT_OUT_T;

    fetch u_fetch(
        CLK, PRE, CLR, 
        FE_EIP_IN, 
        IC_DOUT, 
        IC_R,
    	      
        FE_JMP_FP, FE_TRAP_FP,
        CSDOUT,
        FE_FP_MUX,
        FE_LD_EIP,
    
        DE_EIP_IN,
        DE_CS_IN,
        IC_EN,
        IC_PADDR,
        FE_SEG_LIM_EXC,
        IR_IN,
        DE_INSTR_LENGTH_UPDT_IN,
        DE_OPCODE_IN,
        DE_PRE_SIZE_IN,
        DE_PRE_PRES_IN,  DE_SEG_OVR_IN,  DE_OP_OVR_IN,  DE_RE_PRE_IN, 
        DE_MODRM_PRES_IN,  DE_IMM_PRES_IN, 
        DE_IMM_SIZE_IN, 
        DE_SIB_PRES_IN,  DE_DISP_PRES_IN,  DE_DISP_SIZE_IN, 
        DE_IMM_SEL_IN, 
        DE_DISP_SEL_IN, 
        DE_OFFSET_PRES_IN, 
        DE_OP_SIZE_IN, 
        DE_OFFSET_SIZE_IN, 
        DE_SEGID_IN, 
        DE_MODRM_IN,  DE_SIB_IN, 
        DE_MODRM_SEL_IN
    
    ); 

    //decode_stage1 u_decode_stage1 (
    //    CLK, PRE, CLR,
    //    IR,
    //    IR_IN,
    //    DE_INSTR_LENGTH_UPDT_IN,
    //    DE_OPCODE_IN,
    //    DE_PRE_SIZE_IN,
    //    DE_PRE_PRES_IN,  DE_SEG_OVR_IN,  DE_OP_OVR_IN,  DE_RE_PRE_IN, 
    //    DE_MODRM_PRES_IN,  DE_IMM_PRES_IN, 
    //    DE_IMM_SIZE_IN, 
    //    DE_SIB_PRES_IN,  DE_DISP_PRES_IN,  DE_DISP_SIZE_IN, 
    //    DE_IMM_SEL_IN, 
    //    DE_DISP_SEL_IN, 
    //    DE_OFFSET_PRES_IN, 
    //    DE_OP_SIZE_IN, 
    //    DE_OFFSET_SIZE_IN, 
    //    DE_SEGID_IN, 
    //    DE_MODRM_IN,  DE_SIB_IN, 
    //    DE_MODRM_SEL_IN
    //);


    //Latches between fetch and decode
    wire [31:0] DE_V_OUT_T, DE_V_OUT_T_BAR, DE_OP_CS_OUT_T, DE_OP_CS_OUT_T_BAR, MOD_SIB_OUT, MOD_SIB_OUT_BAR;	//temp wires
    wire [127:0] IR_OUT, IR_BAR_OUT;
    wire DE_V_IN;
    reg32e$ MOD_SIB(CLK, {16'b0, DE_MODRM_IN, DE_SIB_IN}, MOD_SIB_OUT, MOD_SIB_OUT_BAR, CLR, PRE, EN);
    reg32e$ IR_3(CLK, IR_IN[127:96], IR_OUT[127:96], IR_BAR_OUT[127:96], CLR, PRE, EN);
    reg32e$ IR_2(CLK, IR_IN[95:64], IR_OUT[95:64], IR_BAR_OUT[95:64], CLR, PRE, EN);
    reg32e$ IR_1(CLK, IR_IN[63:32], IR_OUT[63:32], IR_BAR_OUT[63:32], CLR, PRE, EN);
    reg32e$ IR_0(CLK, IR_IN[31:0], IR_OUT[31:0], IR_BAR_OUT[31:0], CLR, PRE, EN);
    reg32e$ DE_EIP(CLK, DE_EIP_IN, DE_EIP_OUT, DE_EIP_OUT_BAR, CLR, PRE, EN);
    reg32e$ DE_V(CLK, {1'b0, DE_DISP_PRES_IN, DE_DISP_SIZE_IN, DE_OFFSET_PRES_IN, DE_OP_SIZE_IN, DE_PRE_PRES_IN, 
                DE_SEG_OVR_IN, DE_OP_OVR_IN, DE_RE_PRE_IN, DE_MODRM_PRES_IN, DE_IMM_PRES_IN, DE_SIB_PRES_IN, 
                DE_IMM_SEL_IN, DE_DISP_SEL_IN, DE_SEGID_IN, DE_MODRM_SEL_IN, DE_IMM_SIZE_IN, DE_OFFSET_SIZE_IN, 
                DE_PRE_SIZE_IN, DE_V_IN}, DE_V_OUT_T, DE_V_OUT_T_BAR, CLR, PRE, EN);	//used for various values 

    reg32e$ DE_OP_CS(CLK, {DE_OPCODE_IN, DE_CS_IN}, DE_OP_CS_OUT_T, DE_OP_CS_OUT_T_BAR, CLR, PRE, EN); 
    reg32e$ INSTR_LENGTH (CLK, {28'b0, DE_INSTR_LENGTH_UPDT_IN}, DE_INSTR_LENGTH_UPDT_OUT_T, ,CLR, PRE, EN);

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
    wire [7:0] DE_MODRM_OUT = MOD_SIB_OUT[15:8];

    wire [15:0] DE_OPCODE_OUT = DE_OP_CS_OUT_T[31:16];
    wire [15:0] DE_CS_OUT = DE_OP_CS_OUT_T[15:0];
    wire [3:0] DE_INSTR_LENGTH_UPDATE_OUT = DE_INSTR_LENGTH_UPDT_OUT_T[3:0];

   // Outputs from Decode Stage 2
    wire [31:0] D2_EIP_OUT;
    wire [15:0] D2_CS_OUT;
    wire [127:0] D2_CONTROL_STORE_OUT;

    wire [47:0] D2_OFFSET_OUT;

    wire D2_SR1_NEEDED_AG_OUT, D2_SEG1_NEEDED_AG_OUT, D2_MM1_NEEDED_AG_OUT, D2_MEM_RD_ME_OUT, D2_MEM_WR_ME_OUT;
    wire [2:0] D2_ALUK_EX_OUT;
    wire D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT;
    wire [31:0] D2_IMM32_OUT, D2_DISP32_OUT;
    wire D2_SIB_EN_AG, D2_DISP_EN_AG, D2_BASE_REG_EN_AG, D2_MUX_SEG_AG, D2_CMPXCHG_AG;
    wire [1:0] D2_SIB_S_AG;

    // Assigned 1 for now - placeholder
    assign LD_AG=1;

    wire [2:0] AG_DRID1, AG_DRID2;
    wire V_AG_LD_GPR1, V_AG_LD_GPR2, V_AG_LD_SEG, V_AG_LD_CSEG, V_AG_LD_MM;
    wire [2:0] ME_DRID1, ME_DRID2;
    wire V_ME_LD_GPR1, V_ME_LD_GPR2, V_ME_LD_SEG, V_ME_LD_CSEG, V_ME_LD_MM;
    wire [2:0] EX_DRID1, EX_DRID2;
    wire V_EX_LD_GPR1, V_EX_LD_GPR2, V_EX_LD_SEG, V_EX_LD_CSEG, V_EX_LD_MM;
   
//*******DECODE STAGE 2*******//
    decode_stage2 u_decode_stage2(
        CLK, PRE, CLR,
        IR_OUT, 
        DE_EIP_OUT,
        DE_CS_OUT,
        DE_INSTR_LENGTH_UPDATE_OUT,
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
   wire [127:0] D2_CONTROL_STORE;
   wire [127:0] AG_PS_CONTROL_STORE_OUT;
   
   wire [31:0] D2_OUT1_AG_PS, D2_OUT2_AG_PS, AG_PS_IN1, AG_PS_IN2;
   wire [31:0] D2_CS_OUT32;

   reg32e$
      u_reg_ag_ps_eip (CLK, D2_EIP_OUT, AG_PS_EIP, , CLR, PRE, LD_AG),
      u_reg_ag_ps_cs (CLK, {16'b0, D2_CS_OUT}, {AG_PS_CS_NC, AG_PS_CS}, , CLR, PRE, LD_AG);

   reg64e$
      u_reg_ag_ps_control_store0 (CLK, D2_CONTROL_STORE_OUT[127:64], AG_PS_CONTROL_STORE[127:64], , CLR, PRE, LD_AG),
     u_reg_ag_ps_control_store1 (CLK, D2_CONTROL_STORE_OUT[63:0], AG_PS_CONTROL_STORE[63:0], , CLR, PRE, LD_AG);

   // [31:2]
   assign D2_OUT1_AG_PS = { 
          D2_DATA_SIZE_AG_OUT, D2_SR1_NEEDED_AG_OUT, D2_SEG1_NEEDED_AG_OUT, D2_MM1_NEEDED_AG_OUT,
          D2_MEM_RD_ME_OUT, D2_MEM_WR_ME_OUT, D2_ALUK_EX_OUT, D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT,
          D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT, D2_SEG1_OUT, D2_SEG2_OUT, 2'b0 };

    wire [63:0] AG_PS_OFFSET_OUT;
    // reg32e$ IR_1(CLK, IR_IN[63:32], IR_OUT[63:32], IR_BAR_OUT[63:32], CLR, PRE, EN);
   reg32e$
      u_reg_ag_ps_in1 (CLK, D2_OUT1_AG_PS, AG_PS_IN1, , CLR, PRE, LD_AG),
      u_reg_ag_ps_imm32 (CLK, D2_IMM32_OUT, AG_PS_IMM32, , CLR, PRE, LD_AG),
      u_reg_ag_ps_disp32 (CLK, D2_DISP32_OUT, AG_PS_DISP32, , CLR, PRE, LD_AG),
      u_reg_ag_ps_offset32 (CLK, D2_OFFSET_OUT[31:0], AG_PS_OFFSET_OUT[31:0], , CLR, PRE, LD_AG),
      u_reg_ag_ps_offset16 (CLK, {16'h0, D2_OFFSET_OUT[47:32]}, AG_PS_OFFSET_OUT[63:32], , CLR, PRE, LD_AG);

    assign AG_PS_OFFSET = AG_PS_OFFSET_OUT[47:0];
     assign { AG_PS_DATA_SIZE, AG_PS_D2_SR1_NEEDED_AG, AG_PS_D2_SEG1_NEEDED_AG, AG_PS_D2_MM1_NEEDED_AG,
            AG_PS_D2_MEM_RD_ME, AG_PS_D2_MEM_WR_ME, AG_PS_D2_ALUK_EX, AG_PS_D2_LD_GPR1_WB, AG_PS_D2_LD_MM_WB,
            AG_PS_SR1, AG_PS_SR2, AG_PS_SR3, AG_PS_SIB_I, AG_PS_SEG1, AG_PS_SEG2 } = AG_PS_IN1[31:2];


   // [31:25]
   assign D2_OUT2_AG_PS[31:25] = { D2_SIB_EN_AG, D2_DISP_EN_AG, D2_BASE_REG_EN_AG, D2_MUX_SEG_AG,
                                   D2_CMPXCHG_AG, D2_SIB_S_AG };
   reg32e$
      u_reg_ag_ps_in2 (CLK, D2_OUT2_AG_PS, AG_PS_IN2, , CLR, PRE, LD_AG);

    assign { AG_PS_DE_SIB_EN_AG, AG_PS_DE_DISP_EN_AG, AG_PS_DE_BASE_REG_EN_AG,
        AG_PS_DE_MUX_SEG_AG, AG_PS_DE_CMPXCHG_AG, AG_PS_DE_SIB_S_AG } = AG_PS_IN2[31:25];
     
endmodule
