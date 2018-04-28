`timescale 1ns/1ps
`define EOF = 32'hFFFF_FFFF
`define NULL 0
`define default_mem_Value 32'h12

`define assert(signal, value) \
        if (signal !== value) begin \
            $display("ASSERTION FAILED in %m: signal != value"); \
            $finish; \
        end

module TOP;
//this module is used to debug the basic functionality of the simulator
//the clk cycle used to drive the entire system
   reg error = 0;

   reg clk, clr, pre;
   reg [127:0] IR;
   integer clk_cycle = 10;
   integer half_cycle = 5;

   // Signals for testbench loop
   integer file, char, retval, lineno, cntErrors;
   reg [15:0] opcode;
   reg [31:0] result;
   reg [7:0] prefix1, prefix2, prefix3, modrm, sib;
   reg [31:0] disp, imm;
   reg [47:0] offset, offset_compare;
   reg prefix1_present, prefix2_present, prefix3_present, sib_present, modrm_present;
   reg [1:0] opcode_size, prefix_size;
   reg disp_present, imm_present, prefix_present, offset_present;
   reg [2:0] disp_size, imm_size, offset_size;
   reg [3:0] instr_length;
   reg opcode_size_en, disp_size_en;
   reg [1:0] imm_size_en, offset_size_en;
   reg imm_size8, imm_size16, imm_size32;         
   reg offset_size8, offset_size16, offset_size32, offset_size48;
   reg operand_override;
   integer j=14;

    reg [31:0] EIP_UPDATE;
    // Internal reg/wires
    //signals from EX to Dependency Checks
    reg DEP_v_ex_ld_gpr1;
    reg DEP_v_ex_ld_gpr2;
    reg DEP_v_ex_ld_gpr3;
    reg Dep_v_ex_ld_seg;
    reg Dep_v_ex_ld_mm;
    reg Dep_v_ex_dcache_write;
    //signals from WB to Dependency Checks
    reg DEP_v_wb_ld_gpr1;
    reg DEP_v_wb_ld_gpr2;
    reg DEP_v_wb_ld_gpr3;
    reg DEP_v_wb_ld_seg;
    reg DEP_v_wb_ld_mm;
    reg DEP_v_wb_dcache_write;
    //signals from WB to dcache
    reg [2:0] WB_Final_DR1;
    reg [2:0] WB_Final_DR2;
    reg [2:0] WB_Final_DR3;
    reg [31:0] WB_Final_data1;
    reg [31:0] WB_Final_data2;
    reg [31:0] WB_Final_data3;
    reg WB_Final_ld_gpr1;
    reg WB_Final_ld_gpr2;
    reg WB_Final_ld_gpr3;
    reg [1:0] WB_Final_datasize;
    reg WB_Final_ld_seg; 
    reg [63:0] WB_Final_MM_Data;
    reg WB_Final_ld_mm; 
    reg [31:0] WB_Final_EIP; 
    reg WB_Final_ld_eip; 
    reg [63:0] WB_Final_Dcache_Data;
    reg [31:0] WB_Final_Dcache_address;
    //signals from d-cache needed by WB
    //WB outputs
    reg wb_halt_all;
    reg wb_repne_terminate_all;
    reg WB_stall;
    //Dataforwarded, currently for daa
    reg CF_dataforwarded;
    reg AF_dataforwarded; 

    //*******REGISTER FILE*******//
    reg RST;
    reg [15:0] SEG_DIN;
    reg [2:0]   SEGID1, SEGID2, WRSEGID;
    reg   SEGWE;
    reg [63:0] MM_DIN;
    reg [2:0]   MMID1, MMID2, WRMMID;
    reg   MMWE;
    reg [31:0] GPR_DIN0, GPR_DIN1, GPR_DIN2;
    reg [2:0]   GPRID0, GPRID1, GPRID2, GPRID3, WRGPR0, WRGPR1, WRGPR2;
    reg [1:0]   GPR_RE0, GPR_RE1, GPR_RE2, GPR_RE3, GPRWE0, GPRWE1, GPRWE2;
    reg WE0, WE1, WE2;     // WRITE ENABLE SIGNALS
    reg [15:0] CS_DIN;
    reg [31:0] EIP_DIN, EFLAGS_DIN;
    reg   LD_CS, LD_EIP, LD_EFLAGS;
    reg  [15:0] SEGDOUT1, SEGDOUT2;
    reg  [63:0] MMDOUT1, MMDOUT2;
    reg  [31:0] GPRDOUT0, GPRDOUT1, GPRDOUT2, GPRDOUT3;
    reg  [15:0] CSDOUT;
    reg  [31:0] EIPDOUT;
    reg  [31:0] EFLAGSDOUT;
    reg [31:0] SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA;
    reg [2:0] D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT, D2_SEG1_OUT, D2_SEG2_OUT;
    reg [1:0] D2_DATA_SIZE_AG_OUT;

    //*******CACHE FILES*******//
    //Cache file systems to be used by the system
    reg [127:0] IC_DOUT, DC_IN, DC_DOUT;
    reg [31:0] IC_PADDR, DC_PADDR;
    reg IC_EN, DC_WE, IC_R, DC_R; //IC_EN needs to be included

    //*******FETCH STAGE*******//
    reg [31:0] FE_EIP_IN; //this signal should be coming out of WB, does not need a latch
    reg [31:0] FE_JMP_FP, FE_TRAP_FP;//not sure where these signals come from yet
    reg [1:0] FE_FP_MUX;//not sure where this signal comes from yet
    reg FE_LD_EIP;//update the EIP!
    reg FE_SEG_LIM_EXC;//The fetch unit has an exception, needs more support

    reg DE_PRE_PRES_IN, DE_SEG_OVR_IN, DE_OP_OVR_IN, DE_RE_PRE_IN, DE_MODRM_PRES_IN, DE_IMM_PRES_IN, DE_SIB_PRES_IN;
    reg DE_DISP_PRES_IN, DE_DISP_SIZE_IN, DE_OFFSET_PRES_IN, DE_OP_SIZE_IN;
    reg [1:0] DE_IMM_SIZE_IN, DE_OFFSET_SIZE_IN, DE_PRE_SIZE_IN;
    reg [2:0] DE_DISP_SEL_IN, DE_SEGID_IN, DE_MODRM_SEL_IN;
    reg [3:0] DE_IMM_SEL_IN;
    reg [7:0] DE_MODRM_IN, DE_SIB_IN;
    reg [15:0] DE_OPCODE_IN, DE_CS_IN;
    reg [31:0] DE_EIP_IN, DE_EIP_OUT, DE_EIP_OUT_BAR;
    reg [127:0] IR_IN;
    reg [3:0] DE_INSTR_LENGTH_UPDT_IN; 

    //Latches between fetch and decode
    reg [31:0] DE_V_OUT_T, DE_V_OUT_T_BAR, DE_OP_CS_OUT_T, DE_OP_CS_OUT_T_BAR, MOD_SIB_OUT, MOD_SIB_OUT_BAR;  //temp wires
    reg [127:0] IR_OUT, IR_BAR_OUT;
    reg DE_V_IN;

    reg DE_V_OUT;
    reg [1:0] DE_PRE_SIZE_OUT;
    reg [1:0] DE_OFFSET_SIZE_OUT;
    reg [1:0] DE_IMM_SIZE_OUT;
    reg [2:0] DE_MODRM_SEL_OUT;
    reg [2:0] DE_SEGID_OUT;
    reg [2:0] DE_DISP_SEL_OUT;
    reg [3:0] DE_IMM_SEL_OUT;
    reg DE_SIB_PRES_OUT;
    reg DE_IMM_PRES_OUT;
    reg DE_MODRM_PRES_OUT;
    reg DE_RE_PRE_OUT;
    reg DE_OP_OVR_OUT;
    reg DE_SEG_OVR_OUT;
    reg DE_PRE_PRES_OUT;
    reg DE_OP_SIZE_OUT;
    reg DE_OFFSET_PRES_OUT;
    reg DE_DISP_SIZE_OUT;
    reg DE_DISP_PRES_OUT;
    reg [7:0] DE_SIB_OUT;
    reg [7:0] DE_MODRM_OUT;

    reg [15:0] DE_OPCODE_OUT;
    reg [15:0] DE_CS_OUT;

    // Outputs from Decode Stage 2
    reg [31:0] D2_EIP_OUT;
    reg [15:0] D2_CS_OUT;
    reg [127:0] D2_CONTROL_STORE_OUT;

    reg [47:0] D2_OFFSET_OUT;

    reg D2_SR1_NEEDED_AG_OUT, D2_SEG1_NEEDED_AG_OUT, D2_MM1_NEEDED_AG_OUT, D2_MEM_RD_ME_OUT, D2_MEM_WR_ME_OUT;
    reg [2:0] D2_ALUK_EX_OUT;
    reg D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT;
    reg [31:0] D2_IMM32_OUT, D2_DISP32_OUT;
    reg D2_SIB_EN_AG, D2_DISP_EN_AG, D2_BASE_REG_EN_AG, D2_MUX_SEG_AG, D2_CMPXCHG_AG;
    reg [1:0] D2_SIB_S_AG;

    reg [2:0] AG_DRID1, AG_DRID2;
    reg V_AG_LD_GPR1, V_AG_LD_GPR2, V_AG_LD_SEG, V_AG_LD_CSEG, V_AG_LD_MM;
    reg [2:0] ME_DRID1, ME_DRID2;
    reg V_ME_LD_GPR1, V_ME_LD_GPR2, V_ME_LD_SEG, V_ME_LD_CSEG, V_ME_LD_MM;
    reg [2:0] EX_DRID1, EX_DRID2;
    reg V_EX_LD_GPR1, V_EX_LD_GPR2, V_EX_LD_SEG, V_EX_LD_CSEG, V_EX_LD_MM;

   reg [31:0] AG_PS_EIP;
   reg [15:0] AG_PS_CS, AG_PS_CS_NC;
   
   reg [127:0] AG_PS_CONTROL_STORE;
   reg [47:0]   AG_PS_OFFSET;
   
   reg [1:0] AG_PS_DATA_SIZE;
   reg AG_PS_D2_SR1_NEEDED_AG, AG_PS_D2_SEG1_NEEDED_AG, AG_PS_D2_MM1_NEEDED_AG;

   reg AG_PS_D2_MEM_RD_ME, AG_PS_D2_MEM_WR_ME;
   reg [2:0] AG_PS_D2_ALUK_EX;
   reg AG_PS_D2_LD_GPR1_WB, AG_PS_D2_LD_MM_WB;

   reg [2:0] AG_PS_SR1, AG_PS_SR2, AG_PS_SR3, AG_PS_SIB_I, AG_PS_SEG1, AG_PS_SEG2;
   reg [31:0] AG_PS_IMM32, AG_PS_DISP32;

   reg AG_PS_DE_SIB_EN_AG, AG_PS_DE_DISP_EN_AG, AG_PS_DE_BASE_REG_EN_AG;
   reg AG_PS_DE_MUX_SEG_AG, AG_PS_DE_CMPXCHG_AG;
   reg [1:0] AG_PS_DE_SIB_S_AG;

   reg [15:0] SEG1_DATA, SEG2_DATA;
   reg [63:0] MM1_DATA, MM2_DATA;

   reg [3:0] DE_EXC_CODE_AG;

   // Signals to register file
   reg [2:0] AG_SR1_OUT, AG_SR2_OUT, AG_SR3_OUT, AG_SIB_I_OUT, AG_SEG1_OUT, AG_SEG2_OUT, AG_MM1_OUT, AG_MM2_OUT;
   reg [1:0] AG_DATA_SIZE_OUT;
   
   // Signals for next stage latches
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
   reg        AG_DEP_STALL_OUT, AG_SEG_LIMIT_EXC_OUT;
   reg [127:0] D2_CONTROL_STORE;
   reg [127:0] AG_PS_CONTROL_STORE_OUT;
   
   reg [31:0] D2_OUT1_AG_PS, D2_OUT2_AG_PS, AG_PS_IN1, AG_PS_IN2;
   reg [31:0] D2_CS_OUT32;
   reg NextV;
   reg [31:0] ME_PS_NEIP;
   reg [15:0] ME_PS_NCS, ME_PS_NCS_NC;
   reg [127:0] ME_PS_CONTROL_STORE;
   reg [127:0] ME_PS_CONTROL_STORE_OUT;

   reg [31:0] ME_PS_A, ME_PS_B;
   reg [63:0] ME_PS_MM_A, ME_PS_MM_B;
   reg [31:0] ME_PS_SP_XCHG_DATA;

   reg [31:0] ME_PS_MEM_RD_ADDR, ME_PS_MEM_WR_ADDR;
   reg [1:0] ME_PS_DATA_SIZE;

   reg [2:0] ME_PS_D2_ALUK_EX;
   reg [2:0] ME_PS_DRID1, ME_PS_DRID2;

   reg ME_PS_D2_MEM_RD_ME, ME_PS_D2_MEM_WR_WB, ME_PS_D2_LD_GPR1_WB, ME_PS_D2_LD_MM_WB;

   // Signals not from latches
   reg [63:0] DCACHE_DATA;
   reg DCACHE_READY;

   reg ME_DCACHE_EN;

   reg [31:0] ME_NEIP_OUT;
   reg [15:0] ME_NCS_OUT;
   reg [127:0] ME_CONTROL_STORE_OUT;

   reg [31:0] ME_A_OUT, ME_B_OUT;
   reg [63:0] ME_MM_A_OUT, ME_MM_B_OUT;
   reg [31:0] ME_SP_XCHG_DATA_OUT;

   reg [31:0] ME_MEM_RD_ADDR_OUT, ME_MEM_WR_ADDR_OUT;
   reg [1:0] ME_DATA_SIZE_OUT;

   reg [2:0] ME_D2_ALUK_EX_OUT;
   reg [2:0] ME_DRID1_OUT, ME_DRID2_OUT;

   reg ME_D2_MEM_WR_WB_OUT, ME_D2_LD_GPR1_WB_OUT, ME_D2_LD_MM_WB_OUT;

   reg [31:0] AG_OUT1_ME_PS, ME_PS_IN1;
   reg [31:0] AG_NCS_OUT32;
   reg [127:0] AG_CONTROL_STORE;

   //EX Inputs
    reg EX_V;
    reg [31:0] EX_NEIP;
    reg [15:0] EX_NCS;    
    reg [127:0] EX_CONTROL_STORE;

    reg [1:0] EX_de_datasize_all;
    reg [2:0] EX_de_aluk_ex; 
    reg EX_de_shift_dir_ex;
    reg EX_de_ld_gpr1_ex;
    reg EX_de_dcache_write_ex; 
    reg EX_de_repne_wb; 
    reg [31:0] EX_A, EX_B, EX_C;
    reg [63:0] EX_MM_A, EX_MM_B;
    reg [2:0] EX_DR1, EX_DR2, EX_DR3;
    reg [31:0] EX_ADDRESS;

    //register between EX and WB
    reg WB_V; 
    reg [31:0] WB_NEIP;
    reg [15:0] WB_NCS;
    reg [127:0] WB_CONTROL_STORE;

    reg [1:0] WB_de_datasize_all; 
    reg WB_ex_ld_gpr1_wb; 
    reg WB_ex_ld_gpr2_wb; 
    reg WB_ex_dcache_write_wb; 
    reg WB_de_repne_wb; 

    reg [31:0] WB_RESULT_A;
    reg [31:0] WB_RESULT_B;
    reg [31:0] WB_RESULT_C;
    reg [31:0] WB_FLAGS;
    reg [63:0] WB_RESULT_MM; 
    reg [2:0] WB_DR1, WB_DR2, WB_DR3;
    reg [31:0] WB_ADDRESS; 


   PIPELINE u_pipeline(clk, clr, pre, IR);

   initial begin
        clk = 0;
        clr = 1;
        pre = 0;
        repeat(2) #clk_cycle //wait 2 clock cycles
        pre = 1;
        forever #(half_cycle)  clk = ~clk;
    end

    // Set the register values
    // reg0 = 32'08000823
    // reg1 = 32'09010901
    // reg2 = 32'0A020A02
    // reg3 = 32'0B030B03
    // reg4 = 32'0C040C04
    // reg5 = 32'0D050D05
    // reg6 = 32'0E060E06
    // reg7 = 32'0F070F07
    initial begin
        u_pipeline.u_register_file.gpr.reg0_ll.Q = 32'h23;
        u_pipeline.u_register_file.gpr.reg1_ll.Q = 32'h1;
        u_pipeline.u_register_file.gpr.reg2_ll.Q = 32'h2;
        u_pipeline.u_register_file.gpr.reg3_ll.Q = 32'h3;
        u_pipeline.u_register_file.gpr.reg4_ll.Q = 32'h4;
        u_pipeline.u_register_file.gpr.reg5_ll.Q = 32'h5;
        u_pipeline.u_register_file.gpr.reg6_ll.Q = 32'h6;
        u_pipeline.u_register_file.gpr.reg7_ll.Q = 32'h7;

        u_pipeline.u_register_file.gpr.reg0_lh.Q = 32'h800;
        u_pipeline.u_register_file.gpr.reg1_lh.Q = 32'h900;
        u_pipeline.u_register_file.gpr.reg2_lh.Q = 32'hA00;
        u_pipeline.u_register_file.gpr.reg3_lh.Q = 32'hB00;
        u_pipeline.u_register_file.gpr.reg4_lh.Q = 32'hC00;
        u_pipeline.u_register_file.gpr.reg5_lh.Q = 32'hD00;
        u_pipeline.u_register_file.gpr.reg6_lh.Q = 32'hE00;
        u_pipeline.u_register_file.gpr.reg7_lh.Q = 32'hF00;

        u_pipeline.u_register_file.gpr.reg0_hl.Q = 32'h00000;
        u_pipeline.u_register_file.gpr.reg1_hl.Q = 32'h10000;
        u_pipeline.u_register_file.gpr.reg2_hl.Q = 32'h20000;
        u_pipeline.u_register_file.gpr.reg3_hl.Q = 32'h30000;
        u_pipeline.u_register_file.gpr.reg4_hl.Q = 32'h40000;
        u_pipeline.u_register_file.gpr.reg5_hl.Q = 32'h50000;
        u_pipeline.u_register_file.gpr.reg6_hl.Q = 32'h60000;
        u_pipeline.u_register_file.gpr.reg7_hl.Q = 32'h70000;

        u_pipeline.u_register_file.gpr.reg0_hh.Q = 32'h8000000;
        u_pipeline.u_register_file.gpr.reg1_hh.Q = 32'h9000000;
        u_pipeline.u_register_file.gpr.reg2_hh.Q = 32'hA000000;
        u_pipeline.u_register_file.gpr.reg3_hh.Q = 32'hB000000;
        u_pipeline.u_register_file.gpr.reg4_hh.Q = 32'hC000000;
        u_pipeline.u_register_file.gpr.reg5_hh.Q = 32'hD000000;
        u_pipeline.u_register_file.gpr.reg6_hh.Q = 32'hE000000;
        u_pipeline.u_register_file.gpr.reg7_hh.Q = 32'hF000000;

        u_pipeline.u_register_file.segr.regfilelo.mem_array[0] = 8'h0;
        u_pipeline.u_register_file.segr.regfilelo.mem_array[1] = 8'h1;
        u_pipeline.u_register_file.segr.regfilelo.mem_array[2] = 8'h2;
        u_pipeline.u_register_file.segr.regfilelo.mem_array[3] = 8'h3;
        u_pipeline.u_register_file.segr.regfilelo.mem_array[4] = 8'h4;
        u_pipeline.u_register_file.segr.regfilelo.mem_array[5] = 8'h5;
        u_pipeline.u_register_file.segr.regfilelo.mem_array[6] = 8'h6;
        u_pipeline.u_register_file.segr.regfilelo.mem_array[7] = 8'h7;

        u_pipeline.u_register_file.segr.regfilehi.mem_array[0] = 8'h0;
        u_pipeline.u_register_file.segr.regfilehi.mem_array[1] = 8'h1;
        u_pipeline.u_register_file.segr.regfilehi.mem_array[2] = 8'h2;
        u_pipeline.u_register_file.segr.regfilehi.mem_array[3] = 8'h3;
        u_pipeline.u_register_file.segr.regfilehi.mem_array[4] = 8'h4;
        u_pipeline.u_register_file.segr.regfilehi.mem_array[5] = 8'h5;
        u_pipeline.u_register_file.segr.regfilehi.mem_array[6] = 8'h6;
        u_pipeline.u_register_file.segr.regfilehi.mem_array[7] = 8'h7;

        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilehi.mem_array[0] = 8'h0;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilehi.mem_array[1] = 8'h1;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilehi.mem_array[2] = 8'h2;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilehi.mem_array[3] = 8'h3;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilehi.mem_array[4] = 8'h4;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilehi.mem_array[5] = 8'h5;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilehi.mem_array[6] = 8'h6;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilehi.mem_array[7] = 8'h7;

        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilelo.mem_array[0] = 8'h0;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilelo.mem_array[1] = 8'h1;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilelo.mem_array[2] = 8'h2;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilelo.mem_array[3] = 8'h3;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilelo.mem_array[4] = 8'h4;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilelo.mem_array[5] = 8'h5;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilelo.mem_array[6] = 8'h6;
        u_pipeline.u_register_file.mmr.regfilehi.regfilehi.regfilelo.mem_array[7] = 8'h7;

        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilehi.mem_array[0] = 8'h0;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilehi.mem_array[1] = 8'h1;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilehi.mem_array[2] = 8'h2;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilehi.mem_array[3] = 8'h3;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilehi.mem_array[4] = 8'h4;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilehi.mem_array[5] = 8'h5;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilehi.mem_array[6] = 8'h6;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilehi.mem_array[7] = 8'h7;

        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilelo.mem_array[0] = 8'h0;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilelo.mem_array[1] = 8'h1;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilelo.mem_array[2] = 8'h2;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilelo.mem_array[3] = 8'h3;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilelo.mem_array[4] = 8'h4;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilelo.mem_array[5] = 8'h5;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilelo.mem_array[6] = 8'h6;
        u_pipeline.u_register_file.mmr.regfilehi.regfilelo.regfilelo.mem_array[7] = 8'h7;

        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilehi.mem_array[0] = 8'h0;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilehi.mem_array[1] = 8'h1;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilehi.mem_array[2] = 8'h2;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilehi.mem_array[3] = 8'h3;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilehi.mem_array[4] = 8'h4;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilehi.mem_array[5] = 8'h5;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilehi.mem_array[6] = 8'h6;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilehi.mem_array[7] = 8'h7;

        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilelo.mem_array[0] = 8'h0;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilelo.mem_array[1] = 8'h1;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilelo.mem_array[2] = 8'h2;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilelo.mem_array[3] = 8'h3;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilelo.mem_array[4] = 8'h4;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilelo.mem_array[5] = 8'h5;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilelo.mem_array[6] = 8'h6;
        u_pipeline.u_register_file.mmr.regfilelo.regfilehi.regfilelo.mem_array[7] = 8'h7;

        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilehi.mem_array[0] = 8'h0;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilehi.mem_array[1] = 8'h1;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilehi.mem_array[2] = 8'h2;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilehi.mem_array[3] = 8'h3;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilehi.mem_array[4] = 8'h4;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilehi.mem_array[5] = 8'h5;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilehi.mem_array[6] = 8'h6;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilehi.mem_array[7] = 8'h7;

        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilelo.mem_array[0] = 8'h0;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilelo.mem_array[1] = 8'h1;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilelo.mem_array[2] = 8'h2;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilelo.mem_array[3] = 8'h3;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilelo.mem_array[4] = 8'h4;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilelo.mem_array[5] = 8'h5;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilelo.mem_array[6] = 8'h6;
        u_pipeline.u_register_file.mmr.regfilelo.regfilelo.regfilelo.mem_array[7] = 8'h7;


        u_pipeline.u_register_file.eip.Q = 32'h01;
        u_pipeline.u_register_file.segr_cs.Q = 32'h1A;
        u_pipeline.u_register_file.eflags.Q = 32'h01;
        u_pipeline.u_writeback.u_flags_wb.u_flags_register.Q = 32'h01; //internal flags register
     end 

     initial begin
         // file format
         // prefix1 prefix2 prefix3 opcode modrm sib disp imm offset
         file = $fopen("instruction_trace", "r");
         if (file == `NULL) begin
             $stop;
         end

         @(posedge pre);
         #(half_cycle)
        char = $fgetc(file);
        
           // Initializing the sizes every time to zero
           j = 15; 
           IR = 128'h0;
           prefix_size = 0;
           opcode_size = 1;
           imm_size = 0;
           disp_size = 0;
           offset_size = 0;
           opcode_size_en = 0;
           imm_size_en = 0;
           disp_size_en = 0;
           offset_size_en = 0;
            prefix_present = 0;
            operand_override =0;

           retval = $ungetc(char, file); // push back the non-EOF char

           // retval = $fscanf(file, "%h %h %h %h %h %h %h %h", prefix1, prefix2, prefix3,
           //     opcode, modrm, sib, disp, imm);
           retval = $fscanf(file, "%h %h", prefix1, opcode);
           char = $fgetc(file); // eats newline

          // $display ("Time: %0d, OPCODE: %h", $time, opcode);
           
           if(prefix1 == 16'h66) begin
               prefix_present = 1;
               prefix_size = 1;
               operand_override = 1;
               IR[8*j +: 8] = prefix1;
               j = j-1;
           end

           if(opcode[15:8] == 8'h0F) begin
               j= j-1;
               IR[8*j +: 16] = opcode;
               opcode_size =2;
               opcode_size_en=1;
           end else begin
               IR[8*j +: 8] = opcode[7:0];
               opcode_size =1;
               opcode_size_en=0;
           end
//           //$display ("Time: %0d IR = %h", $time, IR[127:112]);

           modrm_present = (opcode==16'h0081) || (opcode==16'h0083) || (opcode==16'h0001) || (opcode==16'h0000) || (opcode==16'h0002) || 
            (opcode==16'h0003) || (opcode==16'h0008) || (opcode==16'h0009) || (opcode==16'h000A) || (opcode==16'h000B) || 
            (opcode==16'h0F42) || (opcode==16'h0F6F) || (opcode==16'h0F70) || (opcode==16'h0F7F) || (opcode==16'h0FB0) ||
            (opcode==16'h0FB1) || (opcode==16'h0FED) || (opcode==16'h0FFD) || (opcode==16'h0FFE) || (opcode==16'h0020) ||
            (opcode==16'h0021) || (opcode==16'h0022) || (opcode==16'h0023) || (opcode==16'h0080) || (opcode==16'h0086) ||
            (opcode==16'h0087) || (opcode==16'h0088) || (opcode==16'h0089) || (opcode==16'h008A) || (opcode==16'h008B) ||
            (opcode==16'h008C) || (opcode==16'h008E) || (opcode==16'h008F) || (opcode==16'h00C0) || (opcode==16'h00C1) ||
            (opcode==16'h00C6) || (opcode==16'h00C7) || (opcode==16'h00D0) || (opcode==16'h00D1) || (opcode==16'h00D1) ||
            (opcode==16'h00D2) || (opcode==16'h00D3) || (opcode==16'h00F6) || (opcode==16'h00F7) || (opcode==16'h00FE) ||
            (opcode==16'h00FF);

            if(modrm_present == 1'b1) begin 
                //modrm = {$random};
                modrm = 32'b10010101; //95
                j=j-1;
                IR[8*j +: 8] = modrm;
//                $display ("Time: %0d MODRM = %h", $time, modrm);
            end

            sib_present = modrm_present && (((modrm[7:6]==2'b00) || (modrm[7:6]==2'b01) || (modrm[7:6]==2'b10)) && (modrm[2:0]==3'b100)); 

            if(sib_present == 1'b1) begin
                sib = {$random};
                j=j-1;
                IR[8*j +: 8] = sib;
//                $display ("Time: %0d SIB = %h", $time, sib);
            end

            disp_present = modrm_present && ((modrm[7:6]==2'b01) || (modrm[7:6]==2'b10) || ((modrm[7:6]==2'b00) && (modrm[2:0]==3'b101)));

            if(modrm_present && (modrm[7:6]==2'b01)) 
                disp_size=1;

            if(disp_present == 1'b1) begin
                if(disp_size==1) begin
                    j=j-1;
                    //disp[7:0] = {$random};
                    disp = 32'h0A000000;
                    IR[8*j +: 8] = disp[7:0];
                    disp_size_en=1;
//                    $display ("Time: %0 DISP = %h", $time, disp[7:0]);
                end else begin
                    j=j-4;
                    //disp = {$random};
                    disp_size = 4;
                    disp = 32'h0A000000;
                    IR[8*j +: 32] = disp; 
                    disp_size_en=0;
//                    $display ("Time: %0 DISP = %h", $time, disp);
                end
            end
            

            imm_size8 = (opcode==16'h04) || (opcode==16'h0C) || (opcode==16'h0F70) || (opcode==16'h24) || (opcode==16'h6A) || 
            (opcode==16'h80) || (opcode==16'h83) || (opcode==16'hB0) || (opcode==16'hB1) || (opcode==16'hB2) ||
            (opcode==16'hB3) || (opcode==16'hB4) || (opcode==16'hB5) || (opcode==16'hB6) || (opcode==16'hB7) ||
            (opcode==16'hC0) || (opcode==16'hC1) || (opcode==16'hC6);

            imm_size16 = (opcode==16'hC2) || (opcode==16'hCA) || 
            (operand_override && ((opcode==16'h68) || (opcode==16'h05) || (opcode==16'h0D) || (opcode==16'h25) || 
            (opcode==16'h81) || (opcode==16'hB8) || (opcode==16'hB9) || (opcode==16'hBA) || (opcode==16'hBB) ||
            (opcode==16'hBC) || (opcode==16'hBD) || (opcode==16'hBE) || (opcode==16'hBF) || (opcode==16'hC7)));

            imm_size32 = !operand_override && ((opcode==16'h68) || (opcode==16'h05) || (opcode==16'h0D) || (opcode==16'h25) || 
            (opcode==16'h81) || (opcode==16'hB8) || (opcode==16'hB9) || (opcode==16'hBA) || (opcode==16'hBB) ||
            (opcode==16'hBC) || (opcode==16'hBD) || (opcode==16'hBE) || (opcode==16'hBF) || (opcode==16'hC7));
                
            imm_present = imm_size8 | imm_size16 | imm_size32;

            if(imm_size8) begin
                imm[7:0] = {$random};
                imm[7:0] = 31'h75;
                j=j-1;
                imm_size = 1;
                imm_size_en = 0;
                IR[8*j +: 8] = imm[7:0];
//                $display ("Time: %0d IMM = %h", $time, imm[7:0]);
            end else if(imm_size16) begin
                imm[15:0] = {$random};
                imm[15:0] = 31'h5462;
                j=j-2;
                imm_size = 2;
                imm_size_en = 1;
                IR[8*j +: 16] = imm[15:0];
//                $display ("Time: %0d IMM = %h", $time, imm[15:0]);
            end else if(imm_size32) begin
                imm = {$random};
                imm = 31'h3930_3929;
                j=j-4;
                imm_size = 4;
                imm_size_en = 2;
                IR[8*j +: 32] = imm;
//                $display ("Time: %0d IMM = %h", $time, imm);
            end


            offset_size8 = (opcode==16'hEB) || (opcode==16'h77) || (opcode==16'h75);
            offset_size16 = operand_override && ((opcode==16'hE8) || (opcode==16'hE9) || (opcode==16'h0F87) || (opcode==16'h0F85));
            offset_size32 = (operand_override && (opcode==16'hEA)) || 
                (!operand_override && ((opcode==16'hE9) || (opcode==16'hE8) || (opcode==16'h0F87) || (opcode==16'h0F85)));
            offset_size48 = (!operand_override && (opcode==16'hEA)) || (opcode==16'h9A);

            offset_present = offset_size8 | offset_size16 | offset_size32 | offset_size48;

            if(offset_size8) begin
                offset[7:0] = {$random};
                j=j-1;
                offset_size = 1;
                offset_size_en = 0;
                IR[8*j +: 8] = offset[7:0];
//                $display ("Time: %0d OFFSET = %h", $time, offset[7:0]);
            end else if(offset_size16) begin
                offset[15:0] = {$random};
                j=j-2;
                offset_size = 2;
                offset_size_en = 1;
                IR[8*j +: 16] = offset[15:0];
//                $display ("Time: %0d OFFSET = %h", $time, offset[15:0]);
            end else if(offset_size32) begin
                offset = {$random};
                j=j-4;
                offset_size = 4;
                offset_size_en = 2;
                IR[8*j +: 32] = offset;
//                $display ("Time: %0d OFFSET = %h", $time, offset[31:0]);
            end else if(offset_size48) begin
                offset[31:0] = {$random};
                offset[47:32] = {$random};
                j=j-6;
                offset_size = 6;
                offset_size_en = 3;
                IR[8*j +: 48] = offset;
//                $display ("Time: %0d OFFSET = %h", $time, offset[47:0]);
            end

            instr_length = prefix_size + opcode_size + modrm_present + sib_present + disp_size + imm_size + offset_size;
//            $display("%h, %h, %h, %h, %h, %h, %h", prefix_size, opcode_size,modrm_present,sib_present,disp_size,imm_size,offset_size);
            //$display("instr_length = %h", instr_length);
            @(posedge clk);
           #clk_cycle; 
           #1; // allow for "setup time"

/*************************** DECODE2 STAGE INPUTS COMPARE ******************************/
           if(u_pipeline.IR_OUT !== IR) begin
               $display("time: %0d IR_OUT error: %h!!", $time, u_pipeline.IR_OUT);
//               $stop;
           end else 
               // $display("time: %0d IR_OUT: %h", $time, u_pipeline.IR_OUT);

           if(u_pipeline.DE_EIP_OUT !== u_pipeline.DE_EIP_IN) begin
               $display("time: %0d DE_EIP_OUT error!!: %h", $time, u_pipeline.DE_EIP_OUT);
//               $stop;
           end

           if(u_pipeline.DE_CS_OUT !== u_pipeline.DE_CS_IN) begin
               $display("time: %0d DE_CS_OUT error!!: %h", $time, u_pipeline.DE_CS_OUT);
//               $stop;
           end

           if(u_pipeline.DE_INSTR_LENGTH_UPDATE_OUT !== instr_length) begin
               $display("time: %0d DE_INSTR_LENGTH_UPDATE_OUT error!!: %h %h", $time, u_pipeline.DE_INSTR_LENGTH_UPDATE_OUT, instr_length);
//               $stop;
           end

           if(u_pipeline.DE_OPCODE_OUT !== opcode) begin
               $display("time: %0d DE_OPCODE_OUT error!!: %h", $time, u_pipeline.DE_OPCODE_OUT);
//               $stop;
           end

           if(u_pipeline.DE_PRE_SIZE_OUT !== prefix_size) begin
               $display("time: %0d DE_PRE_SIZE_OUT error!! %h", $time, u_pipeline.DE_PRE_SIZE_OUT);
//               $stop;
           end

           if(u_pipeline.DE_PRE_PRES_OUT !== prefix_present) begin
               $display("time: %0d DE_PRE_PRES_OUT error!! %h", $time, u_pipeline.DE_PRE_PRES_OUT);
//               $stop;
           end

           if(u_pipeline.DE_SEG_OVR_OUT !== 0) begin
               $display("time: %0d DE_SEG_OVR_OUT error!! %h", $time, u_pipeline.DE_SEG_OVR_OUT);
//               $stop;
           end

           if(u_pipeline.DE_OP_OVR_OUT !== operand_override) begin
               $display("time: %0d DE_OP_OVR_OUT error!! %h", $time, u_pipeline.DE_OP_OVR_OUT);
//               $stop;
           end

           if(u_pipeline.DE_RE_PRE_OUT !== 0) begin
               $display("time: %0d DE_RE_PRE_OUT error!! %h", $time, u_pipeline.DE_RE_PRE_OUT);
//               $stop;
           end

           if(u_pipeline.DE_MODRM_PRES_OUT !== modrm_present) begin
               $display("time: %0d DE_MODRM_PRES_OUT error!! %h", $time, u_pipeline.DE_MODRM_PRES_OUT);
//               $stop;
           end

           if(u_pipeline.DE_IMM_PRES_OUT !== imm_present) begin
               $display("time: %0d DE_IMM_PRES_OUT error!! %h", $time, u_pipeline.DE_IMM_PRES_OUT);
//               $stop;
           end

           if(imm_present) begin
           if(u_pipeline.DE_IMM_SIZE_OUT !== imm_size_en) begin
               $display("time: %0d DE_IMM_SIZE_OUT error!! %h", $time, u_pipeline.DE_IMM_SIZE_OUT);
//               $stop;
           end
           end

           if(u_pipeline.DE_SIB_PRES_OUT !== sib_present) begin
               $display("time: %0d DE_SIB_PRES_OUT error!! %h", $time, u_pipeline.DE_SIB_PRES_OUT);
//               $stop;
           end

           if(u_pipeline.DE_DISP_PRES_OUT !== disp_present) begin
               $display("time: %0d DE_DISP_PRES_OUT error!! %h", $time, u_pipeline.DE_DISP_PRES_OUT);
//               $stop;
           end

           if(disp_present) begin
           if(u_pipeline.DE_DISP_SIZE_OUT !== disp_size_en) begin
               $display("time: %0d DE_DISP_SIZE_OUT error!! %h", $time, u_pipeline.DE_DISP_SIZE_OUT);
//               $stop;
           end
           end

           if(u_pipeline.DE_OFFSET_PRES_OUT !== offset_present) begin
               $display("time: %0d DE_OFFSET_PRES_OUT error!! %h", $time, u_pipeline.DE_OFFSET_PRES_OUT);
//               $stop;
           end

           if(u_pipeline.DE_OP_SIZE_OUT !== opcode_size_en) begin
               $display("time: %0d DE_OP_SIZE_OUT error!! %h", $time, u_pipeline.DE_OP_SIZE_OUT);
//               $stop;
           end

           if(u_pipeline.DE_OFFSET_SIZE_OUT !== offset_size_en) begin
               $display("time: %0d DE_OFFSET_SIZE_OUT error!! %h", $time, u_pipeline.DE_OFFSET_SIZE_OUT);
//               $stop;
           end

//           if(u_pipeline.DE_SEGID_OUT !== segID) begin
//               $display("time: %0d DE_SEGID_OUT error!! %h", $time, u_pipeline.DE_SEGID_OUT);
////               $stop;
//           end

          if(modrm_present) begin
           if(u_pipeline.DE_MODRM_OUT !== modrm) begin
               $display("time: %0d DE_MODRM_OUT error!! %h", $time, u_pipeline.DE_MODRM_OUT);
//               $stop;
           end
          end

          if(sib_present) begin
           if(u_pipeline.DE_SIB_OUT !== sib) begin
               $display("time: %0d DE_SIB_OUT error!! %h", $time, u_pipeline.DE_SIB_OUT);
//               $stop;
           end
          end

/*************************** ADDRESS GENERATION STAGE INPUTS COMPARE ******************************/
            EIP_UPDATE = u_pipeline.DE_INSTR_LENGTH_UPDATE_OUT + u_pipeline.DE_EIP_OUT;

            if(offset_present) begin
                if(offset_size == 1) begin
                    offset_compare[7:0] = offset[7:0];
                    offset_compare[47:8] = 0;
                end else if(offset_size == 2) begin
                    offset_compare[7:0] = offset[15:8];
                    offset_compare[15:8] = offset[7:0];
                    offset_compare[47:16] = 0;
                end else if(offset_size == 4) begin
                    if(opcode == 16'hEA && operand_override) begin
                        offset_compare[47:40] = offset[7:0];
                        offset_compare[39:32] = offset[15:8];
                        offset_compare[31:16] = 16'h0;
                        offset_compare[15:8] = offset[23:16];
                        offset_compare[7:0] = offset[31:24];
                    end else begin
                        offset_compare[31:24] = offset[7:0];
                        offset_compare[23:16] = offset[15:8];
                        offset_compare[15:8] = offset[23:16];
                        offset_compare[7:0] = offset[31:24];
                        offset_compare[47:32] = 0;
                    end
                end else if(offset_size == 6) begin
                    offset_compare[47:40] = offset[7:0];
                    offset_compare[39:32] = offset[15:8];
                    offset_compare[31:24] = offset[23:16];
                    offset_compare[23:16] = offset[31:24];
                    offset_compare[15:8] = offset[39:32];
                    offset_compare[7:0] = offset[47:40];
                end
            end


/*************************** ADDRESS GENERATION STAGE INPUTS COMPARE ******************************/
            #(clk_cycle-1);
            #1;    // Allow for setup time
           
            // Valid Signal always 1 for now
            // Check for the valid signal
            NextV = 1;

            if(u_pipeline.AG_PS_EIP !== EIP_UPDATE) begin
                $display("time: %0d AG_PS_EIP error!! %h", $time, u_pipeline.AG_PS_EIP);
//              $stop;
            end

            if(u_pipeline.AG_PS_CS !== u_pipeline.D2_CS_OUT) begin
                $display("time: %0d AG_PS_CS error!! %h", $time, u_pipeline.AG_PS_CS);
//              $stop;
            end

            if(u_pipeline.AG_PS_CONTROL_STORE !== u_pipeline.D2_CONTROL_STORE_OUT) begin
                $display("time: %0d AG_PS_CONTROL_STORE error!! %h", $time, u_pipeline.AG_PS_CONTROL_STORE_OUT);
//              $stop;
            end

//            if(u_pipeline.AG_PS_OFFSET !== offset_compare) begin
//                $display("time: %0d AG_PS_OFFSET error!! %h", $time, u_pipeline.AG_PS_OFFSET);
////              $stop;
//            end


/*************************** MEMORY STAGE INPUTS COMPARE ******************************/
            #(clk_cycle-1);
            #1;    // Allow for setup time

            // Opcode == 04
            //if(opcode == 16'h4 || opcode==16'h5 || opcode==16'h81 || opcode==16'h83 || opcode==16'h01) begin
            //    result = ME_A_OUT + ME_B_OUT;
            //end
            /*
        $display ("at time %0d, MEM_A = %h", $time, u_pipeline.u_memory_stage.A);
        $display ("at time %0d, MEM_b = %h", $time, u_pipeline.u_memory_stage.B);
        */

/*************************** EXECUTE STAGE INPUTS COMPARE ******************************/
            #(clk_cycle-1);
            #1;    // Allow for setup time
            if(u_pipeline.EX_A != `default_mem_Value) begin 
              $display("Error: EX_B is: %h, but needs to be: %h", u_pipeline.EX_A, `default_mem_Value);
              error <= 1;
            end

            if(u_pipeline.EX_B != 8'h05) begin 
              $display("Error: EX_B is: %h, but needs to be: %h", u_pipeline.EX_B, 8'h05);
              error <= 1;
            end

            if(u_pipeline.EX_ADDRESS != 32'hE060D05) begin 
              $display("Error: EX_ADDRESS is: %h, but needs to be: %h", u_pipeline.EX_ADDRESS, 32'hE060D05);
              error <= 1;
            end

            if(u_pipeline.WB_de_datasize_all_next != 2'b00) begin 
              $display("Error: WB_de_datasize_all_next is: %h, but needs to be: %h", u_pipeline.WB_de_datasize_all_next, 3'b00);
              error <= 1;
            end

            if(u_pipeline.EX_d2_aluk_ex != 2'b00) begin 
              $display("Error: EX_d2_aluk_ex is: %h, but needs to be: %h", u_pipeline.EX_d2_aluk_ex, 3'b00);
              error <= 1;
            end

/*************************** WRITEBACK STAGE INPUTS COMPARE ******************************/
            #(clk_cycle-1);
            #1;    // Allow for setup time

            if(u_pipeline.WB_FLAGS != 32'h000) begin 
              $display("Error: WB_FLAGS is: %h, but needs to be: %h", u_pipeline.WB_FLAGS, 32'h000);
              error <= 1;
            end

/*************************** WRITEBACK STAGE OUTPUTS COMPARE ******************************/

            if(u_pipeline.WB_Final_Dcache_address != 32'hE060D05) begin 
              $display("Error: WB_Final_Dcache_address is: %h, but needs to be: %h", u_pipeline.WB_Final_Dcache_address, 32'hE060D05);
              error <= 1;
            end

            if(u_pipeline.WB_Final_data1 != u_pipeline.EX_A + u_pipeline.EX_B) begin 
              $display("Error: WB_Final_data1 is: %h, but needs to be: %h", u_pipeline.WB_Final_data1, u_pipeline.EX_A + u_pipeline.EX_B);
              error <= 1;
            end

            if(u_pipeline.WB_Final_ld_gpr1 != 1'b0) begin 
              $display("Error: WB_Final_ld_gpr1 is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_gpr1, 1'b1);
              error <= 1;
            end

            if(u_pipeline.WB_Final_ld_gpr2 != 1'b0) begin 
              $display("Error: WB_Final_ld_gpr2 is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_gpr2, 1'b0);
              error <= 1;
            end

            if(u_pipeline.WB_Final_ld_gpr3 != 1'b0) begin 
              $display("Error: WB_Final_ld_gpr3 is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_gpr3, 1'b0);
              error <= 1;
            end
            
            if(u_pipeline.WB_Final_datasize != 2'b00) begin 
              $display("Error: WB_Final_datasize is: %h, but needs to be: %h", u_pipeline.WB_Final_datasize, 2'b00);
              error <= 1;
            end

            if(u_pipeline.WB_Final_ld_mm != 1'b0) begin 
              $display("Error: WB_Final_ld_mm is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_mm, 1'b0);
              error <= 1;
            end

           if(u_pipeline.WB_Final_ld_eip != 1'b1) begin 
              $display("Error: WB_Final_ld_eip is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_eip, 1'b1);
              error <= 1;
            end

            if(u_pipeline.WB_Final_ld_cs != 1'b0) begin 
              $display("Error: WB_Final_ld_cs is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_cs, 1'b0);
              error <= 1;
            end

            if(u_pipeline.WB_Final_Flags != 32'h000) begin 
              $display("Error: WB_Final_Flags is: %h, but needs to be: %h", u_pipeline.WB_Final_Flags, 32'h890);
              error <= 1;
            end

            if(u_pipeline.WB_Final_ld_flags != 1'b1) begin 
              $display("Error: WB_Final_ld_flags is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_flags, 1'b1);
              error <= 1;
            end

        // WRITEBACK SIGNALS
        /*
        $display ("at time %0d, WB_Final_DR1 = %h", $time, u_pipeline.u_writeback.WB_Final_DR1);
        $display ("at time %0d, WB_Final_DR2 = %h", $time, u_pipeline.u_writeback.WB_Final_DR2);
        $display ("at time %0d, WB_Final_DR3 = %h", $time, u_pipeline.u_writeback.WB_Final_DR3);
        $display ("at time %0d, WB_Final_data1 = %h", $time, u_pipeline.u_writeback.WB_Final_data1);
        $display ("at time %0d, WB_Final_data2 = %h", $time, u_pipeline.u_writeback.WB_Final_data2);
        $display ("at time %0d, WB_Final_data3 = %h", $time, u_pipeline.u_writeback.WB_Final_data3);
        $display ("at time %0d, WB_Final_ld_gpr1 = %h", $time, u_pipeline.u_writeback.WB_Final_ld_gpr1);
        $display ("at time %0d, WB_Final_ld_gpr2 = %h", $time, u_pipeline.u_writeback.WB_Final_ld_gpr2);
        $display ("at time %0d, WB_Final_ld_gpr3 = %h", $time, u_pipeline.u_writeback.WB_Final_ld_gpr3);
        $display ("at time %0d, WB_Final_datasize = %h", $time, u_pipeline.u_writeback.WB_Final_datasize);
        $display ("at time %0d, WB_Final_ld_seg = %h", $time, u_pipeline.u_writeback.WB_Final_ld_seg);
        $display ("at time %0d, WB_Final_MM_Data = %h", $time, u_pipeline.u_writeback.WB_Final_MM_Data);
        $display ("at time %0d, WB_Final_ld_mm  = %h", $time, u_pipeline.u_writeback.WB_Final_ld_mm);
        $display ("at time %0d, WB_Final_EIP  = %h", $time, u_pipeline.u_writeback.WB_Final_EIP);
        $display ("at time %0d, WB_Final_ld_eip  = %h", $time, u_pipeline.u_writeback.WB_Final_ld_eip);
        $display ("at time %0d, WB_Final_Dcache_Data = %h", $time, u_pipeline.u_writeback.WB_Final_Dcache_Data);
        $display ("at time %0d, WB_Final_Dcache_address = %h", $time, u_pipeline.u_writeback.WB_Final_Dcache_address);
        $display ("at time %0d, DEP_v_wb_ld_gpr1 = %h", $time, u_pipeline.u_writeback.DEP_v_wb_ld_gpr1);
        $display ("at time %0d, DEP_v_wb_ld_gpr2 = %h", $time, u_pipeline.u_writeback.DEP_v_wb_ld_gpr2);
        $display ("at time %0d, DEP_v_wb_ld_gpr3 = %h", $time, u_pipeline.u_writeback.DEP_v_wb_ld_gpr3);
        $display ("at time %0d, DEP_v_wb_ld_seg = %h", $time, u_pipeline.u_writeback.DEP_v_wb_ld_seg);
        $display ("at time %0d, DEP_v_wb_ld_mm = %h", $time, u_pipeline.u_writeback.DEP_v_wb_ld_mm);
        $display ("at time %0d, DEP_v_wb_dcache_write = %h", $time, u_pipeline.u_writeback.DEP_v_wb_dcache_write);
        $display ("at time %0d, wb_halt_all  = %h", $time, u_pipeline.u_writeback.wb_halt_all);
        $display ("at time %0d, wb_repne_terminate_all = %h", $time, u_pipeline.u_writeback.wb_repne_terminate_all);
        $display ("at time %0d, WB_stall = %h", $time, u_pipeline.u_writeback.WB_stall);
        $display ("at time %0d, Flags_forwarded = %h", $time, u_pipeline.u_writeback.flags_dataforwarded);
        */
/*********************************************************/
           // Ignore all stall cycles; do not compare them against trace cycles.
           //while (stall_signal == 1'b1) begin
           //     #clk_cycle
           //end

        if(error == 0) begin 
          $display("****************** Test Passed! ******************");
        end else begin
          $display("****************** Test Failed! ******************");
        end
        $fclose(file);
        $finish;
     end


   initial begin
       $vcdplusfile("pipeline.dump.vpd");
       $vcdpluson(0, TOP);
   end

    // Initializing the control store
    initial begin
        $readmemb("control_store/rom0_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom1.mem);
        $readmemb("control_store/rom0_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom1.mem);
        $readmemb("control_store/rom1_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom2.mem);
        $readmemb("control_store/rom1_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom2.mem);
        $readmemb("control_store/rom2_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom3.mem);
        $readmemb("control_store/rom2_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom3.mem);
        $readmemb("control_store/rom3_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom4.mem);
        $readmemb("control_store/rom3_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom4.mem);
        $readmemb("control_store/rom4_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom5.mem);
        $readmemb("control_store/rom4_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom5.mem);
        $readmemb("control_store/rom5_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom6.mem);
        $readmemb("control_store/rom5_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom6.mem);
        $readmemb("control_store/rom6_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom7.mem);
        $readmemb("control_store/rom6_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom7.mem);
        $readmemb("control_store/rom7_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom8.mem);
        $readmemb("control_store/rom7_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom8.mem);
        $readmemb("control_store/rom8_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom9.mem);
        $readmemb("control_store/rom8_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom9.mem);
    end


    // Checking the values
/*    always @(posedge clk) begin
        // Decode stage 1 signals 
        $strobe ("at time %0d, DE1_opcode = %h", $time, u_pipeline.u_decode_stage1.opcode);
        $strobe ("at time %0d, DE1_opcode_size = %h", $time, u_pipeline.u_decode_stage1.opcode_size);
        $strobe ("at time %0d, DE1_modrm_sel = %h", $time, u_pipeline.u_decode_stage1.modrm_sel);
        $strobe ("at time %0d, DE1_instr_length_updt = %h", $time, u_pipeline.u_decode_stage1.instr_length_updt);
        $strobe ("at time %0d, DE1_prefix_size = %h", $time, u_pipeline.u_decode_stage1.prefix_size);
        $strobe ("at time %0d, DE1_prefix_present = %h", $time, u_pipeline.u_decode_stage1.prefix_present);
        $strobe ("at time %0d, DE1_segment_override = %h", $time, u_pipeline.u_decode_stage1.segment_override);
        $strobe ("at time %0d, DE1_operand_override = %h", $time, u_pipeline.u_decode_stage1.operand_override);
        $strobe ("at time %0d, DE1_repeat_prefix = %h", $time, u_pipeline.u_decode_stage1.repeat_prefix);
        $strobe ("at time %0d, DE1_modrm_present = %h", $time, u_pipeline.u_decode_stage1.modrm_present);
        $strobe ("at time %0d, DE1_imm_present = %h", $time, u_pipeline.u_decode_stage1.imm_present);
        $strobe ("at time %0d, DE1_imm_size = %h", $time, u_pipeline.u_decode_stage1.imm_size);
        $strobe ("at time %0d, DE1_sib_present = %h", $time, u_pipeline.u_decode_stage1.sib_present);
        $strobe ("at time %0d, DE1_disp_present = %h", $time, u_pipeline.u_decode_stage1.disp_present);
        $strobe ("at time %0d, DE1_disp_size = %h", $time, u_pipeline.u_decode_stage1.disp_size);
        $strobe ("at time %0d, DE1_imm_sel = %h", $time, u_pipeline.u_decode_stage1.imm_sel);
        $strobe ("at time %0d, DE1_disp_sel = %h", $time, u_pipeline.u_decode_stage1.disp_sel);
        $strobe ("at time %0d, DE1_offset_present = %h", $time, u_pipeline.u_decode_stage1.offset_present);
        $strobe ("at time %0d, DE1_offset_size = %h", $time, u_pipeline.u_decode_stage1.offset_size);
        $strobe ("at time %0d, DE1_segID = %h", $time, u_pipeline.u_decode_stage1.segID);
        $strobe ("at time %0d, DE1_modrm = %h", $time, u_pipeline.u_decode_stage1.modrm);
        $strobe ("at time %0d, DE1_sib = %h", $time, u_pipeline.u_decode_stage1.sib);

        // Decode_stage 2 signals
        $strobe ("at time %0d, DE2_offset = %h", $time, u_pipeline.u_decode_stage2.offset);
        $strobe ("at time %0d, DE2_CONTROL_STORE = %h", $time, u_pipeline.u_decode_stage2.CONTROL_STORE);
        $strobe ("at time %0d, DE2_D2_DATA_SIZE_AG = %h", $time, u_pipeline.u_decode_stage2.D2_DATA_SIZE_AG);
        $strobe ("at time %0d, DE2_D2_SR1_NEEDED_AG = %h", $time, u_pipeline.u_decode_stage2.D2_SR1_NEEDED_AG);
        $strobe ("at time %0d, DE2_D2_SEG1_NEEDED_AG = %h", $time, u_pipeline.u_decode_stage2.D2_SEG1_NEEDED_AG);
        $strobe ("at time %0d, DE2_D2_MM1_NEEDED_DE = %h", $time, u_pipeline.u_decode_stage2.D2_MM1_NEEDED_AG);
        $strobe ("at time %0d, DE2_D2_MEM_RD_ME = %h", $time, u_pipeline.u_decode_stage2.D2_MEM_RD_ME);
        $strobe ("at time %0d, DE2_D2_MEM_WR_ME = %h", $time, u_pipeline.u_decode_stage2.D2_MEM_WR_ME);
        $strobe ("at time %0d, DE2_D2_ALUK_EX = %h", $time, u_pipeline.u_decode_stage2.D2_ALUK_EX);
        $strobe ("at time %0d, DE2_D2_LD_GPR1_WB = %h", $time, u_pipeline.u_decode_stage2.D2_LD_GPR1_WB);
        $strobe ("at time %0d, DE2_D2_LD_MM_WB = %h", $time, u_pipeline.u_decode_stage2.D2_LD_MM_WB);
        $strobe ("at time %0d, DE2_SR1_OUT = %h", $time, u_pipeline.u_decode_stage2.SR1_OUT);
        $strobe ("at time %0d, DE2_SR2_OUT = %h", $time, u_pipeline.u_decode_stage2.SR2_OUT);
        $strobe ("at time %0d, DE2_SR3_OUT = %h", $time, u_pipeline.u_decode_stage2.SR3_OUT);
        $strobe ("at time %0d, DE2_SR4_OUT = %h", $time, u_pipeline.u_decode_stage2.SR4_OUT);
        $strobe ("at time %0d, DE2_SEG1_OUT = %h", $time, u_pipeline.u_decode_stage2.SEG1_OUT);
        $strobe ("at time %0d, DE2_SEG2_OUT = %h", $time, u_pipeline.u_decode_stage2.SEG2_OUT);
        $strobe ("at time %0d, DE2_IMM32_OUT = %h", $time, u_pipeline.u_decode_stage2.IMM32_OUT);
        $strobe ("at time %0d, DE2_DISP32_OUT = %h", $time, u_pipeline.u_decode_stage2.DISP32_OUT);
        $strobe ("at time %0d, DE2_DE_SIB_EN_AG = %h", $time, u_pipeline.u_decode_stage2.DE_SIB_EN_AG);
        $strobe ("at time %0d, DE2_DE_DISP_EN_AG = %h", $time, u_pipeline.u_decode_stage2.DE_DISP_EN_AG);
        $strobe ("at time %0d, DE2_DE_BASE_REG_EN_AG = %h", $time, u_pipeline.u_decode_stage2.DE_BASE_REG_EN_AG);
        $strobe ("at time %0d, DE2_DE_MUX_SEG_AG = %h", $time, u_pipeline.u_decode_stage2.DE_MUX_SEG_AG);
        $strobe ("at time %0d, DE2_DE_CMPXCHG_AG = %h", $time, u_pipeline.u_decode_stage2.DE_CMPXCHG_AG);
        $strobe ("at time %0d, DE2_DE_SIB_S_AG = %h", $time, u_pipeline.u_decode_stage2.DE_SIB_S_AG);

        // Register file signals
        $strobe ("at time %0d, REG_SR1_DATA = %h", $time, u_pipeline.SR1_DATA);
        $strobe ("at time %0d, REG_SR2_DATA = %h", $time, u_pipeline.SR2_DATA);
        $strobe ("at time %0d, REG_SR3_DATA = %h", $time, u_pipeline.SR3_DATA);
        $strobe ("at time %0d, REG_SIB_I_DATA = %h", $time, u_pipeline.SIB_I_DATA);
        $strobe ("at time %0d, REG_SEG_OUT1 = %h", $time, u_pipeline.u_register_file.SEGDOUT1);
        $strobe ("at time %0d, REG_SEG_OUT2 = %h", $time, u_pipeline.u_register_file.SEGDOUT2);
        $strobe ("at time %0d, REG_MM_OUT1 = %h", $time, u_pipeline.u_register_file.MMDOUT1);
        $strobe ("at time %0d, REG_MM_OUT2 = %h", $time, u_pipeline.u_register_file.MMDOUT2);
        $strobe ("at time %0d, REG_CSDOUT = %h", $time, u_pipeline.u_register_file.CSDOUT);
        $strobe ("at time %0d, REG_EIP_DOUT = %h", $time, u_pipeline.u_register_file.EIPDOUT);
        $strobe ("at time %0d, REG_EFLAGS = %h", $time, u_pipeline.u_register_file.EFLAGSDOUT);

        // Address generation stage signals
        $strobe ("at time %0d, AG_SR1_OUT = %h", $time, u_pipeline.u_address_generation.SR1_OUT);
        $strobe ("at time %0d, AG_SR2_OUT = %h", $time, u_pipeline.u_address_generation.SR2_OUT);
        $strobe ("at time %0d, AG_SR3_OUT = %h", $time, u_pipeline.u_address_generation.SR3_OUT);
        $strobe ("at time %0d, AG_SIB_I_OUT = %h", $time, u_pipeline.u_address_generation.SIB_I_OUT);
        $strobe ("at time %0d, AG_SEG1_OUT = %h", $time, u_pipeline.u_address_generation.SEG1_OUT);
        $strobe ("at time %0d, AG_SEG2_OUT = %h", $time, u_pipeline.u_address_generation.SEG2_OUT);
        $strobe ("at time %0d, AG_MM1_OUT = %h", $time, u_pipeline.u_address_generation.MM1_OUT);
        $strobe ("at time %0d, AG_MM2_OUT = %h", $time, u_pipeline.u_address_generation.MM2_OUT);
        $strobe ("at time %0d, AG_DATA_SIZE_OUT = %h", $time, u_pipeline.u_address_generation.DATA_SIZE_OUT);
        $strobe ("at time %0d, AG_NEIP_OUT = %h", $time, u_pipeline.u_address_generation.NEIP_OUT);
        $strobe ("at time %0d, AG_NCS_OUT = %h", $time, u_pipeline.u_address_generation.NCS_OUT);
        $strobe ("at time %0d, AG_CONTROL_STORE_OUT = %h", $time, u_pipeline.u_address_generation.CONTROL_STORE_OUT);
        $strobe ("at time %0d, AG_A_OUT = %h", $time, u_pipeline.u_address_generation.A_OUT);
        $strobe ("at time %0d, AG_B_OUT = %h", $time, u_pipeline.u_address_generation.B_OUT);
        $strobe ("at time %0d, AG_MM_A_OUT = %h", $time, u_pipeline.u_address_generation.MM_A_OUT);
        $strobe ("at time %0d, AG_MM_B_OUT = %h", $time, u_pipeline.u_address_generation.MM_B_OUT);
        $strobe ("at time %0d, AG_SP_XCHG_DATA_OUT = %h", $time, u_pipeline.u_address_generation.SP_XCHG_DATA_OUT);
        $strobe ("at time %0d, AG_MEM_RD_ADDR_OUT = %h", $time, u_pipeline.u_address_generation.MEM_RD_ADDR_OUT);
        $strobe ("at time %0d, AG_MEM_WR_ADDR_OUT = %h", $time, u_pipeline.u_address_generation.MEM_WR_ADDR_OUT);
        $strobe ("at time %0d, AG_D2_ALUK_EX_OUT = %h", $time, u_pipeline.u_address_generation.D2_ALUK_EX_OUT);
        $strobe ("at time %0d, AG_DRID1_OUT = %h", $time, u_pipeline.u_address_generation.DRID1_OUT);
        $strobe ("at time %0d, AG_DRID2_OUT = %h", $time, u_pipeline.u_address_generation.DRID2_OUT);
        $strobe ("at time %0d, AG_D2_MEM_RD_ME_OUT = %h", $time, u_pipeline.u_address_generation.D2_MEM_RD_ME_OUT);
        $strobe ("at time %0d, AG_D2_MEM_WR_WB_OUT = %h", $time, u_pipeline.u_address_generation.D2_MEM_WR_WB_OUT);
        $strobe ("at time %0d, AG_D2_LD_GPR1_WB_OUT = %h", $time, u_pipeline.u_address_generation.D2_LD_GPR1_WB_OUT);
        $strobe ("at time %0d, AG_D2_LD_MM_WB_OUT = %h", $time, u_pipeline.u_address_generation.D2_LD_MM_WB_OUT);
        $strobe ("at time %0d, AG_DEP_STALL_OUT = %h", $time, u_pipeline.u_address_generation.DEP_STALL_OUT);
        $strobe ("at time %0d, AG_SEG_LIMIT_EXC_OUT = %h", $time, u_pipeline.u_address_generation.SEG_LIMIT_EXC_OUT);

        // MEMORY STAGE SIGNALS
        $strobe ("at time %0d, ME_DCACHE_EN = %h", $time, u_pipeline.u_memory_stage.DCACHE_EN);
        $strobe ("at time %0d, ME_NEIP_OUT = %h", $time, u_pipeline.u_memory_stage.NEIP_OUT);
        $strobe ("at time %0d, ME_NCS_OUT = %h", $time, u_pipeline.u_memory_stage.NCS_OUT);
        $strobe ("at time %0d, ME_CONTROL_STORE_OUT = %h", $time, u_pipeline.u_memory_stage.CONTROL_STORE_OUT);
        $strobe ("at time %0d, ME_A_OUT = %h", $time, u_pipeline.u_memory_stage.A_OUT);
        $strobe ("at time %0d, ME_B_OUT = %h", $time, u_pipeline.u_memory_stage.B_OUT);
        $strobe ("at time %0d, ME_MM_A_OUT = %h", $time, u_pipeline.u_memory_stage.MM_A_OUT);
        $strobe ("at time %0d, ME_MM_B_OUT = %h", $time, u_pipeline.u_memory_stage.MM_B_OUT);
        $strobe ("at time %0d, ME_SP_XCHG_DATA_OUT = %h", $time, u_pipeline.u_memory_stage.SP_XCHG_DATA_OUT);
        $strobe ("at time %0d, ME_MEM_RD_ADDR_OUT = %h", $time, u_pipeline.u_memory_stage.MEM_RD_ADDR_OUT);
        $strobe ("at time %0d, ME_MEM_WR_ADDR_OUT = %h", $time, u_pipeline.u_memory_stage.MEM_WR_ADDR_OUT);
        $strobe ("at time %0d, ME_DATA_SIZE_OUT = %h", $time, u_pipeline.u_memory_stage.DATA_SIZE_OUT);
        $strobe ("at time %0d, ME_DE_ALUK_EX_OUT = %h", $time, u_pipeline.u_memory_stage.DE_ALUK_EX_OUT);
        $strobe ("at time %0d, ME_DRID1_OUT = %h", $time, u_pipeline.u_memory_stage.DRID1_OUT);
        $strobe ("at time %0d, ME_DRID2_OUT = %h", $time, u_pipeline.u_memory_stage.DRID2_OUT);
        $strobe ("at time %0d, ME_D2_MEM_WR_WB_OUT = %h", $time, u_pipeline.u_memory_stage.D2_MEM_WR_WB_OUT);
        $strobe ("at time %0d, ME_D2_LD_GPR1_WB_OUT = %h", $time, u_pipeline.u_memory_stage.D2_LD_GPR1_WB_OUT);
        $strobe ("at time %0d, ME_D2_LD_MM_WB_OUT = %h", $time, u_pipeline.u_memory_stage.D2_LD_MM_WB_OUT);

        // EXECUTE STAGE SIGNALS
        $strobe ("at time %0d, EX_WB_V_next = %h", $time, u_pipeline.u_execute.WB_V_next);
        $strobe ("at time %0d, EX_WB_NEIP_next = %h", $time, u_pipeline.u_execute.WB_NEIP_next);
        $strobe ("at time %0d, EX_WB_NCS_next = %h", $time, u_pipeline.u_execute.WB_NCS_next);
        $strobe ("at time %0d, EX_WB_CONTROL_STORE_next = %h", $time, u_pipeline.u_execute.WB_CONTROL_STORE_next);
        $strobe ("at time %0d, EX_WB_de_datasize_all_next = %h", $time, u_pipeline.u_execute.WB_de_datasize_all_next);
        $strobe ("at time %0d, EX_WB_ex_ld_gpr1_wb_next = %h", $time, u_pipeline.u_execute.WB_ex_ld_gpr1_wb_next);
        $strobe ("at time %0d, EX_WB_ex_ld_gpr2_wb_next = %h", $time, u_pipeline.u_execute.WB_ex_ld_gpr2_wb_next);
        $strobe ("at time %0d, EX_WB_ex_dcache_write_wb_next = %h", $time, u_pipeline.u_execute.WB_ex_dcache_write_wb_next);
        $strobe ("at time %0d, EX_WB_de_repne_wb_next = %h", $time, u_pipeline.u_execute.WB_de_repne_wb_next);
        $strobe ("at time %0d, EX_WB_RESULT_A_next = %h", $time, u_pipeline.u_execute.WB_RESULT_A_next);
        $strobe ("at time %0d, EX_WB_RESULT_B_next = %h", $time, u_pipeline.u_execute.WB_RESULT_B_next);
        $strobe ("at time %0d, EX_WB_RESULT_C_next = %h", $time, u_pipeline.u_execute.WB_RESULT_C_next);
        $strobe ("at time %0d, EX_WB_FLAGS_next = %h", $time, u_pipeline.u_execute.WB_FLAGS_next);
        $strobe ("at time %0d, EX_WB_RESULT_MM_next = %h", $time, u_pipeline.u_execute.WB_RESULT_MM_next);
        $strobe ("at time %0d, EX_WB_ADDRESS_next = %h", $time, u_pipeline.u_execute.WB_ADDRESS_next);
        $strobe ("at time %0d, EX_DEP_v_ex_ld_gpr1 = %h", $time, u_pipeline.u_execute.DEP_v_ex_ld_gpr1);
        $strobe ("at time %0d, EX_DEP_v_ex_ld_gpr2 = %h", $time, u_pipeline.u_execute.DEP_v_ex_ld_gpr2);
        $strobe ("at time %0d, EX_DEP_v_ex_ld_gpr3 = %h", $time, u_pipeline.u_execute.DEP_v_ex_ld_gpr3);
        $strobe ("at time %0d, EX_DEP_v_ex_ld_seg = %h", $time, u_pipeline.u_execute.Dep_v_ex_ld_seg);
        $strobe ("at time %0d, EX_DEP_v_ex_ld_mm = %h", $time, u_pipeline.u_execute.Dep_v_ex_ld_mm);
        $strobe ("at time %0d, EX_DEP_v_ex_dcache_write = %h", $time, u_pipeline.u_execute.Dep_v_ex_dcache_write);
        $strobe ("at time %0d, EX_WB_ld_latches = %h", $time, u_pipeline.u_execute.WB_ld_latches);
        $strobe ("at time %0d, EX_WB_DR1_next = %h", $time, u_pipeline.u_execute.WB_DR1_next);
        $strobe ("at time %0d, EX_WB_DR2_next = %h", $time, u_pipeline.u_execute.WB_DR2_next);
        $strobe ("at time %0d, EX_WB_DR3_next = %h", $time, u_pipeline.u_execute.WB_DR3_next);

        // WRITEBACK SIGNALS
        $strobe ("at time %0d, WB_Final_DR1 = %h", $time, u_pipeline.u_writeback.WB_Final_DR1);
        $strobe ("at time %0d, WB_Final_DR2 = %h", $time, u_pipeline.u_writeback.WB_Final_DR2);
        $strobe ("at time %0d, WB_Final_DR3 = %h", $time, u_pipeline.u_writeback.WB_Final_DR3);
        $strobe ("at time %0d, WB_Final_data1 = %h", $time, u_pipeline.u_writeback.WB_Final_data1);
        $strobe ("at time %0d, WB_Final_data2 = %h", $time, u_pipeline.u_writeback.WB_Final_data2);
        $strobe ("at time %0d, WB_Final_data3 = %h", $time, u_pipeline.u_writeback.WB_Final_data3);
        $strobe ("at time %0d, WB_Final_ld_gpr1 = %h", $time, u_pipeline.u_writeback.WB_Final_ld_gpr1);
        $strobe ("at time %0d, WB_Final_ld_gpr2 = %h", $time, u_pipeline.u_writeback.WB_Final_ld_gpr2);
        $strobe ("at time %0d, WB_Final_ld_gpr3 = %h", $time, u_pipeline.u_writeback.WB_Final_ld_gpr3);
        $strobe ("at time %0d, WB_Final_datasize = %h", $time, u_pipeline.u_writeback.WB_Final_datasize);
        $strobe ("at time %0d, WB_Final_ld_seg = %h", $time, u_pipeline.u_writeback.WB_Final_ld_seg);
        $strobe ("at time %0d, WB_Final_MM_Data = %h", $time, u_pipeline.u_writeback.WB_Final_MM_Data);
        $strobe ("at time %0d, WB_Final_ld_mm  = %h", $time, u_pipeline.u_writeback.WB_Final_ld_mm);
        $strobe ("at time %0d, WB_Final_EIP  = %h", $time, u_pipeline.u_writeback.WB_Final_EIP);
        $strobe ("at time %0d, WB_Final_ld_eip  = %h", $time, u_pipeline.u_writeback.WB_Final_ld_eip);
        $strobe ("at time %0d, WB_Final_Dcache_Data = %h", $time, u_pipeline.u_writeback.WB_Final_Dcache_Data);
        $strobe ("at time %0d, WB_Final_Dcache_address = %h", $time, u_pipeline.u_writeback.WB_Final_Dcache_address);
        $strobe ("at time %0d, DEP_v_wb_ld_gpr1 = %h", $time, u_pipeline.u_writeback.DEP_v_wb_ld_gpr1);
        $strobe ("at time %0d, DEP_v_wb_ld_gpr2 = %h", $time, u_pipeline.u_writeback.DEP_v_wb_ld_gpr2);
        $strobe ("at time %0d, DEP_v_wb_ld_gpr3 = %h", $time, u_pipeline.u_writeback.DEP_v_wb_ld_gpr3);
        $strobe ("at time %0d, DEP_v_wb_ld_seg = %h", $time, u_pipeline.u_writeback.DEP_v_wb_ld_seg);
        $strobe ("at time %0d, DEP_v_wb_ld_mm = %h", $time, u_pipeline.u_writeback.DEP_v_wb_ld_mm);
        $strobe ("at time %0d, DEP_v_wb_dcache_write = %h", $time, u_pipeline.u_writeback.DEP_v_wb_dcache_write);
        $strobe ("at time %0d, wb_halt_all  = %h", $time, u_pipeline.u_writeback.wb_halt_all);
        $strobe ("at time %0d, wb_repne_terminate_all = %h", $time, u_pipeline.u_writeback.wb_repne_terminate_all);
        $strobe ("at time %0d, WB_stall = %h", $time, u_pipeline.u_writeback.WB_stall);
        $strobe ("at time %0d, CF_dataforwarded = %h", $time, u_pipeline.u_writeback.CF_dataforwarded);
        $strobe ("at time %0d, AF_dataforwarded = %h", $time, u_pipeline.u_writeback.AF_dataforwarded);

    end
*/
   
endmodule
