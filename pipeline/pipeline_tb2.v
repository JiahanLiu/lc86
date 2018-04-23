`timescale 1ns/1ps
`define EOF = 32'hFFFF_FFFF
`define NULL 0

`define assert(signal, value) \
        if (signal !== value) begin \
            $display("ASSERTION FAILED in %m: signal != value"); \
            $finish; \
        end

module TOP;
//this module is used to debug the basic functionality of the simulator
//the clk cycle used to drive the entire system
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

   PIPELINE u_pipeline(clk, clr, pre, IR);

   initial begin
        clk = 0;
        clr = 1;
        pre = 0;
        repeat(2) #clk_cycle
        pre = 1;
        forever #(half_cycle)  clk = ~clk;
    end

    // Set the register values
    // reg0 = 32'08000800
    // reg1 = 32'09010901
    // reg2 = 32'0A020A02
    // reg3 = 32'0B030B03
    // reg4 = 32'0C040C04
    // reg5 = 32'0D050D05
    // reg6 = 32'0E060E06
    // reg7 = 32'0F070F07
    initial begin
        u_pipeline.u_register_file.gpr.reg0_ll.Q = 32'h0;
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
     end 

     initial begin
        IR = 128'h0412;

        #clk_cycle
        IR = 128'h0412;

        #(2*clk_cycle)
        $finish;
     end

    // Checking the values
    always @(posedge clk) begin
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
//        $strobe ("at time %0d, CF_dataforwarded = %h", $time, u_pipeline.u_writeback.CF_dataforwarded);
//        $strobe ("at time %0d, AF_dataforwarded = %h", $time, u_pipeline.u_writeback.AF_dataforwarded);

    end

   
endmodule
