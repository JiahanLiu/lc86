`timescale 1ns/1ps

module TOP;
//this module is used to debug the basic functionality of the simulator
//the clk cycle used to drive the entire system
   reg clk, clr, pre;
   integer clk_cycle = 20;
   integer half_cycle = 10;

   PIPELINE u_pipeline(clk, clr, pre);

   always  #(half_cycle)  clk = ~clk;
   
   initial
     begin
        clk = 0;
        clr = 1;
        pre = 1;
//        # clk_cycle
//        clr = 0;
//        # (clk_cycle -2)
//        clr = 1;
//        #clk_cycle
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

     end 


   initial #(10 * clk_cycle) $finish;
   
   initial
     begin
        $vcdplusfile("pipeline.dump.vpd");
        $vcdpluson(0, TOP);
     end

    // Initializing the control store
   initial
     begin
        $readmemb("../control_store/rom0_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom1.mem);
        $readmemb("../control_store/rom0_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom1.mem);
        $readmemb("../control_store/rom1_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom2.mem);
        $readmemb("../control_store/rom1_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom2.mem);
        $readmemb("../control_store/rom2_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom3.mem);
        $readmemb("../control_store/rom2_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom3.mem);
        $readmemb("../control_store/rom3_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom4.mem);
        $readmemb("../control_store/rom3_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom4.mem);
        $readmemb("../control_store/rom4_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom5.mem);
        $readmemb("../control_store/rom4_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom5.mem);
        $readmemb("../control_store/rom5_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom6.mem);
        $readmemb("../control_store/rom5_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom6.mem);
        $readmemb("../control_store/rom6_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom7.mem);
        $readmemb("../control_store/rom6_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom7.mem);
        $readmemb("../control_store/rom7_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom8.mem);
        $readmemb("../control_store/rom7_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom8.mem);
        $readmemb("../control_store/rom8_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom9.mem);
        $readmemb("../control_store/rom8_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom9.mem);
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
//        $strobe ("at time %0d, AG_MEM_WR_ADDR_OUT = %h", $time, u_pipeline.u_address_generation.MEM_WB_ADDR_OUT);
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

/*
        // EXECUTE STAGE SIGNALS
        $strobe ("at time %0d, EX_WB_V_next = %h", $time, u_pipeline.u_execute.WB_V_next);
        $strobe ("at time %0d, EX_WB_NEIP_next = %h", $time, u_pipeline.u_execute.WB_NEIP_next);
        $strobe ("at time %0d, EX_WB_NCS_next = %h", $time, u_pipeline.u_execute.WB_NCS_next);
        $strobe ("at time %0d, EX_WB_CONTROL_STORE_next = %h", $time, u_pipeline.u_execute.WB_CONTROL_STORE_next);
        $strobe ("at time %0d, EX_WB_de_datasize_all_next = %h", $time, u_pipeline.u_execute.WB_de_datasize_all_next);
        $strobe ("at time %0d, EX_WB_de_aluk_ex_next = %h", $time, u_pipeline.u_execute.WB_de_aluk_ex_next);
        $strobe ("at time %0d, EX_WB_de_ld_gpr1_wb_next = %h", $time, u_pipeline.u_execute.WB_de_ld_gpr1_wb_next);
        $strobe ("at time %0d, EX_WB_de_dcache_write_wb_next = %h", $time, u_pipeline.u_execute.WB_de_dcache_write_wb_next);
        $strobe ("at time %0d, EX_WB_de_flags_affected_wb_next = %h", $time, u_pipeline.u_execute.WB_de_flags_affected_wb_next);
        $strobe ("at time %0d, EX_WB_ALU32_RESULT_next = %h", $time, u_pipeline.u_execute.WB_ALU32_RESULT_next);
        $strobe ("at time %0d, EX_WB_FLAGS_next = %h", $time, u_pipeline.u_execute.WB_FLAGS_next);
        $strobe ("at time %0d, EX_WB_CMPS_POINTER_next = %h", $time, u_pipeline.u_execute.WB_CMPS_POINTER_next);
        $strobe ("at time %0d, EX_WB_COUNT_next = %h", $time, u_pipeline.u_execute.WB_COUNT_next);
        $strobe ("at time %0d, EX_WB_DR1_next = %h", $time, u_pipeline.u_execute.WB_DR1_next);
        $strobe ("at time %0d, EX_WB_DR2_next = %h", $time, u_pipeline.u_execute.WB_DR2_next);
        $strobe ("at time %0d, EX_WB_DR3_next = %h", $time, u_pipeline.u_execute.WB_DR3_next);

        // WRITEBACK SIGNALS
        $strobe ("at time %0d, WB_Out_DR1 = %h", $time, u_pipeline.u_writeback.Out_DR1);
        $strobe ("at time %0d, WB_Out_DR2 = %h", $time, u_pipeline.u_writeback.Out_DR2);
        $strobe ("at time %0d, WB_Out_DR3 = %h", $time, u_pipeline.u_writeback.Out_DR3);
        $strobe ("at time %0d, WB_Out_DR1_Data = %h", $time, u_pipeline.u_writeback.Out_DR1_Data);
        $strobe ("at time %0d, WB_Out_DR2_Data = %h", $time, u_pipeline.u_writeback.Out_DR2_Data);
        $strobe ("at time %0d, WB_Out_DR3_Data = %h", $time, u_pipeline.u_writeback.Out_DR3_Data);
        $strobe ("at time %0d, WB_out_v_de_ld_gpr1_wb = %h", $time, u_pipeline.u_writeback.out_v_de_ld_gpr1_wb);
        $strobe ("at time %0d, WB_out_v_cs_ld_gpr2_wb = %h", $time, u_pipeline.u_writeback.out_v_cs_ld_gpr2_wb);
        $strobe ("at time %0d, WB_out_v_cs_ld_gpr3_wb = %h", $time, u_pipeline.u_writeback.out_v_cs_ld_gpr3_wb);
        $strobe ("at time %0d, WB_out_de_datasize = %h", $time, u_pipeline.u_writeback.out_de_datasize);
        $strobe ("at time %0d, WB_Out_Dcache_Data = %h", $time, u_pipeline.u_writeback.Out_Dcache_Data);
        $strobe ("at time %0d, WB_Out_Dcache_Address = %h", $time, u_pipeline.u_writeback.Out_Dcache_Address);
        $strobe ("at time %0d, WB_Out_ex_repne_termination_all = %h", $time, u_pipeline.u_writeback.Out_ex_repne_termination_all);
*/
    end

   
endmodule

module PIPELINE(CLK, CLR, PRE);
   //connect this to simulator
    input CLK, CLR, PRE;
    assign EN = 1;//placeholder until stalls are working correctly
   
    //signals from EX to Dependency Checks
    wire DEP_v_ex_ld_gpr1;
    wire DEP_v_ex_ld_gpr2;
    wire DEP_v_ex_ld_gpr3;
    wire Dep_v_ex_ld_seg;
    wire Dep_v_ex_ld_mm;
    wire Dep_v_ex_dcache_write;
    //signals from WB to Dependency Checks
    wire DEP_v_wb_ld_gpr1;
    wire DEP_v_wb_ld_gpr2;
    wire DEP_v_wb_ld_gpr3;
    wire DEP_v_wb_ld_seg;
    wire DEP_v_wb_ld_mm;
    wire DEP_v_wb_dcache_write;
    //signals from WB to dcache
    wire [2:0] WB_Final_DR1;
    wire [2:0] WB_Final_DR2;
    wire [2:0] WB_Final_DR3;
    wire [31:0] WB_Final_data1;
    wire [31:0] WB_Final_data2;
    wire [31:0] WB_Final_data3;
    wire WB_Final_ld_gpr1;
    wire WB_Final_ld_gpr2;
    wire WB_Final_ld_gpr3;
    wire [1:0] WB_Final_datasize;
    wire WB_Final_ld_seg; 
    wire [63:0] WB_Final_MM_Data;
    wire WB_Final_ld_mm; 
    wire [31:0] WB_Final_EIP; 
    wire WB_Final_ld_eip; 
    wire [63:0] WB_Final_Dcache_Data;
    wire [31:0] WB_Final_Dcache_address;
    //signals from d-cache needed by WB
    wire In_write_ready = 1'b1; //Steven 
    //WB outputs
    wire wb_halt_all;
    wire wb_repne_terminate_all;
    wire WB_stall;
    //Dataforwarded, currently for daa
    wire CF_dataforwarded;
    wire AF_dataforwarded; 
   
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
    wire [15:0] DE_OPCODE_IN, DE_CS_IN;
    wire [31:0] DE_EIP_IN, DE_EIP_OUT, DE_EIP_OUT_BAR;
    wire [127:0] IR_IN;
    //Debug - change reg to wire
    //wire [127:0] IR;
    reg [127:0] IR = 128'h83c00a00000000000000000000000000;
    wire [3:0] DE_INSTR_LENGTH_UPDT_IN;

    //fetch u_fetch(
    //    CLK, PRE, CLR, 
    //    FE_EIP_IN, 
    //    IC_DOUT, 
    //    IC_R,
    //	      
    //    FE_JMP_FP, FE_TRAP_FP,
    //    CSDOUT,
    //    FE_FP_MUX,
    //    FE_LD_EIP,
    //
    //    DE_EIP_IN,
    //    DE_CS_IN,
    //    IC_EN,
    //    IC_PADDR,
    //    FE_SEG_LIM_EXC,
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
    //
    //    IR_OUT,
    //); 

    decode_stage1 u_decode_stage1 (
        CLK, PRE, CLR,
        IR,
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

    // reg32e$ IR_1(CLK, IR_IN[63:32], IR_OUT[63:32], IR_BAR_OUT[63:32], CLR, PRE, EN);
   reg32e$
      u_reg_ag_ps_in1 (CLK, D2_OUT1_AG_PS, AG_PS_IN1, , CLR, PRE, LD_AG),
      u_reg_ag_ps_imm32 (CLK, D2_IMM32_OUT, AG_PS_IMM32, , CLR, PRE, LD_AG),
      u_reg_ag_ps_disp32 (CLK, D2_DISP32_OUT, AG_PS_DISP32, , CLR, PRE, LD_AG);

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
     
   wire NextV;
    address_generation u_address_generation (CLK, PRE, CLR, NextV,
        // s from pipestage latches
        AG_PS_EIP, AG_PS_CS, AG_PS_CONTROL_STORE, AG_PS_OFFSET,
        AG_PS_DATA_SIZE, AG_PS_D2_SR1_NEEDED_AG, AG_PS_D2_SEG1_NEEDED_AG, AG_PS_D2_MM1_NEEDED_AG,
        AG_PS_D2_MEM_RD_ME, AG_PS_D2_MEM_WR_ME,
        AG_PS_D2_ALUK_EX, AG_PS_D2_LD_GPR1_WB, AG_PS_D2_LD_MM_WB,
        AG_PS_SR1, AG_PS_SR2, AG_PS_SR3, AG_PS_SIB_I, AG_PS_SEG1, AG_PS_SEG2,
        AG_PS_IMM32, AG_PS_DISP32,
        AG_PS_DE_SIB_EN_AG, AG_PS_DE_DISP_EN_AG, AG_PS_DE_BASE_REG_EN_AG,
        AG_PS_DE_MUX_SEG_AG, AG_PS_DE_CMPXCHG_AG,
        AG_PS_DE_SIB_S_AG,

        // s from register file
        SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA,
        SEG1_DATA, SEG2_DATA, MM1_DATA, MM2_DATA,

        // s from exception/interrupt logic
        DE_EXC_CODE_AG,

        // dependency check s
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
        AG_DEP_STALL_OUT, AG_SEG_LIMIT_EXC_OUT
    );

   wire [31:0] ME_PS_NEIP;
   wire [15:0] ME_PS_NCS, ME_PS_NCS_NC;
   wire [127:0] ME_PS_CONTROL_STORE;
   wire [127:0] ME_PS_CONTROL_STORE_OUT;

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
   // Placeholder for ME
   assign LD_ME=1;
   wire [31:0] AG_NCS_OUT32;
   wire [127:0] AG_CONTROL_STORE;

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
   
    wire V;
    memory_stage u_memory_stage (CLK, CLR, PRE, V,
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
        ME_DRID1_OUT, ME_DRID2_OUT, ME_D2_MEM_WR_WB_OUT, ME_D2_LD_GPR1_WB_OUT, ME_D2_LD_MM_WB_OUT
    );
   
    //register between ME and EX
    //reg32e$(CLK, Din, Q, QBAR, CLR, PRE,en);
    //reg32e$ REG_DEST_COM(CLK, {{31{1'b0}},REG_DEST_COM_IN}, D_REG_DEST, D_3, CLR, PRE, EN);
    //EX s
    wire EX_V_next = 1'b1; // TODO
    // CHeck whether the /output is properly connected - TODO
    wire [31:0] EX_V_out; 
    reg32e$ u_EX_v_latch(CLK, {{31{1'b0}}, EX_V_next}, EX_V_out, ,CLR,PRE,EN); 
    wire EX_V;
    assign EX_V = EX_V_out[0]; 

    wire [31:0] EX_NEIP_next = ME_NEIP_OUT;
    wire [31:0] EX_NEIP;
    reg32e$ u_EX_neip_latch(CLK, EX_NEIP_next, EX_NEIP, ,CLR,PRE,EN);

    wire [15:0] EX_NCS_next = ME_NCS_OUT;
    wire [31:0] EX_NCS_out; 
    wire [15:0] EX_NCS;    
    reg32e$ u_EX_ncs_latch(CLK, {{16{1'b0}}, EX_NCS_next}, EX_NCS_out, ,CLR,PRE,EN); 
    assign EX_NCS = EX_NCS_out[15:0]; 

    wire [127:0] EX_CONTROL_STORE_next = ME_CONTROL_STORE_OUT;
    wire [127:0] EX_CONTROL_STORE;
    reg64e$ u_EX_control_store_latch1(CLK, EX_CONTROL_STORE_next[63:0], EX_CONTROL_STORE[63:0], ,CLR,PRE,EN);
    reg64e$ u_EX_control_store_latch2(CLK, EX_CONTROL_STORE_next[127:64], EX_CONTROL_STORE[127:64], ,CLR,PRE,EN);

    wire [1:0] EX_de_datasize_all_next = ME_DATA_SIZE_OUT; 
    wire [31:0] EX_de_datasize_all_out;
    wire [1:0] EX_de_datasize_all;
    reg32e$ u_EX_de_datasize_all_all(CLK, {30'b0,EX_de_datasize_all_next}, EX_de_datasize_all_out, ,CLR,PRE,EN);
    assign EX_de_datasize_all = EX_de_datasize_all_out[1:0]; 

    wire [2:0] EX_de_aluk_ex_next = ME_D2_ALUK_EX_OUT;
    wire [31:0] EX_de_aluk_ex_out;
    wire [2:0] EX_de_aluk_ex; 
    reg32e$ u_EX_de_aluk_ex_latch(CLK, {29'b0, EX_de_aluk_ex_next}, EX_de_aluk_ex_out, ,CLR,PRE,EN);
    assign EX_de_aluk_ex = EX_de_aluk_ex_out[2:0]; 

    wire EX_de_shift_dir_ex_next = 3'b0; //Nelson
    wire [31:0] EX_de_shift_dir_ex_out;
    wire EX_de_shift_dir_ex;
    reg32e$ u_EX_de_shift_dir_ex_latch(CLK, {31'b0, EX_de_shift_dir_ex_next}, EX_de_shift_dir_ex_out, ,CLR,PRE,EN);
    assign EX_de_shift_dir_ex = EX_de_shift_dir_ex_out[0]; 

    wire EX_de_ld_gpr1_ex_next = ME_D2_LD_GPR1_WB_OUT;
    wire [31:0] EX_de_ld_gpr1_ex_out;
    wire EX_de_ld_gpr1_ex;
    reg32e$ u_EX_de_ld_gpr1_wb_latch (CLK, {31'b0, EX_de_ld_gpr1_ex_next}, EX_de_ld_gpr1_ex_out, ,CLR,PRE,EN);
    assign EX_de_ld_gpr1_ex = EX_de_ld_gpr1_ex_out[0]; 

    wire EX_de_dcache_write_ex_next = ME_D2_MEM_WR_WB_OUT;
    wire [31:0] EX_de_dcache_write_ex_out;
    wire EX_de_dcache_write_ex; 
    reg32e$ u_EX_de_dcache_write_wb_latch(CLK, {31'b0, EX_de_dcache_write_ex_next}, EX_de_dcache_write_ex_out, ,CLR,PRE,EN);
    assign EX_de_dcache_write_ex = EX_de_dcache_write_ex_out[0]; 

    wire EX_de_repne_wb_next = 1'b0; //Nelson
    wire [31:0] EX_de_repne_wb_out; 
    wire EX_de_repne_wb; 
    reg32e$ u_EX_de_repne_wb_latch(CLK, {31'b0, EX_de_repne_wb_next}, EX_de_repne_wb_out, ,CLR,PRE,EN);
    assign EX_de_repne_wb = EX_de_repne_wb_out[0]; 

    wire [31:0] EX_A_next = ME_A_OUT;
    wire [31:0] EX_B_next = ME_B_OUT;
    wire [31:0] EX_C_next = 32'b00000000; //Nelson
    wire [31:0] EX_A, EX_B, EX_C;
    reg32e$ u_EX_a_latch(CLK, EX_A_next, EX_A, ,CLR,PRE,EN);
    reg32e$ u_EX_b_latch(CLK, EX_B_next, EX_B, ,CLR,PRE,EN);
    reg32e$ u_EX_c_latch(CLK, EX_C_next, EX_C, ,CLR,PRE,EN);

    wire [63:0] EX_MM_A_next = ME_MM_A_OUT;
    wire [63:0] EX_MM_B_next = ME_MM_B_OUT;
    wire [63:0] EX_MM_A, EX_MM_B;
    reg64e$ u_EX_mm_a_latch(CLK, EX_MM_A_next, EX_MM_A, ,CLR,PRE,EN);
    reg64e$ u_EX_mm_b_latch(CLK, EX_MM_B_next, EX_MM_B, ,CLR,PRE,EN);

    wire [2:0] EX_DR1_next = ME_DRID1_OUT;
    wire [2:0] EX_DR2_next = ME_DRID2_OUT;
    // TODO - What is it assigned from? //Jiahan
    wire [2:0] EX_DR3_next;
    wire [31:0] EX_DR1_out, EX_DR2_out, EX_DR3_out;
    wire [2:0] EX_DR1, EX_DR2, EX_DR3;
    reg32e$ u_EX_dr1_latch(CLK, {29'b0, EX_DR1_next}, EX_DR1_out, ,CLR,PRE,EN);
    reg32e$ u_EX_dr2_latch(CLK, {29'b0, EX_DR2_next}, EX_DR2_out, ,CLR,PRE,EN);
    reg32e$ u_EX_dr3_latch(CLK, {29'b0, EX_DR3_next}, EX_DR3_out, ,CLR,PRE,EN);
    assign EX_DR1 = EX_DR1_out[2:0]; 
    assign EX_DR2 = EX_DR2_out[2:0]; 
    assign EX_DR3 = EX_DR3_out[2:0]; 

    wire [31:0] EX_ADDRESS_next = ME_MEM_WR_ADDR_OUT;
    wire [31:0] EX_ADDRESS;
    reg32e$ u_EX_address_latch(CLK, EX_ADDRESS_next, EX_ADDRESS, ,CLR,PRE,EN);

    //******************************************************************************//
    //*
    //*                                Execute STAGE
    //*
    //*******************************************************************************//

    //Execute Outputs

    wire WB_V_next;
    wire [31:0] WB_NEIP_next; 
    wire [15:0] WB_NCS_next;
    wire [127:0] WB_CONTROL_STORE_next;

    wire [1:0] WB_de_datasize_all_next;
    wire WB_ex_ld_gpr1_wb_next;
    wire WB_ex_ld_gpr2_wb_next; 
    wire WB_ex_dcache_write_wb_next; 
    wire WB_de_repne_wb_next; 

    wire [31:0] WB_RESULT_A_next;
    wire [31:0] WB_RESULT_B_next;
    wire [31:0] WB_RESULT_C_next;
    wire [31:0] WB_FLAGS_next;
    wire [63:0] WB_RESULT_MM_next; 

    wire [2:0] WB_DR1_next;
    wire [2:0] WB_DR2_next;
    wire [2:0] WB_DR3_next;
    wire [31:0] WB_ADDRESS_next;   

    wire WB_ld_latches;

    execute u_execute(
        CLK, PRE, CLR, //not uesd SET/RST

        EX_V,
        EX_NEIP,
        EX_NCS,
        EX_CONTROL_STORE,
        //pseudo-control store signals not from control store but generated in decode
        EX_de_datasize_all,
        EX_de_aluk_ex, 
        EX_de_shift_dir_ex, 
        EX_de_ld_gpr1_ex,
        EX_de_dcache_write_ex, 
        EX_de_repne_wb, 

        //execute results
        EX_A, 
        EX_B, 
        EX_C,
        EX_MM_A, 
        EX_MM_B,

        EX_DR1, 
        EX_DR2,
        EX_DR3,
        EX_ADDRESS,

        WB_stall, 

        CF_dataforwarded,
        AF_dataforwarded,

        WB_V_next,
        WB_NEIP_next, 
        WB_NCS_next,
        WB_CONTROL_STORE_next,

        WB_de_datasize_all_next,
        WB_ex_ld_gpr1_wb_next,
        WB_ex_ld_gpr2_wb_next, 
        WB_ex_dcache_write_wb_next, 
        WB_de_repne_wb_next, 

        WB_RESULT_A_next,
        WB_RESULT_B_next,
        WB_RESULT_C_next,
        WB_FLAGS_next,
        WB_RESULT_MM_next, 

        WB_DR1_next,
        WB_DR2_next,
        WB_DR3_next,
        WB_ADDRESS_next,   

        DEP_v_ex_ld_gpr1,
        DEP_v_ex_ld_gpr2,
        DEP_v_ex_ld_gpr3,
        Dep_v_ex_ld_seg,
        Dep_v_ex_ld_mm,
        Dep_v_ex_dcache_write,

        WB_ld_latches
    );


    //register between EX and WB
    wire [31:0] WB_V_out;
    wire WB_V; 
    reg32e$ u_WB_v_latch(CLK, {{31{1'b0}}, WB_V_next}, WB_V_out, ,CLR,PRE,EN); 
    assign WB_V = WB_V_out[0]; 

    wire [31:0] WB_NEIP;
    reg32e$ u_WB_neip_latch(CLK, WB_NEIP_next, WB_NEIP, ,CLR,PRE,EN);

    wire [31:0] WB_NCS_out;
    wire [15:0] WB_NCS;
    reg32e$ u_WB_ncs_latch(CLK, {16'b0, WB_NCS_next}, WB_NCS_out, ,CLR,PRE,EN);
    assign WB_NCS = WB_NCS_out[15:0];

    wire [127:0] WB_CONTROL_STORE;
    reg64e$ u_WB_control_store_latch1 (CLK, WB_CONTROL_STORE_next[127:64], WB_CONTROL_STORE[127:64], ,CLR,PRE,EN);
    reg64e$ u_WB_control_store_latch2 (CLK, WB_CONTROL_STORE_next[63:0], WB_CONTROL_STORE[63:0], ,CLR,PRE,EN);

    wire [31:0] WB_de_datasize_all_out; 
    wire [1:0] WB_de_datasize_all; 
    reg32e$ u_WB_de_datasize_all_latch(CLK, {30'b0, WB_de_datasize_all_next}, WB_de_datasize_all_out, ,CLR,PRE,EN);
    assign WB_de_datasize_all = WB_de_datasize_all_out[1:0]; 

    wire [31:0] WB_ex_ld_gpr1_wb_out; 
    wire WB_ex_ld_gpr1_wb; 
    reg32e$ u_WB_ex_ld_gpr1_wb_latch(CLK, {31'b0, WB_ex_ld_gpr1_wb}, WB_ex_ld_gpr1_wb_out, ,CLR,PRE,EN);
    assign WB_ex_ld_gpr1_wb = WB_ex_ld_gpr1_wb_out[0]; 

    wire [31:0] WB_ex_ld_gpr2_wb_out; 
    wire WB_ex_ld_gpr2_wb; 
    reg32e$ u_WB_ex_ld_gpr2_wb_latch(CLK, {31'b0, WB_ex_ld_gpr2_wb}, WB_ex_ld_gpr2_wb_out, ,CLR,PRE,EN);
    assign WB_ex_ld_gpr2_wb = WB_ex_ld_gpr2_wb_out[0]; 

    wire [31:0] WB_ex_dcache_write_wb_out; 
    wire WB_ex_dcache_write_wb; 
    reg32e$ u_WB_ex_dcache_write_wb_latch(CLK, {31'b0, WB_ex_dcache_write_wb}, WB_ex_dcache_write_wb_out, ,CLR,PRE,EN);
    assign WB_ex_dcache_write_wb = WB_ex_dcache_write_wb_out[0]; 

    wire [31:0] WB_de_repne_wb_out; 
    wire WB_de_repne_wb; 
    reg32e$ u_WB_de_repne_wb_latch(CLK, {31'b0, WB_de_repne_wb}, WB_de_repne_wb_out, ,CLR,PRE,EN);
    assign WB_de_repne_wb = WB_de_repne_wb_out[0]; 

    wire [31:0] WB_RESULT_A;
    reg32e$ u_WB_RESULT_A_latch(CLK, WB_RESULT_A_next, WB_RESULT_A, ,CLR,PRE,EN);

    wire [31:0] WB_RESULT_B;
    reg32e$ u_WB_RESULT_B_latch(CLK, WB_RESULT_B_next, WB_RESULT_B, ,CLR,PRE,EN);

    wire [31:0] WB_RESULT_C;
    reg32e$ u_WB_RESULT_C_latch(CLK, WB_RESULT_C_next, WB_RESULT_C, ,CLR,PRE,EN);

    wire [31:0] WB_FLAGS;
    reg32e$ u_WB_FLAGS_latch(CLK, WB_FLAGS_next, WB_FLAGS, ,CLR,PRE,EN);

    wire [63:0] WB_RESULT_MM; 
    reg64e$ u_WB_RESULT_MM_latch(CLK, WB_RESULT_MM_next, WB_RESULT_MM, ,CLR,PRE,EN);

    wire [31:0] WB_DR1_out, WB_DR2_out, WB_DR3_out;
    wire [2:0] WB_DR1, WB_DR2, WB_DR3;
    reg32e$ u_WB_DR1_latch(CLK, {29'b0, WB_DR1_next}, WB_DR1_out, ,CLR,PRE,EN);
    reg32e$ u_WB_DR2_latch(CLK, {29'b0, WB_DR2_next}, WB_DR2_out, ,CLR,PRE,EN);
    reg32e$ u_WB_DR3_latch(CLK, {29'b0, WB_DR3_next}, WB_DR3_out, ,CLR,PRE,EN);
    assign WB_DR1 = WB_DR1_next[2:0];
    assign WB_DR2 = WB_DR2_next[2:0];
    assign WB_DR3 = WB_DR3_next[2:0];

    wire [31:0] WB_ADDRESS; 
    reg32e$ u_WB_ADDRESS_latch(CLK, WB_ADDRESS_next, WB_ADDRESS, ,CLR,PRE,EN);

    //******************************************************************************//
    //*
    //*                                Writeback STAGE
    //*
    //*******************************************************************************//

    writeback u_writeback(
        CLK, PRE, CLR, //not uesd SET/RST

        WB_V,
        WB_NEIP,
        WB_NCS,
        WB_CONTROL_STORE,
       //pseudo-control store signals not from control store but generated in decode
        WB_de_datasize_all,
        WB_ex_ld_gpr1_wb,
        WB_ex_ld_gpr2_wb,
        WB_ex_dcache_write_wb,
        WB_de_repne_wb, 

        WB_RESULT_A, 
        WB_RESULT_B, 
        WB_RESULT_C,
        WB_FLAGS,
        WB_RESULT_MM,

        WB_DR1,
        WB_DR2,
        WB_DR3,
        WB_ADDRESS,

        In_write_ready, 

        WB_Final_DR1,
        WB_Final_DR2,
        WB_Final_DR3,
        WB_Final_data1,
        WB_Final_data2,
        WB_Final_data3,
        WB_Final_ld_gpr1,
        WB_Final_ld_gpr2,
        WB_Final_ld_gpr3,
        WB_Final_datasize,
        WB_Final_ld_seg, 
        WB_Final_MM_Data,
        WB_Final_ld_mm, 
        WB_Final_EIP, 
        WB_Final_ld_eip, 
        WB_Final_Dcache_Data,
        WB_Final_Dcache_address,

        DEP_v_wb_ld_gpr1,
        DEP_v_wb_ld_gpr2,
        DEP_v_wb_ld_gpr3,
        DEP_v_wb_ld_seg,
        DEP_v_wb_ld_mm,
        DEP_v_wb_dcache_write,

        wb_halt_all, 
        wb_repne_terminate_all,
        WB_stall,
        CF_dataforwarded,
        AF_dataforwarded
    );

endmodule
