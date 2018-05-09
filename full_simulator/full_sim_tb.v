`timescale 1ns/1ps
`include "../pipeline/constants.v"
`define EOF = 32'hFFFF_FFFF
`define NULL 0

module TOP;
    reg clk, bus_clk, clr, pre;
    integer clk_cycle = 14;
    integer half_cycle = 7;

    FULL_SIMULATOR u_full_simulator (clk, bus_clk, clr, pre);

    initial begin
        clk = 0;
        bus_clk = 0;
        clr = 0;
        pre = 1;
        repeat(2) #clk_cycle //wait 2 clock cycles
        clr = 1;
        forever #(half_cycle)  clk = ~clk;
    end

    initial begin
        repeat(2) #clk_cycle;
        #half_cycle;
        forever #(clk_cycle) bus_clk = ~bus_clk;
    end
    
     initial #6000 $finish;

     always @(posedge clk) begin
         $strobe ("at time %0d, IR = %h", $time, u_full_simulator.u_pipeline.u_fetch.CURRENT_IR);
         $strobe ("at time %0d, read_ptr = %h", $time, u_full_simulator.u_pipeline.u_fetch.read_ptr);
         $strobe ("at time %0d, instr_length_updt = %h", $time, u_full_simulator.u_pipeline.u_fetch.instr_length_updt);
         $strobe ("at time %0d, Opcode = %h", $time, u_full_simulator.u_pipeline.u_fetch.opcode);

         if(u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_gpr1 === 1'b1) begin 
          $strobe ("at time %0d, GPR b%b = h%h | datasize = b%b", $time, u_full_simulator.u_pipeline.u_writeback.WB_Final_DR1, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_data1, u_full_simulator.u_pipeline.u_writeback.WB_Final_datasize);
         end

        if(u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_gpr2 === 1'b1) begin 
          $strobe ("at time %0d, GPR b%b = h%h | datasize = b%b", $time, u_full_simulator.u_pipeline.u_writeback.WB_Final_DR2, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_data2, u_full_simulator.u_pipeline.u_writeback.WB_Final_datasize);
         end

        if(u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_gpr3 === 1'b1) begin 
          $strobe ("at time %0d, GPR b%b = h%h | datasize = b%b", $time, u_full_simulator.u_pipeline.u_writeback.WB_Final_DR3, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_data3, u_full_simulator.u_pipeline.u_writeback.WB_Final_DR3_datasize);
         end

         if(u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_seg === 1'b1) begin 
          $strobe ("at time %0d, SEGR b%b = h%h | datasize = b%b", $time, u_full_simulator.u_pipeline.u_writeback.WB_Final_DR1, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_data1, 2'b01);
         end

         if(u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_mm === 1'b1) begin 
          $strobe ("at time %0d, MM b%b = h%h | datasize = b%b", $time, u_full_simulator.u_pipeline.u_writeback.WB_Final_DR1, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_MM_Data, 2'b11);
         end

        if(u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_eip === 1'b1) begin 
          $strobe ("\nat time %0d, EIP = h%h | datasize = b%b", $time,
            u_full_simulator.u_pipeline.u_writeback.WB_Final_EIP, 2'b10);
         end

        if(u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_cs === 1'b1) begin 
          $strobe ("at time %0d, CS = h%h| datasize = b%b", $time, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_CS, 2'b01);
         end

        if(u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_flags === 1'b1) begin 
          
          $strobe ("at time %0d, OF = %b", $time, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_Flags[11]);
          $strobe ("at time %0d, DF = %b", $time, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_Flags[10]);
          $strobe ("at time %0d, SF = %b", $time, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_Flags[7]);
          $strobe ("at time %0d, ZF = %b", $time, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_Flags[6]);
          $strobe ("at time %0d, AF = %b", $time, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_Flags[4]);
          $strobe ("at time %0d, PF = %b", $time, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_Flags[2]);
          $strobe ("at time %0d, CF = %b", $time, 
            u_full_simulator.u_pipeline.u_writeback.WB_Final_Flags[0]);

        end

        if(u_full_simulator.u_pipeline.u_writeback.WB_Final_Dcache_Write === 1'b1) begin 
          $strobe ("at time %0d, Dcache Address: h%h = h%h| datasize = b%b", $time, u_full_simulator.u_pipeline.u_writeback.WB_Final_Dcache_Address,
            u_full_simulator.u_pipeline.u_writeback.WB_Final_Dcache_Data, u_full_simulator.u_pipeline.u_writeback.WB_Final_datasize);
        end


     end



//  TLB ENTRY        VPN        RPN        V     PRE   R/W   PCD
`define TLB_ENTRY_0 {20'h00000, 20'h00000, 1'b1, 1'b1, 1'b0, 1'b0}
`define TLB_ENTRY_1 {20'h02000, 20'h00002, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_2 {20'h04000, 20'h00005, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_3 {20'h0b000, 20'h00004, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_4 {20'h0c000, 20'h00007, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_5 {20'h0a000, 20'h00005, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_6 {20'h10000, 20'h10000, 1'b1, 1'b0, 1'b1, 1'b1}
`define TLB_ENTRY_7 {20'h02001, 20'h2FFFF, 1'b1, 1'b0, 1'b1, 1'b1}
   initial
      begin
         u_full_simulator.u_pipeline.u_fetch.u_ifu.itlb.ENTRY[0] = `TLB_ENTRY_0;
         u_full_simulator.u_pipeline.u_fetch.u_ifu.itlb.ENTRY[1] = `TLB_ENTRY_1;
         u_full_simulator.u_pipeline.u_fetch.u_ifu.itlb.ENTRY[2] = `TLB_ENTRY_2;
         u_full_simulator.u_pipeline.u_fetch.u_ifu.itlb.ENTRY[3] = `TLB_ENTRY_3;
         u_full_simulator.u_pipeline.u_fetch.u_ifu.itlb.ENTRY[4] = `TLB_ENTRY_4;
         u_full_simulator.u_pipeline.u_fetch.u_ifu.itlb.ENTRY[5] = `TLB_ENTRY_5;
         u_full_simulator.u_pipeline.u_fetch.u_ifu.itlb.ENTRY[6] = `TLB_ENTRY_6;
         u_full_simulator.u_pipeline.u_fetch.u_ifu.itlb.ENTRY[7] = `TLB_ENTRY_7;
      end
   initial
      begin
         u_full_simulator.u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[0] = `TLB_ENTRY_0;
         u_full_simulator.u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[1] = `TLB_ENTRY_1;
         u_full_simulator.u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[2] = `TLB_ENTRY_2;
         u_full_simulator.u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[3] = `TLB_ENTRY_3;
         u_full_simulator.u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[4] = `TLB_ENTRY_4;
         u_full_simulator.u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[5] = `TLB_ENTRY_5;
         u_full_simulator.u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[6] = `TLB_ENTRY_6;
         u_full_simulator.u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[7] = `TLB_ENTRY_7;
      end


   initial begin
       $vcdplusfile("pipeline.dump.vpd");
       $vcdpluson(0, TOP);
   end

    // Initializing the control store
    initial begin
        $readmemb("../pipeline/control_store/rom0_0.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom1.mem);
        $readmemb("../pipeline/control_store/rom0_1.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom1.mem);
        $readmemb("../pipeline/control_store/rom1_0.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom2.mem);
        $readmemb("../pipeline/control_store/rom1_1.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom2.mem);
        $readmemb("../pipeline/control_store/rom2_0.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom3.mem);
        $readmemb("../pipeline/control_store/rom2_1.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom3.mem);
        $readmemb("../pipeline/control_store/rom3_0.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom4.mem);
        $readmemb("../pipeline/control_store/rom3_1.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom4.mem);
        $readmemb("../pipeline/control_store/rom4_0.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom5.mem);
        $readmemb("../pipeline/control_store/rom4_1.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom5.mem);
        $readmemb("../pipeline/control_store/rom5_0.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom6.mem);
        $readmemb("../pipeline/control_store/rom5_1.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom6.mem);
        $readmemb("../pipeline/control_store/rom6_0.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom7.mem);
        $readmemb("../pipeline/control_store/rom6_1.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom7.mem);
        $readmemb("../pipeline/control_store/rom7_0.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom8.mem);
        $readmemb("../pipeline/control_store/rom7_1.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom8.mem);
        $readmemb("../pipeline/control_store/rom8_0.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom9.mem);
        $readmemb("../pipeline/control_store/rom8_1.list", u_full_simulator.u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom9.mem);
    end


    initial begin
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram0.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram0.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram1.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram1.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram2.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram2.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram3.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram3.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram4.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram4.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram5.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram5.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram6.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram6.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram7.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram7.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram8.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram8.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram9.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram9.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram10.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram10.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram11.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram11.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram12.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram12.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram13.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram13.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram14.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram14.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram15.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram15.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram16.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram16.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram17.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram17.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram18.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram18.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram19.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram19.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram20.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram20.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram21.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram21.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram22.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram22.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram23.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram23.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram24.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram24.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram25.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram25.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram26.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram26.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram27.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram27.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram28.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram28.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram29.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram29.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram30.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram30.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line0_sram31.list", u_full_simulator.u_full_memory.main_memory_u.blk_line0.sram31.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram0.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram0.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram1.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram1.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram2.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram2.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram3.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram3.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram4.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram4.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram5.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram5.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram6.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram6.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram7.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram7.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram8.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram8.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram9.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram9.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram10.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram10.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram11.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram11.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram12.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram12.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram13.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram13.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram14.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram14.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram15.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram15.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram16.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram16.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram17.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram17.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram18.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram18.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram19.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram19.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram20.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram20.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram21.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram21.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram22.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram22.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram23.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram23.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram24.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram24.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram25.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram25.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram26.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram26.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram27.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram27.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram28.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram28.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram29.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram29.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram30.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram30.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line1_sram31.list", u_full_simulator.u_full_memory.main_memory_u.blk_line1.sram31.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram0.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram0.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram1.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram1.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram2.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram2.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram3.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram3.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram4.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram4.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram5.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram5.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram6.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram6.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram7.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram7.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram8.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram8.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram9.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram9.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram10.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram10.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram11.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram11.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram12.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram12.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram13.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram13.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram14.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram14.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram15.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram15.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram16.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram16.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram17.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram17.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram18.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram18.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram19.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram19.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram20.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram20.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram21.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram21.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram22.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram22.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram23.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram23.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram24.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram24.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram25.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram25.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram26.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram26.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram27.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram27.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram28.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram28.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram29.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram29.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram30.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram30.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line2_sram31.list", u_full_simulator.u_full_memory.main_memory_u.blk_line2.sram31.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram0.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram0.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram1.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram1.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram2.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram2.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram3.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram3.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram4.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram4.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram5.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram5.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram6.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram6.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram7.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram7.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram8.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram8.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram9.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram9.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram10.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram10.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram11.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram11.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram12.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram12.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram13.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram13.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram14.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram14.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram15.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram15.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram16.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram16.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram17.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram17.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram18.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram18.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram19.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram19.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram20.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram20.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram21.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram21.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram22.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram22.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram23.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram23.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram24.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram24.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram25.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram25.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram26.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram26.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram27.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram27.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram28.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram28.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram29.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram29.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram30.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram30.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line3_sram31.list", u_full_simulator.u_full_memory.main_memory_u.blk_line3.sram31.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram0.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram0.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram1.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram1.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram2.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram2.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram3.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram3.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram4.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram4.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram5.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram5.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram6.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram6.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram7.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram7.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram8.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram8.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram9.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram9.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram10.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram10.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram11.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram11.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram12.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram12.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram13.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram13.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram14.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram14.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram15.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram15.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram16.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram16.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram17.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram17.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram18.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram18.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram19.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram19.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram20.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram20.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram21.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram21.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram22.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram22.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram23.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram23.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram24.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram24.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram25.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram25.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram26.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram26.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram27.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram27.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram28.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram28.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram29.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram29.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram30.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram30.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line4_sram31.list", u_full_simulator.u_full_memory.main_memory_u.blk_line4.sram31.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram0.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram0.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram1.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram1.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram2.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram2.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram3.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram3.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram4.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram4.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram5.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram5.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram6.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram6.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram7.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram7.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram8.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram8.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram9.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram9.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram10.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram10.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram11.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram11.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram12.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram12.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram13.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram13.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram14.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram14.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram15.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram15.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram16.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram16.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram17.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram17.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram18.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram18.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram19.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram19.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram20.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram20.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram21.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram21.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram22.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram22.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram23.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram23.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram24.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram24.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram25.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram25.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram26.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram26.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram27.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram27.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram28.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram28.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram29.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram29.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram30.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram30.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line5_sram31.list", u_full_simulator.u_full_memory.main_memory_u.blk_line5.sram31.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram0.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram0.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram1.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram1.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram2.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram2.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram3.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram3.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram4.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram4.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram5.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram5.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram6.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram6.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram7.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram7.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram8.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram8.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram9.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram9.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram10.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram10.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram11.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram11.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram12.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram12.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram13.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram13.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram14.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram14.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram15.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram15.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram16.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram16.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram17.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram17.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram18.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram18.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram19.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram19.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram20.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram20.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram21.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram21.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram22.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram22.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram23.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram23.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram24.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram24.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram25.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram25.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram26.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram26.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram27.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram27.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram28.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram28.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram29.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram29.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram30.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram30.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line6_sram31.list", u_full_simulator.u_full_memory.main_memory_u.blk_line6.sram31.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram0.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram0.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram1.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram1.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram2.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram2.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram3.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram3.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram4.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram4.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram5.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram5.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram6.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram6.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram7.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram7.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram8.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram8.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram9.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram9.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram10.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram10.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram11.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram11.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram12.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram12.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram13.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram13.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram14.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram14.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram15.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram15.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram16.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram16.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram17.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram17.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram18.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram18.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram19.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram19.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram20.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram20.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram21.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram21.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram22.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram22.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram23.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram23.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram24.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram24.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram25.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram25.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram26.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram26.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram27.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram27.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram28.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram28.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram29.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram29.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram30.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram30.mem);
        $readmemh("../memory/main_memory/sram_list/blk_line7_sram31.list", u_full_simulator.u_full_memory.main_memory_u.blk_line7.sram31.mem);
    end

endmodule
