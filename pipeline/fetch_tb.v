`include "constants.v"
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
   integer clk_cycle = 20;
   integer half_cycle = 10;

   // Signals for testbench loop
   integer file, char, retval, lineno, cntErrors;
   reg [15:0] opcode;
   reg [31:0] result;
   reg [7:0] prefix1, prefix2, prefix3, modrm, sib;
   reg [31:0] disp, imm, imm_compare, disp_compare;
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
    reg [2:0] SR1, SR2;
    reg [1:0] SR1_size, SR2_size;
    reg NextV;

    /************************************************************************/
    /*
                            BEHAVIOURAL REGISTER FILE 
                                                                           */
    /***********************************************************************/
    reg [31:0] reg_array[7:0];
    initial begin
        reg_array[0] = 32'h08000800;
        reg_array[1] = 32'h09010901;
        reg_array[2] = 32'h0A020A02;
        reg_array[3] = 32'h0B030B03;
        reg_array[4] = 32'h0C040C04;
        reg_array[5] = 32'h0D050D05;
        reg_array[6] = 32'h0E060E06;
        reg_array[7] = 32'h0F070F07;
    end

    reg [15:0] reg_array_seg[7:0];
    initial begin
        reg_array_seg[0] = 16'h08;
        reg_array_seg[1] = 16'h09;
        reg_array_seg[2] = 16'h0A;
        reg_array_seg[3] = 16'h0B;
        reg_array_seg[4] = 16'h0C;
        reg_array_seg[5] = 16'h0D;
        reg_array_seg[6] = 16'h0E;
        reg_array_seg[7] = 16'h0F;
    end

    reg [63:0] reg_array_mm[7:0];
    initial begin
        reg_array_seg[0] = 63'h08;
        reg_array_seg[1] = 63'h09;
        reg_array_seg[2] = 63'h0A;
        reg_array_seg[3] = 63'h0B;
        reg_array_seg[4] = 63'h0C;
        reg_array_seg[5] = 63'h0D;
        reg_array_seg[6] = 63'h0E;
        reg_array_seg[7] = 63'h0F;
    end


   PIPELINE u_pipeline(clk, clr, pre, IR);

    initial begin
        clk = 1;
        clr = 0;
        pre = 1;
        #(half_cycle)
        clr = 1;
        u_pipeline.u_icache.tagstore_u.valid_store.Q = 32'hFFFF_FFFF;
        u_pipeline.u_icache.state.Q = 16'h0001;
        u_pipeline.u_dcache.tagstore_u.valid_store.Q = 32'hFFFF_FFFF;
        u_pipeline.u_dcache.state.Q = 16'h0001;
        forever #(half_cycle)  clk = ~clk;
    end

    // Set the register values
    // reg0 = 32'h08000800
    // reg1 = 32'h09010901
    // reg2 = 32'h0A020A02
    // reg3 = 32'h0B030B03
    // reg4 = 32'h0C040C04
    // reg5 = 32'h0D050D05
    // reg6 = 32'h0E060E06
    // reg7 = 32'h0F070F07
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

//        u_pipeline.u_fetch.reg_read_ptr.Q = 32'h0000000;
//        u_pipeline.u_fetch.u_FE_buf_3.low.Q = 64'h81773D090CDB1283;
//        u_pipeline.u_fetch.u_FE_buf_2.low.Q = 64'h85BC148878235B49;
//        u_pipeline.u_fetch.u_FE_buf_1.low.Q = 64'h81773D090CDB1283;
//        u_pipeline.u_fetch.u_FE_buf_0.low.Q = 64'h85BC148878235B49;
//        u_pipeline.u_fetch.u_FE_buf_3.high.Q = 64'h0F6FEB254B212F96;
//        u_pipeline.u_fetch.u_FE_buf_2.high.Q = 64'h7E6D39201F21D322;
//        u_pipeline.u_fetch.u_FE_buf_1.high.Q = 64'h0F6FEB254B212F96;
//        u_pipeline.u_fetch.u_FE_buf_0.high.Q = 64'h7E6D39201F21D322;
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
     end 

     initial begin
        $readmemh("ram0_0.list", u_pipeline.u_icache.data_u.data_line0.ram0.mem);
        $readmemh("ram0_1.list", u_pipeline.u_icache.data_u.data_line0.ram1.mem);
        $readmemh("ram0_2.list", u_pipeline.u_icache.data_u.data_line0.ram2.mem);
        $readmemh("ram0_3.list", u_pipeline.u_icache.data_u.data_line0.ram3.mem);
        $readmemh("ram0_4.list", u_pipeline.u_icache.data_u.data_line0.ram4.mem);
        $readmemh("ram0_5.list", u_pipeline.u_icache.data_u.data_line0.ram5.mem);
        $readmemh("ram0_6.list", u_pipeline.u_icache.data_u.data_line0.ram6.mem);
        $readmemh("ram0_7.list", u_pipeline.u_icache.data_u.data_line0.ram7.mem);
        $readmemh("ram0_8.list", u_pipeline.u_icache.data_u.data_line0.ram8.mem);
        $readmemh("ram0_9.list", u_pipeline.u_icache.data_u.data_line0.ram9.mem);
        $readmemh("ram0_10.list", u_pipeline.u_icache.data_u.data_line0.ram10.mem);
        $readmemh("ram0_11.list", u_pipeline.u_icache.data_u.data_line0.ram11.mem);
        $readmemh("ram0_12.list", u_pipeline.u_icache.data_u.data_line0.ram12.mem);
        $readmemh("ram0_13.list", u_pipeline.u_icache.data_u.data_line0.ram13.mem);
        $readmemh("ram0_14.list", u_pipeline.u_icache.data_u.data_line0.ram14.mem);
        $readmemh("ram0_15.list", u_pipeline.u_icache.data_u.data_line0.ram15.mem);

        $readmemh("ram0_0.list", u_pipeline.u_icache.data_u.data_line1.ram0.mem);
        $readmemh("ram0_1.list", u_pipeline.u_icache.data_u.data_line1.ram1.mem);
        $readmemh("ram0_2.list", u_pipeline.u_icache.data_u.data_line1.ram2.mem);
        $readmemh("ram0_3.list", u_pipeline.u_icache.data_u.data_line1.ram3.mem);
        $readmemh("ram0_4.list", u_pipeline.u_icache.data_u.data_line1.ram4.mem);
        $readmemh("ram0_5.list", u_pipeline.u_icache.data_u.data_line1.ram5.mem);
        $readmemh("ram0_6.list", u_pipeline.u_icache.data_u.data_line1.ram6.mem);
        $readmemh("ram0_7.list", u_pipeline.u_icache.data_u.data_line1.ram7.mem);
        $readmemh("ram0_8.list", u_pipeline.u_icache.data_u.data_line1.ram8.mem);
        $readmemh("ram0_9.list", u_pipeline.u_icache.data_u.data_line1.ram9.mem);
        $readmemh("ram0_10.list", u_pipeline.u_icache.data_u.data_line1.ram10.mem);
        $readmemh("ram0_11.list", u_pipeline.u_icache.data_u.data_line1.ram11.mem);
        $readmemh("ram0_12.list", u_pipeline.u_icache.data_u.data_line1.ram12.mem);
        $readmemh("ram0_13.list", u_pipeline.u_icache.data_u.data_line1.ram13.mem);
        $readmemh("ram0_14.list", u_pipeline.u_icache.data_u.data_line1.ram14.mem);
        $readmemh("ram0_15.list", u_pipeline.u_icache.data_u.data_line1.ram15.mem);

        $readmemh("ram0_0.list", u_pipeline.u_icache.data_u.data_line2.ram0.mem);
        $readmemh("ram0_1.list", u_pipeline.u_icache.data_u.data_line2.ram1.mem);
        $readmemh("ram0_2.list", u_pipeline.u_icache.data_u.data_line2.ram2.mem);
        $readmemh("ram0_3.list", u_pipeline.u_icache.data_u.data_line2.ram3.mem);
        $readmemh("ram0_4.list", u_pipeline.u_icache.data_u.data_line2.ram4.mem);
        $readmemh("ram0_5.list", u_pipeline.u_icache.data_u.data_line2.ram5.mem);
        $readmemh("ram0_6.list", u_pipeline.u_icache.data_u.data_line2.ram6.mem);
        $readmemh("ram0_7.list", u_pipeline.u_icache.data_u.data_line2.ram7.mem);
        $readmemh("ram0_8.list", u_pipeline.u_icache.data_u.data_line2.ram8.mem);
        $readmemh("ram0_9.list", u_pipeline.u_icache.data_u.data_line2.ram9.mem);
        $readmemh("ram0_10.list", u_pipeline.u_icache.data_u.data_line2.ram10.mem);
        $readmemh("ram0_11.list", u_pipeline.u_icache.data_u.data_line2.ram11.mem);
        $readmemh("ram0_12.list", u_pipeline.u_icache.data_u.data_line2.ram12.mem);
        $readmemh("ram0_13.list", u_pipeline.u_icache.data_u.data_line2.ram13.mem);
        $readmemh("ram0_14.list", u_pipeline.u_icache.data_u.data_line2.ram14.mem);
        $readmemh("ram0_15.list", u_pipeline.u_icache.data_u.data_line2.ram15.mem);

        $readmemh("ram0_0.list", u_pipeline.u_icache.data_u.data_line3.ram0.mem);
        $readmemh("ram0_1.list", u_pipeline.u_icache.data_u.data_line3.ram1.mem);
        $readmemh("ram0_2.list", u_pipeline.u_icache.data_u.data_line3.ram2.mem);
        $readmemh("ram0_3.list", u_pipeline.u_icache.data_u.data_line3.ram3.mem);
        $readmemh("ram0_4.list", u_pipeline.u_icache.data_u.data_line3.ram4.mem);
        $readmemh("ram0_5.list", u_pipeline.u_icache.data_u.data_line3.ram5.mem);
        $readmemh("ram0_6.list", u_pipeline.u_icache.data_u.data_line3.ram6.mem);
        $readmemh("ram0_7.list", u_pipeline.u_icache.data_u.data_line3.ram7.mem);
        $readmemh("ram0_8.list", u_pipeline.u_icache.data_u.data_line3.ram8.mem);
        $readmemh("ram0_9.list", u_pipeline.u_icache.data_u.data_line3.ram9.mem);
        $readmemh("ram0_10.list", u_pipeline.u_icache.data_u.data_line3.ram10.mem);
        $readmemh("ram0_11.list", u_pipeline.u_icache.data_u.data_line3.ram11.mem);
        $readmemh("ram0_12.list", u_pipeline.u_icache.data_u.data_line3.ram12.mem);
        $readmemh("ram0_13.list", u_pipeline.u_icache.data_u.data_line3.ram13.mem);
        $readmemh("ram0_14.list", u_pipeline.u_icache.data_u.data_line3.ram14.mem);
        $readmemh("ram0_15.list", u_pipeline.u_icache.data_u.data_line3.ram15.mem);

        $readmemh("tag_ram0.list", u_pipeline.u_icache.tagstore_u.u_tag_ram0.mem);
        $readmemh("tag_ram0.list", u_pipeline.u_icache.tagstore_u.u_tag_ram1.mem);
        $readmemh("tag_ram0.list", u_pipeline.u_icache.tagstore_u.u_tag_ram2.mem);
        $readmemh("tag_ram0.list", u_pipeline.u_icache.tagstore_u.u_tag_ram3.mem);
     end
//        u_pipeline.u_icache.BUS_R = 1'b0;

     initial begin
        $readmemh("dcache5.list", u_pipeline.u_dcache.data_u.data_line0.ram0.mem);
        $readmemh("dcache6.list", u_pipeline.u_dcache.data_u.data_line0.ram1.mem);
        $readmemh("dcache7.list", u_pipeline.u_dcache.data_u.data_line0.ram2.mem);
        $readmemh("dcache8.list", u_pipeline.u_dcache.data_u.data_line0.ram3.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line0.ram4.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line0.ram5.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line0.ram6.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line0.ram7.mem);
        $readmemh("dcache0.list", u_pipeline.u_dcache.data_u.data_line0.ram8.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line0.ram9.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line0.ram10.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line0.ram11.mem);
        $readmemh("dcache1.list", u_pipeline.u_dcache.data_u.data_line0.ram12.mem);
        $readmemh("dcache2.list", u_pipeline.u_dcache.data_u.data_line0.ram13.mem);
        $readmemh("dcache3.list", u_pipeline.u_dcache.data_u.data_line0.ram14.mem);
        $readmemh("dcache4.list", u_pipeline.u_dcache.data_u.data_line0.ram15.mem);

        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram0.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram1.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram2.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram3.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram4.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram5.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram6.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram7.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram8.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram9.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram10.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram11.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram12.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram13.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram14.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line1.ram15.mem);

        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram0.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram1.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram2.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram3.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram4.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram5.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram6.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram7.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram8.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram9.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram10.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram11.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram12.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram13.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram14.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line2.ram15.mem);

        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram0.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram1.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram2.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram3.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram4.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram5.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram6.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram7.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram8.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram9.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram10.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram11.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram12.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram13.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram14.mem);
        $readmemh("dcache.list", u_pipeline.u_dcache.data_u.data_line3.ram15.mem);

        $readmemh("tag_ram1.list", u_pipeline.u_dcache.tagstore_u.u_tag_ram0.mem);
        $readmemh("tag_ram2.list", u_pipeline.u_dcache.tagstore_u.u_tag_ram1.mem);
        $readmemh("tag_ram1.list", u_pipeline.u_dcache.tagstore_u.u_tag_ram2.mem);
        $readmemh("tag_ram1.list", u_pipeline.u_dcache.tagstore_u.u_tag_ram3.mem);
     end
//     initial begin
//        #(clk_cycle)
//        
//     end
     initial #1000 $finish;

     always @(posedge clk) begin
         $strobe ("at time %0d, IR = %h", $time, u_pipeline.u_fetch.CURRENT_IR);
         $strobe ("at time %0d, read_ptr = %h", $time, u_pipeline.u_fetch.read_ptr);
         $strobe ("at time %0d, instr_length_updt = %h", $time, u_pipeline.u_fetch.instr_length_updt);
         $strobe ("at time %0d, Opcode = %h", $time, u_pipeline.u_fetch.opcode);

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
         u_pipeline.u_fetch.u_ifu.itlb.ENTRY[0] = `TLB_ENTRY_0;
         u_pipeline.u_fetch.u_ifu.itlb.ENTRY[1] = `TLB_ENTRY_1;
         u_pipeline.u_fetch.u_ifu.itlb.ENTRY[2] = `TLB_ENTRY_2;
         u_pipeline.u_fetch.u_ifu.itlb.ENTRY[3] = `TLB_ENTRY_3;
         u_pipeline.u_fetch.u_ifu.itlb.ENTRY[4] = `TLB_ENTRY_4;
         u_pipeline.u_fetch.u_ifu.itlb.ENTRY[5] = `TLB_ENTRY_5;
         u_pipeline.u_fetch.u_ifu.itlb.ENTRY[6] = `TLB_ENTRY_6;
         u_pipeline.u_fetch.u_ifu.itlb.ENTRY[7] = `TLB_ENTRY_7;
      end
   initial
      begin
         u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[0] = `TLB_ENTRY_0;
         u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[1] = `TLB_ENTRY_1;
         u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[2] = `TLB_ENTRY_2;
         u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[3] = `TLB_ENTRY_3;
         u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[4] = `TLB_ENTRY_4;
         u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[5] = `TLB_ENTRY_5;
         u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[6] = `TLB_ENTRY_6;
         u_pipeline.u_memory_stage1.u_lsu.dtlb.ENTRY[7] = `TLB_ENTRY_7;
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

endmodule

