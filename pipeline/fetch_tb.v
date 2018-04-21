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
   integer clk_cycle = 16;
   integer half_cycle = 8;

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
        clk = 0;
        clr = 1;
        pre = 1;
    end

    always #(half_cycle)  clk = ~clk;
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

        u_pipeline.u_fetch.IR_2.Q = 32'h0000000;
        u_pipeline.u_fetch.u_FE_buf_0.low.Q = 64'h81773D090CDB1283;
        u_pipeline.u_fetch.u_FE_buf_1.low.Q = 64'h85BC148878235B49;
        u_pipeline.u_fetch.u_FE_buf_2.low.Q = 64'h81773D090CDB1283;
        u_pipeline.u_fetch.u_FE_buf_3.low.Q = 64'h85BC148878235B49;
        u_pipeline.u_fetch.u_FE_buf_0.high.Q = 64'h0F6FEB254B212F96;
        u_pipeline.u_fetch.u_FE_buf_1.high.Q = 64'h7E6D39201F21D322;
        u_pipeline.u_fetch.u_FE_buf_2.high.Q = 64'h0F6FEB254B212F96;
        u_pipeline.u_fetch.u_FE_buf_3.high.Q = 64'h7E6D39201F21D322;

     end 

     initial #20 $finish;

     always @(*) begin
         $strobe ("at time %0d, IR = %h", $time, u_pipeline.u_fetch.IR);
         $strobe ("at time %0d, read_ptr = %h", $time, u_pipeline.u_fetch.read_ptr);
         $strobe ("at time %0d, FE_buf_0 = %h", $time, u_pipeline.u_fetch.FE_buf_0_out);
         $strobe ("at time %0d, FE_buf_1 = %h", $time, u_pipeline.u_fetch.FE_buf_1_out);
         $strobe ("at time %0d, FE_buf_2 = %h", $time, u_pipeline.u_fetch.FE_buf_2_out);
         $strobe ("at time %0d, FE_buf_3 = %h", $time, u_pipeline.u_fetch.FE_buf_3_out);
         $strobe ("at time %0d, instr_length_updt = %h", $time, u_pipeline.u_fetch.instr_length_updt);
    end

   initial begin
       $vcdplusfile("pipeline.dump.vpd");
       $vcdpluson(0, TOP);
   end

endmodule
