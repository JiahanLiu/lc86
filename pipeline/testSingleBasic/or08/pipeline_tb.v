`timescale 1ns/1ps
`define EOF = 32'hFFFF_FFFF
`define NULL 0

`define OF_affected 1'b1
`define DF_affected 1'b0
`define SF_affected 1'b1
`define ZF_affected 1'b1
`define AF_affected 1'b1
`define PF_affected 1'b1
`define CF_affected 1'b1
`define flags_affected ({`OF_affected, `DF_affected, 2'b0, `SF_affected, `ZF_affected, 1'b0, `AF_affected, 1'b0, `PF_affected, 1'b0, `CF_affected})

`define macro_sign_extend 1'b0
`define macro_check_length 2'b00 

`define default_mem_Value 64'h1234_5678_90AB_CDEF
`define default_reg_base_macro 32'h90
`define default_reg_EAX_32 ((`default_reg_base_macro) + ((`default_reg_base_macro) << 8) + ((`default_reg_base_macro ) << 16) + ((`default_reg_base_macro) << 24)) 
`define default_reg_EX_B_32 ((`default_reg_base_macro + `default_modrm_reg_opcode) + ((`default_reg_base_macro + `default_modrm_reg_opcode) << 8) + ((`default_reg_base_macro + `default_modrm_reg_opcode) << 16) + ((`default_reg_base_macro + `default_modrm_reg_opcode) << 24)) 
`define default_reg_base_32 ((`default_reg_base_macro + `default_modrm_rm) + ((`default_reg_base_macro + `default_modrm_rm) << 8) + ((`default_reg_base_macro + `default_modrm_rm) << 16) + ((`default_reg_base_macro + `default_modrm_rm) << 24))
`define default_eip 32'h1 
`define default_cs 32'h22 
`define default_ss ((`default_reg_base_macro + 3'b010) + ((`default_reg_base_macro + 3'b010) << 8))
`define default_flags 32'hFFF
`define default_imm 32'h8765_4321
`define default_big_endian_imm8 8'h21
`define default_big_endian_imm16 32'h2143
`define default_big_endian_imm32 32'h2143_6587
`define default_dis 32'h0B00_0000
`define default_big_endian_dis 32'h0000_000B
`define default_offset 32'h1234_5678
`define default_offset2 16'h2413
`define default_modrm_mod 2'b10
`define default_modrm_reg_opcode 3'b010
`define default_modrm_rm 3'b101

`define if_check_op_a 1'b1
`define if_check_op_b 1'b1
`define if_check_aluk 1'b1
`define check_opA (`default_mem_Value) //check values
`define check_opB (`default_reg_EX_B_32)
`define check_aluk 3'b001

`define if_check_data1 1'b0
`define if_check_data2 1'b0
`define if_check_data3 1'b0
`define if_check_dr1 1'b0
`define if_check_dr2 1'b0
`define if_check_dr3 1'b0
`define if_check_flags 1'b0
`define if_check_datasize 1'b1 
`define check_ld_gpr1 1'b0 //check values
`define check_ld_gpr2 1'b0
`define check_ld_gpr3 1'b0
`define check_data1 32'h0
`define check_data2 32'h0
`define check_data3 32'h0
`define check_dr1 3'b000
`define check_dr2 3'b000
`define check_dr3 3'b000
`define produced_flags 32'h095
`define check_datasize `macro_check_length

`define if_check_mm_data 1'b0
`define which_check_eip 1'b0 //0 for eip + instr length, 1 for other
`define if_check_cs 1'b0
`define check_ld_mm 1'b0 //check values
`define check_ld_eip 1'b1
`define check_ld_cs 1'b0
`define check_ld_seg 1'b0
`define check_mm_data 64'h0
`define taken_eip 32'b0
`define check_cs 16'h0

`define if_check_dcachedata 1'b1
`define if_check_address 1'b1
`define check_ld_dcache 1'b1 //check values
`define check_dcache_data (`check_opA | `check_opB)
`define check_address ((`default_ss << 16) + (`default_reg_base_32 + `default_big_endian_dis))

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

   reg [31:0] tb_opA;
   reg [31:0] tb_opB;
   reg [31:0] tb_data1;
   reg [31:0] tb_data2;
   reg [31:0] tb_dcache;
   reg [63:0] tb_dcache_data; 

   reg [31:0] check_opA;
   reg [31:0] check_opB;
   reg [31:0] check_data1;
   reg [31:0] check_data2;
   reg [63:0] check_dcache_data;
   reg [31:0] correct_opA;
   reg [31:0] correct_opB;
   reg [31:0] correct_data1;
   reg [31:0] correct_data2;
   reg [63:0] correct_dcache_data;

   PIPELINE u_pipeline(clk, clr, pre, IR);

   initial begin
        clk = 0;
        clr = 0;
        pre = 1;
        repeat(2) #clk_cycle //wait 2 clock cycles
        clr = 1;
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
        u_pipeline.u_register_file.gpr.reg0_ll.Q = (`default_reg_base_macro);
        u_pipeline.u_register_file.gpr.reg1_ll.Q = (`default_reg_base_macro + 1);
        u_pipeline.u_register_file.gpr.reg2_ll.Q = (`default_reg_base_macro + 2);
        u_pipeline.u_register_file.gpr.reg3_ll.Q = (`default_reg_base_macro + 3);
        u_pipeline.u_register_file.gpr.reg4_ll.Q = (`default_reg_base_macro + 4);
        u_pipeline.u_register_file.gpr.reg5_ll.Q = (`default_reg_base_macro + 5);
        u_pipeline.u_register_file.gpr.reg6_ll.Q = (`default_reg_base_macro + 6);
        u_pipeline.u_register_file.gpr.reg7_ll.Q = (`default_reg_base_macro + 7);

        u_pipeline.u_register_file.gpr.reg0_lh.Q = (`default_reg_base_macro) << 8;
        u_pipeline.u_register_file.gpr.reg1_lh.Q = (`default_reg_base_macro + 1) << 8;
        u_pipeline.u_register_file.gpr.reg2_lh.Q = (`default_reg_base_macro + 2) << 8;
        u_pipeline.u_register_file.gpr.reg3_lh.Q = (`default_reg_base_macro + 3) << 8;
        u_pipeline.u_register_file.gpr.reg4_lh.Q = (`default_reg_base_macro + 4) << 8;
        u_pipeline.u_register_file.gpr.reg5_lh.Q = (`default_reg_base_macro + 5) << 8;
        u_pipeline.u_register_file.gpr.reg6_lh.Q = (`default_reg_base_macro + 6) << 8;
        u_pipeline.u_register_file.gpr.reg7_lh.Q = (`default_reg_base_macro + 7) << 8;

        u_pipeline.u_register_file.gpr.reg0_hl.Q = (`default_reg_base_macro) << 16;
        u_pipeline.u_register_file.gpr.reg1_hl.Q = (`default_reg_base_macro + 1) << 16;
        u_pipeline.u_register_file.gpr.reg2_hl.Q = (`default_reg_base_macro + 2) << 16;
        u_pipeline.u_register_file.gpr.reg3_hl.Q = (`default_reg_base_macro + 3) << 16;
        u_pipeline.u_register_file.gpr.reg4_hl.Q = (`default_reg_base_macro + 4) << 16;
        u_pipeline.u_register_file.gpr.reg5_hl.Q = (`default_reg_base_macro + 5) << 16;
        u_pipeline.u_register_file.gpr.reg6_hl.Q = (`default_reg_base_macro + 6) << 16;
        u_pipeline.u_register_file.gpr.reg7_hl.Q = (`default_reg_base_macro + 7) << 16;

        u_pipeline.u_register_file.gpr.reg0_hh.Q = (`default_reg_base_macro) << 24;
        u_pipeline.u_register_file.gpr.reg1_hh.Q = (`default_reg_base_macro + 1) << 24;
        u_pipeline.u_register_file.gpr.reg2_hh.Q = (`default_reg_base_macro + 2) << 24;
        u_pipeline.u_register_file.gpr.reg3_hh.Q = (`default_reg_base_macro + 3) << 24;
        u_pipeline.u_register_file.gpr.reg4_hh.Q = (`default_reg_base_macro + 4) << 24;
        u_pipeline.u_register_file.gpr.reg5_hh.Q = (`default_reg_base_macro + 5) << 24;
        u_pipeline.u_register_file.gpr.reg6_hh.Q = (`default_reg_base_macro + 6) << 24;
        u_pipeline.u_register_file.gpr.reg7_hh.Q = (`default_reg_base_macro + 7) << 24;

        u_pipeline.u_register_file.segr.regfilelo.mem_array[0] = (`default_reg_base_macro + 0);
        u_pipeline.u_register_file.segr.regfilelo.mem_array[1] = (`default_reg_base_macro + 1);
        u_pipeline.u_register_file.segr.regfilelo.mem_array[2] = (`default_reg_base_macro + 2);
        u_pipeline.u_register_file.segr.regfilelo.mem_array[3] = (`default_reg_base_macro + 3);
        u_pipeline.u_register_file.segr.regfilelo.mem_array[4] = (`default_reg_base_macro + 4);
        u_pipeline.u_register_file.segr.regfilelo.mem_array[5] = (`default_reg_base_macro + 5);
        u_pipeline.u_register_file.segr.regfilelo.mem_array[6] = (`default_reg_base_macro + 6);
        u_pipeline.u_register_file.segr.regfilelo.mem_array[7] = (`default_reg_base_macro + 7);

        u_pipeline.u_register_file.segr.regfilehi.mem_array[0] = (`default_reg_base_macro + 0);
        u_pipeline.u_register_file.segr.regfilehi.mem_array[1] = (`default_reg_base_macro + 1);
        u_pipeline.u_register_file.segr.regfilehi.mem_array[2] = (`default_reg_base_macro + 2);
        u_pipeline.u_register_file.segr.regfilehi.mem_array[3] = (`default_reg_base_macro + 3);
        u_pipeline.u_register_file.segr.regfilehi.mem_array[4] = (`default_reg_base_macro + 4);
        u_pipeline.u_register_file.segr.regfilehi.mem_array[5] = (`default_reg_base_macro + 5);
        u_pipeline.u_register_file.segr.regfilehi.mem_array[6] = (`default_reg_base_macro + 6);
        u_pipeline.u_register_file.segr.regfilehi.mem_array[7] = (`default_reg_base_macro + 7);

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


        u_pipeline.u_register_file.eip.Q = `default_eip;
        u_pipeline.u_register_file.segr_cs.Q = `default_cs;
        u_pipeline.u_register_file.eflags.Q = `default_flags;
        u_pipeline.u_writeback.u_flags_wb.u_flags_register.Q = `default_flags; //internal flags register
        u_pipeline.u_writeback.u_flags_wb.overwrite_ld_flags = 1'b0;
        u_pipeline.debug_memory = `default_mem_Value;
        
     end 

     initial begin
         // file format
         // prefix1 prefix2 prefix3 opcode modrm sib disp imm offset
         file = $fopen("instruction_trace", "r");
         if (file == `NULL) begin
             $stop;
         end

         @(posedge clr);
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
                modrm = {`default_modrm_mod, `default_modrm_reg_opcode, `default_modrm_rm}; //95
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
                    disp = `default_dis;
                    IR[8*j +: 8] = disp[7:0];
                    disp_size_en=1;
//                    $display ("Time: %0 DISP = %h", $time, disp[7:0]);
                end else begin
                    j=j-4;
                    //disp = {$random};
                    disp_size = 4;
                    disp = `default_dis;
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
                imm[7:0] = `default_imm;
                j=j-1;
                imm_size = 1;
                imm_size_en = 0;
                IR[8*j +: 8] = imm[7:0];
//                $display ("Time: %0d IMM = %h", $time, imm[7:0]);
            end else if(imm_size16) begin
                imm[15:0] = {$random};
                imm[15:0] = `default_imm;
                j=j-2;
                imm_size = 2;
                imm_size_en = 1;
                IR[8*j +: 16] = imm[15:0];
//                $display ("Time: %0d IMM = %h", $time, imm[15:0]);
            end else if(imm_size32) begin
                imm = {$random};
                imm = `default_imm;
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
                offset[7:0] = `default_offset;
                j=j-1;
                offset_size = 1;
                offset_size_en = 0;
                IR[8*j +: 8] = offset[7:0];
//                $display ("Time: %0d OFFSET = %h", $time, offset[7:0]);
            end else if(offset_size16) begin
                offset[15:0] = `default_offset;
                j=j-2;
                offset_size = 2;
                offset_size_en = 1;
                IR[8*j +: 16] = offset[15:0];
//                $display ("Time: %0d OFFSET = %h", $time, offset[15:0]);
            end else if(offset_size32) begin
                offset = `default_offset;
                j=j-4;
                offset_size = 4;
                offset_size_en = 2;
                IR[8*j +: 32] = offset;
//                $display ("Time: %0d OFFSET = %h", $time, offset[31:0]);
            end else if(offset_size48) begin
                offset[31:0] = `default_offset;
                offset[47:32] = `default_offset2;
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


/*************************** ADDRESS GENERATION 1 STAGE INPUTS COMPARE ******************************/
            #(clk_cycle-1);
            #1;    // Allow for setup time
           
            // Valid Signal always 1 for now
            // Check for the valid signal

            if(u_pipeline.AG_PS_EIP !== EIP_UPDATE) begin
                $display("time: %0d AG_PS_EIP error!! %h", $time, u_pipeline.AG_PS_EIP);
//              $stop;
            end

            if(u_pipeline.AG_PS_CS !== u_pipeline.D2_CS_OUT) begin
                $display("time: %0d AG_PS_CS error!! %h", $time, u_pipeline.AG_PS_CS);
//              $stop;
            end

//            if(u_pipeline.AG_PS_OFFSET !== offset_compare) begin
//                $display("time: %0d AG_PS_OFFSET error!! %h", $time, u_pipeline.AG_PS_OFFSET);
////              $stop;
//            end

/*************************** ADDRESS GENERATION 2 STAGE INPUTS COMPARE ******************************/
            #(clk_cycle-1);
            #1;    // Allow for setup time

/*************************** MEM_DEP_CHECK STAGE INPUTS COMPARE ******************************/
            #(clk_cycle-1);
            #1;    // Allow for setup time            

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

            tb_opA = `check_opA; 
            if(2'b00 === `macro_check_length) begin
              check_opA[7:0] = tb_opA[7:0];
              correct_opA[7:0] = u_pipeline.EX_A[7:0];
              if(1'b1 === `macro_sign_extend) begin
                check_opA[31:8] = {24{tb_opA[7]}};
                correct_opA[31:8] = u_pipeline.EX_A[31:8];
              end else begin
                check_opA[31:8] = 0;
                correct_opA[31:8] = 0;
              end
            end else if(2'b01 === `macro_check_length) begin
              check_opA[15:0] = tb_opA[15:0];
              correct_opA[15:0] = u_pipeline.EX_A[15:0];
              if(1'b1 === `macro_sign_extend) begin
                check_opA[31:16] = {16{tb_opA[15]}};
                correct_opA[31:16] = u_pipeline.EX_A[31:16];
              end else begin 
                check_opA[31:16] = 0;
                correct_opA[31:16] = 0;
              end 
            end else if(2'b10 === `macro_check_length) begin
              check_opA = tb_opA; 
              correct_opA = u_pipeline.EX_A;
            end
            if(1'b1 === `if_check_op_a) begin
              if(correct_opA !== check_opA) begin 
                $display("Error: EX_A is: %h, but needs to be: %h", correct_opA, check_opA);
                error <= 1;
              end
            end

            tb_opB = `check_opB; 
            if(2'b00 === `macro_check_length) begin
              check_opB[7:0] = tb_opB[7:0];
              correct_opB[7:0] = u_pipeline.EX_B[7:0];
              if(1'b1 === `macro_sign_extend) begin
                check_opB[31:8] = {24{tb_opB[7]}};
                correct_opB[31:8] = u_pipeline.EX_B[31:8];
              end else begin 
                check_opB[31:8] = 0;
                correct_opB[31:8] = 0;
              end
            end else if(2'b01 === `macro_check_length) begin
              check_opB[15:0] = tb_opB[15:0];
              correct_opB[15:0] = u_pipeline.EX_B[15:0];
              if(1'b1 === `macro_check_length) begin
                check_opB[31:16] = {16{tb_opB[15]}};
                correct_opB[31:16] = u_pipeline.EX_B[31:16];
              end else begin
                check_opB[31:16] = 0;
                correct_opB[31:16] = 0;
              end 
            end else if(2'b10 === `macro_check_length) begin
              check_opB = tb_opB; 
              correct_opB = u_pipeline.EX_B;
            end
            if(1'b1 === `if_check_op_b) begin
              if(correct_opB !== check_opB) begin 
                $display("Error: EX_B is: %h, but needs to be: %h", correct_opB, check_opB);
                error <= 1;
              end
            end


            if(1'b1 === `if_check_aluk) begin
              if(u_pipeline.EX_d2_aluk_ex !== `check_aluk) begin 
                $display("Error: EX_d2_aluk_ex is: %h, but needs to be: %h", u_pipeline.EX_d2_aluk_ex, `check_aluk);
                error <= 1;
              end
            end
            
/*************************** WRITEBACK STAGE INPUTS COMPARE ******************************/
            #(clk_cycle-1);
            #1;    // Allow for setup time

/*************************** WRITEBACK STAGE OUTPUTS COMPARE ******************************/
            tb_data1 = `check_data1; 
            if(2'b00 === `macro_check_length) begin
              check_data1[7:0] = tb_data1[7:0];
              correct_data1[7:0] = u_pipeline.WB_Final_data1[7:0];
              if(1'b1 === `macro_sign_extend) begin
                check_data1[31:8] = {24{tb_data1[7]}};
                correct_data1[31:8] = u_pipeline.WB_Final_data1[31:8];
              end else begin
                check_data1[31:8] = 0;
                correct_data1[31:8] = 0;
              end 
            end else if(2'b01 === `macro_check_length) begin
              check_data1[15:0] = tb_data1[15:0];
              correct_data1[15:0] = u_pipeline.WB_Final_data1[15:0];
              if(1'b1 === `macro_sign_extend) begin
                check_data1[31:16] = {16{tb_data1[15]}};
                correct_data1[31:16] = u_pipeline.WB_Final_data1[31:16];
              end else begin 
                check_data1[31:16] = 0;
                correct_data1[31:16] = 0;
              end
            end else if(2'b10 === `macro_check_length) begin
              check_data1 = tb_data1; 
              correct_data1 = u_pipeline.WB_Final_data1;
            end
            if(1'b1 === tb_data1) begin
              if(correct_data1 !== check_data1) begin 
                $display("Error: WB_Final_data1 is: %h, but needs to be: %h", correct_data1, check_data1);
                error <= 1;
              end
            end

            tb_data2 = `check_data2; 
            if(2'b00 === `macro_check_length) begin
              check_data2[7:0] = tb_data2[7:0];
              correct_data2[7:0] = u_pipeline.WB_Final_data2[7:0];
              if(1'b1 === `macro_sign_extend) begin
                check_data2[31:8] = {24{tb_data2[7]}};
                correct_data2[31:8] = u_pipeline.WB_Final_data2[31:8];
              end begin 
                check_data2[31:8] = 0;
                correct_data2[31:8] = 0;
              end 
            end else if(2'b01 === `macro_check_length) begin
              check_data2[15:0] = tb_data2[15:0];
              correct_data2[15:0] = u_pipeline.WB_Final_data2[15:0];
              if(1'b1 === `macro_sign_extend) begin
                check_data2[31:16] = {16{tb_data2[15]}};;
                correct_data2[31:16] = u_pipeline.WB_Final_data2[31:16];
              end else begin 
                check_data2[31:8] = 0;
                correct_data2[31:8] = 0;
              end
            end else if(2'b10 === `macro_check_length) begin
              check_data2 = tb_data2; 
              correct_data2 = u_pipeline.WB_Final_data2;
            end else begin 

            end
            if(1'b1 === `if_check_data2) begin
              if(correct_data2 !== check_data2) begin 
                $display("Error: WB_Final_data2 is: %h, but needs to be: %h", correct_data2, check_data2);
                error <= 1;
              end
            end 

            if(1'b1 === `if_check_data3) begin
              if(u_pipeline.WB_Final_data3 !== `check_data3) begin 
                $display("Error: WB_Final_data3 is: %h, but needs to be: %h", u_pipeline.WB_Final_data3, `check_data3);
                error <= 1;
              end
            end 

            if(1'b1 === `if_check_dr1) begin
              if(u_pipeline.WB_Final_DR1 !== `check_dr1) begin 
                $display("Error: WB_Final_DR1 is: %h, but needs to be: %h", u_pipeline.WB_Final_DR1, `check_dr1);
                error <= 1;
              end
            end

            if(1'b1 === `if_check_dr2) begin
              if(u_pipeline.WB_Final_DR2 !== `check_dr2) begin 
                $display("Error: WB_Final_DR2 is: %h, but needs to be: %h", u_pipeline.WB_Final_DR2, `check_dr2);
                error <= 1;
              end
            end

            if(1'b1 === `if_check_dr3) begin
              if(u_pipeline.WB_Final_DR3 !== `check_dr3) begin 
                $display("Error: WB_Final_DR3 is: %h, but needs to be: %h", u_pipeline.WB_Final_DR3, `check_dr3);
                error <= 1;
              end
            end
            
            if(u_pipeline.WB_Final_ld_gpr1 !== `check_ld_gpr1) begin 
              $display("Error: WB_Final_ld_gpr1 is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_gpr1, `check_ld_gpr1);
              error <= 1;
            end

            if(u_pipeline.WB_Final_ld_gpr2 !== `check_ld_gpr2) begin 
              $display("Error: WB_Final_ld_gpr2 is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_gpr2, `check_ld_gpr2);
              error <= 1;
            end

            if(u_pipeline.WB_Final_ld_gpr3 !== `check_ld_gpr3) begin 
              $display("Error: WB_Final_ld_gpr3 is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_gpr3, `check_ld_gpr3);
              error <= 1;
            end

            if(1'b1 === `check_ld_gpr3) begin 
              $display("Error: WB_Final_DR3_datasize is: %h, but needs to be: %h", u_pipeline.WB_Final_DR3_datasize, 2'b10);
              error <= 1;
            end

            if(1'b1 === `if_check_flags) begin
              if(u_pipeline.WB_Final_Flags !== ((`default_flags & (~`flags_affected)) + `produced_flags)) begin 
                $display("Error: WB_Final_Flags is: %h, but needs to be: %h", u_pipeline.WB_Final_Flags, (`default_flags & (~`flags_affected)) + `produced_flags);
                error <= 1;
              end
            end

            if(1'b1 === `if_check_datasize) begin
              if(u_pipeline.WB_Final_datasize !== `check_datasize) begin 
                $display("Error: WB_Final_datasize is: %h, but needs to be: %h", u_pipeline.WB_Final_datasize, `check_datasize);
                error <= 1;
              end
            end

            if(1'b1 === `if_check_mm_data) begin 
              if(u_pipeline.WB_Final_MM_Data !== `check_mm_data) begin 
                $display("Error: WB_Final_MM_Data is: %h, but needs to be: %h", u_pipeline.WB_Final_MM_Data, `check_mm_data);
                error <= 1; 
              end
            end

            if(1'b0 === `which_check_eip) begin 
              if(u_pipeline.WB_Final_EIP !== `default_eip + instr_length) begin 
                $display("Error: WB_Final_EIP is: %h, but needs to be: %h", u_pipeline.WB_Final_EIP, `default_eip + instr_length);
                error <= 1; 
              end
            end else begin
              if(u_pipeline.WB_Final_EIP !== `taken_eip) begin 
                $display("Error: WB_Final_EIP is: %h, but needs to be: %h", u_pipeline.WB_Final_EIP, `taken_eip);
                error <= 1; 
              end
            end

            if(1'b1 === `if_check_cs) begin 
              if(u_pipeline.WB_Final_CS !== `check_cs) begin 
                $display("Error: WB_Final_EIP is: %h, but needs to be: %h", u_pipeline.WB_Final_CS, `check_cs);
                error <= 1; 
              end
            end

            if(u_pipeline.WB_Final_ld_mm !== `check_ld_mm) begin 
              $display("Error: WB_Final_ld_mm is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_mm, `check_ld_mm);
              error <= 1;
            end

           if(u_pipeline.WB_Final_ld_eip !== `check_ld_eip) begin 
              $display("Error: WB_Final_ld_eip is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_eip, `check_ld_eip);
              error <= 1;
            end

            if(u_pipeline.WB_Final_ld_cs !== `check_ld_cs) begin 
              $display("Error: WB_Final_ld_cs is: %h, but needs to be: %h", u_pipeline.WB_Final_ld_cs, `check_ld_cs);
              error <= 1;
            end

            tb_dcache_data = `check_dcache_data; 
            if(2'b00 === `macro_check_length) begin
              check_dcache_data[7:0] = tb_dcache_data[7:0];
              correct_dcache_data[7:0] = u_pipeline.WB_Final_Dcache_Data[7:0];
              if(1'b1 === `macro_sign_extend) begin
                check_dcache_data[63:8] = {56{tb_dcache_data[7]}};
                correct_dcache_data[63:8] = u_pipeline.WB_Final_Dcache_Data[63:8];
              end else begin
                check_dcache_data[63:8] = 0;
                correct_dcache_data[63:8] = 0;
              end
            end else if(2'b01 === `macro_check_length) begin
              check_dcache_data[15:0] = tb_dcache_data[15:0];
              correct_dcache_data[15:0] = u_pipeline.WB_Final_Dcache_Data[15:0];
              if(1'b1 === `macro_sign_extend) begin
                check_dcache_data[63:16] = {48{tb_dcache_data[15]}};
                correct_dcache_data[63:16] = u_pipeline.WB_Final_Dcache_Data[63:16];
              end else begin
                check_dcache_data[63:16] = 0;
                correct_dcache_data[63:16] = 0;
              end 
            end else if(2'b10 === `macro_check_length) begin
              check_dcache_data[31:0] = tb_dcache_data[31:0];
              correct_dcache_data[31:0] = u_pipeline.WB_Final_Dcache_Data[31:0];
              if(1'b1 === `macro_sign_extend) begin
                check_dcache_data[63:32] = {32{tb_dcache_data[31]}};
                correct_dcache_data[63:32] = u_pipeline.WB_Final_Dcache_Data[63:32];
              end else begin
                check_dcache_data[63:32] = 0;
                correct_dcache_data[63:32] = 0;
              end 
            end else if(2'b11 === `macro_check_length) begin
              check_dcache_data = tb_dcache_data;
              correct_dcache_data = u_pipeline.WB_Final_Dcache_Data;
            end
            if(1'b1 === `if_check_dcachedata) begin
              if(correct_dcache_data !== check_dcache_data) begin 
                $display("Error: WB_Final_Dcache_Data is: %h, but needs to be: %h", correct_dcache_data, check_dcache_data);
                error <= 1;
              end
            end

            if(1'b1 === `if_check_address) begin
              if(u_pipeline.WB_Final_Dcache_Address !== `check_address) begin 
                $display("Error: WB_Final_Dcache_Address is: %h, but needs to be: %h", u_pipeline.WB_Final_Dcache_Address, `check_address);
                error <= 1;
                $display("Debug: default_ss << 16 is: %h", `default_ss << 16);
                $display("Debug: default_reg_whole_value << is : %h", `default_reg_base_32);
                $display("Debug: default_dis is: %h", `default_big_endian_dis);
              end
            end

            if(u_pipeline.WB_Final_Dcache_Write !== `check_ld_dcache) begin 
              $display("Error: WB_Final_Dcache_Write is: %h, but needs to be: %h", u_pipeline.WB_Final_Dcache_Write, `check_ld_dcache);
              error <= 1;
            end

        #5
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
        $readmemb("../../control_store/rom0_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom1.mem);
        $readmemb("../../control_store/rom0_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom1.mem);
        $readmemb("../../control_store/rom1_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom2.mem);
        $readmemb("../../control_store/rom1_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom2.mem);
        $readmemb("../../control_store/rom2_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom3.mem);
        $readmemb("../../control_store/rom2_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom3.mem);
        $readmemb("../../control_store/rom3_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom4.mem);
        $readmemb("../../control_store/rom3_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom4.mem);
        $readmemb("../../control_store/rom4_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom5.mem);
        $readmemb("../../control_store/rom4_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom5.mem);
        $readmemb("../../control_store/rom5_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom6.mem);
        $readmemb("../../control_store/rom5_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom6.mem);
        $readmemb("../../control_store/rom6_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom7.mem);
        $readmemb("../../control_store/rom6_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom7.mem);
        $readmemb("../../control_store/rom7_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom8.mem);
        $readmemb("../../control_store/rom7_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom8.mem);
        $readmemb("../../control_store/rom8_0.list", u_pipeline.u_decode_stage2.u_ucontrol_store1.u_rom9.mem);
        $readmemb("../../control_store/rom8_1.list", u_pipeline.u_decode_stage2.u_ucontrol_store2.u_rom9.mem);
    end
   
endmodule
