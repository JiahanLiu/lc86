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
   integer clk_cycle = 10;
   integer half_cycle = 5;

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
        pre = 0;
        repeat(2) #clk_cycle
        pre = 1;
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
        while (char != 32'hFFFFFFFF) begin
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

           $display ("Time: %0d, OPCODE: %h", $time, opcode);
           
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
//                modrm = {$random};
                modrm = 8'b10010101;
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
//                    disp[7:0] = {$random};
                    disp[7:0] = 8'h0A;
                    IR[8*j +: 8] = disp[7:0];
                    disp_size_en=1;
//                    $display ("Time: %0 DISP = %h", $time, disp[7:0]);
                end else begin
                    j=j-4;
//                    disp = {$random};
                    disp = 32'h0A;
                    disp_size = 4;
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
//                imm[7:0] = {$random};
                j=j-1;
                imm_size = 1;
                imm_size_en = 0;
                IR[8*j +: 8] = imm[7:0];
//                $display ("Time: %0d IMM = %h", $time, imm[7:0]);
            end else if(imm_size16) begin
//                imm[15:0] = {$random};
                j=j-2;
                imm_size = 2;
                imm_size_en = 1;
                IR[8*j +: 16] = imm[15:0];
//                $display ("Time: %0d IMM = %h", $time, imm[15:0]);
            end else if(imm_size32) begin
//                imm = {$random};
                j=j-4;
                imm_size = 4;
                imm_size_en = 2;
                IR[8*j +: 32] = imm;
//                $display ("Time: %0d IMM = %h", $time, imm);
            end

            if(imm_present) 
                imm = 32'd1234;

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
                $display ("Time: %0d OFFSET = %h", $time, offset[7:0]);
          end else if(offset_size16) begin
              offset[15:0] = {$random};
              j=j-2;
              offset_size = 2;
              offset_size_en = 1;
              IR[8*j +: 16] = offset[15:0];
                $display ("Time: %0d OFFSET = %h", $time, offset[15:0]);
          end else if(offset_size32) begin
              offset = {$random};
              j=j-4;
              offset_size = 4;
              offset_size_en = 2;
              IR[8*j +: 32] = offset;
                $display ("Time: %0d OFFSET = %h", $time, offset[31:0]);
          end else if(offset_size48) begin
              offset[31:0] = {$random};
              offset[47:32] = {$random};
              j=j-6;
              offset_size = 6;
              offset_size_en = 3;
              IR[8*j +: 48] = offset;
                $display ("Time: %0d OFFSET = %h", $time, offset[47:0]);
            end

            instr_length = prefix_size + opcode_size + modrm_present + sib_present + disp_size + imm_size + offset_size;
//            $display("%h, %h, %h, %h, %h, %h, %h", prefix_size, opcode_size,modrm_present,sib_present,disp_size,imm_size,offset_size);
            @(posedge clk);
           #clk_cycle; 
           #1; // allow for "setup time"

/*************************** DECODE2 STAGE INPUTS COMPARE ******************************/
           if(u_pipeline.IR_OUT !== IR) begin
               $display("time: %0d IR_OUT error: %h!!", $time, u_pipeline.IR_OUT);
//               $stop;
           end else 
               $display("time: %0d IR_OUT: %h", $time, u_pipeline.IR_OUT);

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

/*************************** ADDRESS GENERATION STAGE INPUT VALUES GENERATION ******************************/
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

            if(imm_present) begin
                if(imm_size8) begin
                    imm_compare[7:0] = imm[7:0];
                    imm_compare[31:8] = 0;
                end else if(imm_size16) begin
                    imm_compare[15:8] = imm[7:0];
                    imm_compare[7:0] = imm[15:8];
                    imm_compare[31:16] = 0;
                end else if(imm_size32) begin
                    imm_compare[31:24] = imm[7:0];
                    imm_compare[23:16] = imm[15:8];
                    imm_compare[15:8] = imm[23:16];
                    imm_compare[7:0] = imm[31:24];
                end
            end

            if(disp_present) begin
                if(disp_size == 4) begin
                    disp_compare[31:24] = disp[7:0];
                    disp_compare[23:16] = disp[15:8];
                    disp_compare[15:8] = disp[23:16];
                    disp_compare[7:0] = disp[31:24];
                end else begin
                    disp_compare[7:0] = disp[7:0];
                    disp_compare[31:8] = {24{disp[7]}};
                end
            end

            SR2 = modrm[5:3];
            SR1 = (modrm[2:0]==3'b100)?sib[5:3]:modrm[2:0];

            case(opcode)
                // ADD_AL
                16'h04: begin
                    SR1 = `AL;
                    SR1_size = 0;
                end

                // ADD_AX
                16'h05: begin
                    SR1 = `EAX;
                    if(operand_override)
                        SR1_size = 1;
                    else
                        SR1_size = 2;
                end

                // ADD r/m32, imm32
                16'h81: begin
                    SR1 = (modrm[2:0]==3'b100)?sib[5:3]:modrm[2:0];
                    SR1_size = operand_override ? 2:1;
                end

                // ADD r/m16, imm8
                16'h83: begin
                    SR1 = (modrm[2:0]==3'b100)?sib[5:3]:modrm[2:0];
                    SR1_size = operand_override ? 2:1;
                end

                // ADD r/m16, r16
                16'h01: begin
                    SR1 = (modrm[2:0]==3'b100)?sib[5:3]:modrm[2:0];
                    SR1_size = 1;
                    SR2 = (modrm[2:0]==3'b100)?sib[2:0]:modrm[5:3];
                    SR2_size = 1;
                end

                // ADD r/m8, r8
                16'h00: begin
                    SR1 = (modrm[2:0]==3'b100)?sib[5:3]:modrm[2:0];
                    SR1_size = 0;
                    SR2 = (modrm[2:0]==3'b100)?sib[2:0]:modrm[5:3];
                    SR2_size = 0;
                end

                // ADD r16, r/m16
                16'h03: begin
                    SR1 = (modrm[2:0]==3'b100)?sib[5:3]:modrm[2:0];
                    SR2 = modrm[5:3];

                end


            endcase

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

            if(offset_present) begin
                if(u_pipeline.AG_PS_OFFSET !== offset_compare) begin
                    $display("time: %0d AG_PS_OFFSET error!! %h", $time, u_pipeline.AG_PS_OFFSET);
//                  $stop;
                end
            end

            if(imm_present) begin
                if(u_pipeline.AG_PS_IMM32 !== imm_compare) begin
                    $display("time: %0d AG_PS_IMM32 error!! %h", $time, u_pipeline.AG_PS_IMM32);
//                  $stop;
                end
            end

            if(disp_present) begin
                if(u_pipeline.AG_PS_DISP32 !== disp_compare) begin
                    $display("time: %0d AG_PS_DISP32 error!! %h", $time, u_pipeline.AG_PS_DISP32);
//                  $stop;
                end
            end

//            if(u_pipeline.AG_PS_SR1 !== SR1) begin
//                $display("time: %0d AG_PS_SR1 error!! %h %h", $time, u_pipeline.AG_PS_SR1, SR1);
////                $stop;
//            end
//
//            if(u_pipeline.AG_PS_SR2 !== SR2) begin
//                $display("time: %0d AG_PS_SR2 error!! %h %h", $time, u_pipeline.AG_PS_SR2, SR2);
////                $stop;
//            end

            if(u_pipeline.SR1_DATA !== reg_array[u_pipeline.AG_PS_SR1] ) begin
                $display("time: %0d REG_SR1_DATA error!! %h ", $time, u_pipeline.SR1_DATA);
//                $stop;
            end

            if(u_pipeline.SR2_DATA !== reg_array[u_pipeline.AG_PS_SR2]) begin
                $display("time: %0d REG_SR2_DATA error!! %h", $time, u_pipeline.SR2_DATA);
            end

            if(u_pipeline.SR3_DATA !== reg_array[u_pipeline.AG_PS_SR3]) begin
                $display("time: %0d REG_SR3_DATA error!! %h", $time, u_pipeline.SR3_DATA);
            end

            if(u_pipeline.SIB_I_DATA !== reg_array[u_pipeline.AG_PS_SIB_I]) begin
                $display("time: %0d REG_SIB_I_DATA error!! %h", $time, u_pipeline.SIB_I_DATA);
            end

//            if(u_pipeline.SEG1_DATA !== reg_array_seg[u_pipeline.AG_PS_SEG1]) begin
//                $display("time: %0d REG_SEG1_DATA error!! %h", $time, u_pipeline.SEG1_DATA);
//            end
//
//            if(u_pipeline.SEG2_DATA !== reg_array_seg[u_pipeline.AG_PS_SEG2]) begin
//                $display("time: %0d REG_SEG2_DATA error!! %h", $time, u_pipeline.SEG2_DATA);
//            end
//
//            if(u_pipeline.MM1_DATA !== reg_array_seg[u_pipeline.AG_PS_SR1]) begin
//                $display("time: %0d REG_MM1_DATA error!! %h", $time, u_pipeline.MM1_DATA);
//            end
//
//            if(u_pipeline.MM2_DATA !== reg_array_seg[u_pipeline.AG_PS_SR2]) begin
//                $display("time: %0d REG_MM2_DATA error!! %h", $time, u_pipeline.MM2_DATA);
//            end




/*************************** MEMORY STAGE INPUTS COMPARE ******************************/
            #(clk_cycle-1);
            #1;    // Allow for setup time

            // Opcode == 04
//            if(opcode == 16'h4 || opcode==16'h5 || opcode==16'h81 || opcode==16'h83 || opcode==16'h01) begin
//                result = ME_A_OUT + ME_B_OUT;
//            end

/*************************** EXECUTE STAGE INPUTS COMPARE ******************************/
            #(clk_cycle-1);
            #1;    // Allow for setup time

/*************************** WRITEBACK STAGE INPUTS COMPARE ******************************/
            #(clk_cycle-1);
            #1;    // Allow for setup time
        $strobe ("at time %0d, WB_current_flags = %h", $time, u_pipeline.u_writeback.current_flags);
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


/*********************************************************/
           // Ignore all stall cycles; do not compare them against trace cycles.
           //while (stall_signal == 1'b1) begin
           //     #clk_cycle
           //end

        end

        $display("INSTRUCTIONS COMPLETED");
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
        $strobe ("at time %0d, WB_current_flags = %h", $time, u_pipeline.u_writeback.current_flags);
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
