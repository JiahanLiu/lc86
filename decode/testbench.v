`timescale 1ns/1ps

module TOP;
       
    reg clk, reset, set;
    reg [127:0] IR ;
    reg [31:0] EIP;
    reg [15:0] CS;

    wire [31:0] EIP_OUT;
    wire [15:0] CS_OUT;
    wire [127:0] IR_OUT;
    wire [3:0] instr_length_updt;
    wire [15:0] opcode;
    wire [1:0] prefix_size;
    wire prefix_present, segment_override, operand_override, repeat_prefix;
    wire modrm_present, imm_present;
    wire [1:0] imm_size;
    wire sib_present, disp_present, disp_size;
    wire [3:0] imm_sel;
    wire [2:0] disp_sel;
    wire offset_present;
    wire opcode_size ;
    wire [1:0] offset_size;
    wire [2:0] segID;
    wire [7:0] modrm, sib;
    wire [2:0] modrm_sel;

    decode_stage1 u_decode1 (clk, set, reset, IR, EIP, CS, EIP_OUT, CS_OUT, IR_OUT,
    instr_length_updt, opcode, prefix_size, prefix_present, segment_override, operand_override, 
repeat_prefix, modrm_present, imm_present, imm_size, sib_present, disp_present, disp_size, 
imm_sel, disp_sel, offset_present, opcode_size, offset_size, segID, modrm, sib, modrm_sel);


    initial 
    begin
        clk=0;
        reset=0;
        set=1;

        #5
        reset=1;
        set=1;
        IR = 128'h83c00a00000000000000000000000000;

    end

    initial begin
        $vcdplusfile ("decode1.dump.vpd");
        $vcdpluson(0, TOP);
    end

    initial #30 $finish;

    always @(posedge clk) begin
        $strobe ("at time %0d, opcode = %h", $time, opcode);
        $strobe ("at time %0d, modrm_sel = %h", $time, modrm_sel);
        $strobe ("at time %0d, instr_length_updt = %h", $time, instr_length_updt);
        $strobe ("at time %0d, prefix_size = %h", $time, prefix_size);
        $strobe ("at time %0d, prefix_present = %h", $time, prefix_present);
        $strobe ("at time %0d, segment_override = %h", $time, segment_override);
        $strobe ("at time %0d, operand_override = %h", $time, operand_override);
        $strobe ("at time %0d, repeat_prefix = %h", $time, repeat_prefix);
        $strobe ("at time %0d, modrm_present = %h", $time, modrm_present);
        $strobe ("at time %0d, imm_present = %h", $time, imm_present);
        $strobe ("at time %0d, imm_size = %h", $time, imm_size);
        $strobe ("at time %0d, sib_present = %h", $time, sib_present);
        $strobe ("at time %0d, disp_present = %h", $time, disp_present);
        $strobe ("at time %0d, disp_size = %h", $time, disp_size);
        $strobe ("at time %0d, imm_sel = %h", $time, imm_sel);
        $strobe ("at time %0d, disp_sel = %h", $time, disp_sel);
        $strobe ("at time %0d, offset_present = %h", $time, offset_present);
        $strobe ("at time %0d, offset_size = %h", $time, offset_size);
        $strobe ("at time %0d, segID = %h", $time, segID);
        $strobe ("at time %0d, modrm = %h", $time, modrm);
        $strobe ("at time %0d, sib = %h", $time, sib);
        $strobe ("at time %0d, modrm_sel = %h", $time, modrm_sel);
    end

    always 
        #5 clk = !clk;

endmodule
