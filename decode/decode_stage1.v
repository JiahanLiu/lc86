module decode_stage1 (
    input clk, set, reset, 
    input [127:0] IR, 
    input [31:0] EIP,
    input [15:0] CS,

    output [31:0] EIP_OUT, 
    output [15:0] CS_OUT,
    output [127:0] IR_OUT,
    output [3:0] instr_length_updt,
    output [15:0] opcode, 
    output [1:0] prefix_size,
    output prefix_present, segment_override, operand_override, repeat_prefix, 
    output modrm_present, imm_present,
    output [1:0] imm_size,
    output sib_present, disp_present, disp_size,
    output [3:0] imm_sel,
    output [2:0] disp_sel,
    output offset_present,
    output opcode_size, 
    output [1:0] offset_size,
    output [2:0] segID,
    output [7:0] modrm, sib,
    output [2:0] modrm_sel
//    output [31:0] sum,
//    input cin,
//    input [31:0] a, b,
//    output cout
);

// Prefix Checker
wire isPrefix1, isOpcode1, operand_override1, segment_override1, repeat_prefix1;
wire isPrefix2, isOpcode2, operand_override2, segment_override2, repeat_prefix2;
wire isPrefix3, isOpcode3, operand_override3, segment_override3, repeat_prefix3;
wire [2:0] segID1, segID2, segID3;
wire isPrefix4, isOpcode4;
wire isPrefix5, isOpcode5;

// Prefix Decoder
wire [1:0] segID_sel;

// Opcode length decoder
wire [2:0] opcode_sel;
wire [7:0] out1m, out2m;

assign CS_OUT = CS;
assign EIP_OUT = EIP;
assign IR_OUT = IR;

prefix_checker u_prefix_checker1 (.instr_byte(IR[127:120]), .isPrefix(isPrefix1), .isOpcode(isOpcode1),
    .operand_override(operand_override1), .segment_override(segment_override1),
    .repeat_prefix(repeat_prefix1), .segID(segID1)
);

prefix_checker u_prefix_checker2 (.instr_byte(IR[119:112]), .isPrefix(isPrefix2), .isOpcode(isOpcode2),
    .operand_override(operand_override2), .segment_override(segment_override2),
    .repeat_prefix(repeat_prefix2), .segID(segID2)
);

prefix_checker u_prefix_checker3 (.instr_byte(IR[111:104]), .isPrefix(isPrefix3), .isOpcode(isOpcode3),
    .operand_override(operand_override3), .segment_override(segment_override3),
    .repeat_prefix(repeat_prefix3), .segID(segID3)
);

prefix_checker u_prefix_checker4 (.instr_byte(IR[103:96]), .isPrefix(isPrefix4), .isOpcode(isOpcode4),
    .operand_override(), .segment_override(),
    .repeat_prefix(), .segID()
);

prefix_checker u_prefix_checker5 (.instr_byte(IR[95:88]), .isPrefix(isPrefix5), .isOpcode(isOpcode5),
    .operand_override(), .segment_override(),
    .repeat_prefix(), .segID()
);

or3$ or1 (operand_override, operand_override1, operand_override2, operand_override3);
or3$ or2 (repeat_prefix, repeat_prefix1, repeat_prefix2, repeat_prefix3);

prefix_decoder u_prefix_decoder (.isPrefix1(isPrefix1), .isPrefix2(isPrefix2), .isPrefix3(isPrefix3),
    .isSeg_ovrr1(segment_override1), .isSeg_ovrr2(segment_override2), .isSeg_ovrr3(segment_override3),
    .prefix_present(prefix_present), .prefix_length(prefix_size), .segID_sel(segID_sel)
);

mux4$ mux_segID[2:0] (segID, segID1, segID2, segID3, , segID_sel[0], segID_sel[1]);

opcode_length_decoder u_opcode_length_decoder (.isOpcode1(isOpcode1), .isOpcode2(isOpcode2),
    .isOpcode3(isOpcode3), .isOpcode4(isOpcode4), .isOpcode5(isOpcode5), .byte1(IR[127:120]),
    .byte2(IR[119:112]), .byte3(IR[111:104]), .byte4(IR[103:96]), .byte5(IR[95:88]),
    .opcode_sel(opcode_sel), .opcode_size(opcode_size)
);

mux4_8$ mux1_op (out1m, IR[127:120], IR[119:112], IR[111:104], IR[103:96], opcode_sel[0], opcode_sel[1]);
mux4_8$ mux2_op (out2m, IR[119:112], IR[111:104], IR[103:96], IR[95:88], opcode_sel[0], opcode_sel[1]);

mux2_8$ mux3_op (opcode[7:0], out1m, out2m, opcode_sel[2]);
mux2_8$ mux4_op (opcode[15:8], 8'b0, out1m, opcode_sel[2]);

modrm_detector u_modrm_detector (.opcode(opcode), .modrm_present(modrm_present) );

immediate_detector u_immediate_detector (.opcode(opcode), .operand_override(operand_override),
    .imm_present(imm_present), .imm_size(imm_size)
);

modrm_pointer u_modrm_pointer (.opcode_size(opcode_size), .prefix_present(prefix_present),
    .prefix_size(prefix_size), .modrm_sel(modrm_sel)
);

modrm_selector u_modrm_selector (.instr_buf(IR[119:80]), .modrm_sel(modrm_sel), .modrm(modrm) );

sib_disp_detector u_sib_disp_detector (.modrm(modrm), .disp_present(disp_present), .disp_size(disp_size),
    .sib_present(sib_present)
);

//carry_lookahead u_cl (sum, , , cout, a, b, cin);
//adder32 u_adder32 (sum, carry, a, b);

sib_selector u_sib_selector (.instr_buf(IR[111:72]), .sib_sel(modrm_sel), .sib(sib) );

offset_detector u_offset_detector (.opcode(opcode), .operand_override(operand_override),
    .opcode_size(opcode_size), .offset_present(offset_present), .offset_size(offset_size)
);

instruction_length_decoder u_instruction_length_decoder (.prefix_present(prefix_present),
    .prefix_size(prefix_size), .opcode_size(opcode_size), .modrm_present(modrm_present),
    .sib_present(sib_present), .offset_present(offset_present), .offset_size(offset_size), 
    .disp_present(disp_present), .disp_size(disp_size), .imm_present(imm_present),
    .imm_size(imm_size), .disp_sel(disp_sel), .imm_sel(imm_sel), .read_ptr_update(instr_length_updt)
);

endmodule
