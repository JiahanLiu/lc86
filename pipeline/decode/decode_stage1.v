module decode_stage1 (
    input clk, set, reset, 
    input [127:0] IR, 

    input INT_EXIST,

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
    output [2:0] modrm_sel,
    output [7:0] control_store_address
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
wire out4a, out5a, out6a, out7a, out8a, out9a;
wire [1:0] imm_size_in;

// Prefix Decoder
wire [1:0] segID_sel;

// Opcode length decoder
wire [2:0] opcode_sel;
wire [7:0] out1m, out2m;
wire eq_FF, eq_0F70, eq_A6;
wire AGB1, BGA1, AGB2, BGA2, AGB3, BGA3;
wire [7:0] FF_out;

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

and4$ and4 (out4a, isPrefix1, isPrefix2, isPrefix3, operand_override3);
and3$ and5 (out5a, isPrefix1, isPrefix2, operand_override2);
and2$ and6 (out6a, isPrefix1, operand_override1);

and4$ and7 (out7a, isPrefix1, isPrefix2, isPrefix3, repeat_prefix3);
and3$ and8 (out8a, isPrefix1, isPrefix2, repeat_prefix2);
and2$ and9 (out9a, isPrefix1, repeat_prefix1);

or3$ or1 (operand_override, out4a, out5a, out6a);
or3$ or2 (repeat_prefix, out7a, out8a, out9a);

prefix_decoder u_prefix_decoder (.isPrefix1(isPrefix1), .isPrefix2(isPrefix2), .isPrefix3(isPrefix3),
    .isSeg_ovrr1(segment_override1), .isSeg_ovrr2(segment_override2), .isSeg_ovrr3(segment_override3),
    .prefix_present(prefix_present), .prefix_length(prefix_size), .segID_sel(segID_sel),
    .segment_override(segment_override)
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
    .imm_present(imm_present), .imm_size(imm_size_in)
);

modrm_pointer u_modrm_pointer (.opcode_size(opcode_size), .prefix_present(prefix_present),
    .prefix_size(prefix_size), .modrm_sel(modrm_sel)
);

modrm_selector u_modrm_selector (.instr_buf(IR[119:80]), .modrm_sel(modrm_sel), .modrm(modrm) );

sib_disp_detector u_sib_disp_detector (.modrm(modrm), .modrm_present(modrm_present), .disp_present(disp_present), .disp_size(disp_size),
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
    .imm_size(imm_size_in), .disp_sel(disp_sel), .imm_sel(imm_sel), .read_ptr_update(instr_length_updt)
);

assign imm_size = imm_size_in;

mag_comp8$ comp1 (opcode[7:0], 8'hFF, AGB1, BGA1);
nor2$ nand1 (eq_FF, AGB1, BGA1);

mag_comp8$ comp2 (opcode[7:0], 8'h70, AGB2, BGA2);
nor2$ nand2 (eq_0F70, AGB2, BGA2);

mag_comp8$ comp3 ({opcode[7:1], 1'b0}, 8'hA6, AGB3, BGA3);
nor2$ nand3 (eq_A6, AGB3, BGA3);

and2$ and_rep (and_rep_out, repeat_prefix, eq_A6);
or2$ or_opcode3 (or_opcode3_out, and_rep_out, opcode[3]);

wire [7:0] default_control_store_address;

mux4_8$ mux1 (FF_out, 8'h18, 8'h19, 8'h1A, 8'h1B, modrm[4], modrm[5]);
mux4_8$ mux2 (default_control_store_address, {opcode[7:4], or_opcode3_out, opcode[2:0]}, 8'h03, FF_out, , eq_0F70, eq_FF);

mux2_8$ mux3 (control_store_address, default_control_store_address, `INT_CONTROL_STORE_ADDR, INT_EXIST);

endmodule
