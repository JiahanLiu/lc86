module offset_detector (
    input [15:0] opcode,
    input operand_override,
    input opcode_size,
    output offset_present,
    output [1:0] offset_size
);

wire op0_b, op1_b, op2_b, op3_b, op4_b, op5_b, op6_b, op7_b;
wire out1a, out2a, out3a, out4a, out5a, out6a, out7a, out8a;
wire out9a, out10a, out11a, out12a, out13a, out14a, out15a;
wire out16a, out17a, out18a, out19a, out20a, out21a, out22a;
wire out23a;
wire out1r, out2r, out4r, out5r, out7r, out8r;
wire opcode_size_bf, opcode_size_b;
wire operand_override_b;
wire op0_buf, op2_buf, op3_buf, op7_buf;

bufferH16$ buf0 (op0_buf, opcode[0]);
bufferH16$ buf2 (op2_buf, opcode[2]);
bufferH16$ buf3 (op3_buf, opcode[3]);
bufferH16$ buf7 (op7_buf, opcode[7]);

inv1$ inv0 (op0_b, op0_buf);
inv1$ inv1 (op1_b, opcode[1]);
inv1$ inv2 (op2_b, op2_buf);
inv1$ inv3 (op3_b, op3_buf);
inv1$ inv4 (op4_b, opcode[4]);
inv1$ inv5 (op5_b, opcode[5]);
inv1$ inv6 (op6_b, opcode[6]);
inv1$ inv7 (op7_b, op7_buf);
inv1$ inv8 (operand_override_b, operand_override);
inv1$ inv9 (opcode_size_bf, opcode_size);

bufferH16$ buf8 (opcode_size_b, opcode_size_bf);

// Logic for offset
// offset_size:
// 00 - 8
// 01 - 16
// 10 - 32
// 11 - 48
// offset_present = (op7 &!op6 &!op5 &!op4 &!op3 &op2 &op0 &operand_override
//      &opcode_size) | (op7 &!op6 &!op5 &!op4 &!op3 &op2 &op0
//      &!operand_override &opcode_size) | (!op7 &op6 &op5 &op4 &!op3 &op2
//      &op0 &!opcode_size) | (op7 &!op6 &!op5 &op4 &op3 &!op2 &op1 &!op0
//      &!opcode_size) | (op7 &op6 &op5 &!op4 &op3 &!op2 &!opcode_size);
and4$ and1 (out1a, op7_buf, op6_b, op5_b, op4_b);
and4$ and2 (out2a, op3_b, op2_buf, op0_buf, operand_override);
and3$ and3 (out3a, opcode_size, out1a, out2a);

and4$ and4 (out4a, op3_b, op2_buf, op0_buf, operand_override_b);
and3$ and5 (out5a, opcode_size, out1a, out4a);

and4$ and6 (out6a, op7_b, opcode[6], opcode[5], opcode[4]);
and3$ and7 (out7a, op3_b, op2_buf, op0_buf);
and3$ and8 (out8a, out6a, out7a, opcode_size_b);

and4$ and9 (out9a, op7_buf, op6_b, op5_b, opcode[4]);
and4$ and10 (out10a, op3_buf, op2_b, opcode[1], op0_b);
and3$ and11 (out11a, opcode_size_b, out9a, out10a);

and4$ and12 (out12a, op7_buf, opcode[6], opcode[5], op4_b);
and4$ and13 (out13a, op3_buf, op2_b, opcode_size_b, out12a);

or3$ or1 (out1r, out3a, out5a, out8a);
or2$ or2 (out2r, out11a, out13a);
or2$ or3 (offset_present, out1r, out2r);

// offset_size1 = (op7 &!op6 &!op5 &!op4 &!op3 &op2 &op0 &!operand_override
//      &opcode_size) | (op7 &!op6 &!op5 &op4 &op3 &!op2 &op1 &!op0
//      &!opcode_size) | (op7 &op6 &op5 &!op4 &op3 &!op2 &!op1
//      &!operand_override &!opcode_size) | (op7 &op6 &op5 &!op4 &op3 &!op2
//      &op1 &!op0 &!opcode_size);
and4$ and14 (out14a, op3_b, op2_buf, op0_buf, operand_override_b);
and3$ and15 (out15a, out14a, out1a, opcode_size);

and4$ and18 (out18a, op3_buf, op2_b, op1_b, operand_override_b);
and3$ and19 (out19a, out18a, opcode_size_b, out12a);

and3$ and20 (out20a, out10a, out12a, opcode_size_b);

or2$ or4 (out4r, out15a, out11a);
or2$ or5 (out5r, out19a, out20a);
or2$ or6 (offset_size[1], out4r, out5r);

// offset_size0 = (op7 &!op6 &!op5 &!op4 &!op3 &op2 &op0 &operand_override
//      &opcode_size) | (op7 &op6 &op5 &!op4 &op3 &!op2 &op1 &!op0
//      &!operand_override &!opcode_size) | (op7 &op6 &op5 &!op4 &op3 &!op2
//      &!op1 &operand_override &!opcode_size) | (op7 &!op6 &!op5 &op4 &op3
//      &!op2 &op1 &!op0 &!opcode_size);
and4$ and16 (out16a, op7_buf, opcode[6], opcode[5], op4_b);
and4$ and21 (out21a, out16a, out10a, operand_override_b, opcode_size_b);

and4$ and22 (out22a, op3_buf, op2_b, op1_b, operand_override);
and3$ and23 (out23a, out12a, out22a, opcode_size_b);

or2$ or7 (out7r, out3a, out11a);
or2$ or8 (out8r, out21a, out23a);
or2$ or9 (offset_size[0], out7r, out8r);

endmodule
