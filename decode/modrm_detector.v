module modrm_detector (
    input [15:0] opcode,
    output modrm_present
);

wire op1_buf, op2_buf, op3_buf, op4_buf, op5_buf, op6_buf, op_buf7;
wire op0_b, op1_b, op2_b, op3_b, op4_b, op5_b, op6_b, op7_b;
wire op2_bf, op3_bf, op4_bf, op5_bf, op6_bf;
wire op12_b, op13_b, op14_b, op15_b;
wire out1a, out2a, out3a, out4a, out5a, out6a, out7a, out8a;
wire out9a, out10a, out11a, out12a, out13a, out14a, out15a;
wire out16a, out17a, out18a, out19a, out20a, out21a, out22a;
wire out23a, out24a, out25a;
wire out1r, out2r, out3r, out4r, out5r;
wire out1p, out2p, out3p, out4p, out5p, out6p, out7p, out8p;
wire out9p, out10p, out11p, out12p, out13p, out14p, out15p;
wire out16p, out17p, out18p, outm1;

// Buffering for signals having fanout > 4
bufferH16$ buf1 (op1_buf, opcode[1]);
bufferH16$ buf2 (op2_buf, opcode[2]);
bufferH16$ buf3 (op3_buf, opcode[3]);
bufferH16$ buf4 (op4_buf, opcode[4]);
bufferH16$ buf5 (op5_buf, opcode[5]);
bufferH16$ buf6 (op6_buf, opcode[6]);
bufferH16$ buf7 (op7_buf, opcode[7]);

inv1$ inv0 (op0_b, opcode[0]);
inv1$ inv1 (op1_b, op1_buf);
inv1$ inv2 (op2_bf, op2_buf);
inv1$ inv3 (op3_bf, op3_buf);
inv1$ inv4 (op4_bf, op4_buf);
inv1$ inv5 (op5_bf, op5_buf);
inv1$ inv6 (op6_bf, op6_buf);
inv1$ inv7 (op7_b, op7_buf);
inv1$ inv12 (op12_b, opcode[12]);
inv1$ inv13 (op13_b, opcode[13]);
inv1$ inv14 (op14_b, opcode[14]);
inv1$ inv15 (op15_b, opcode[15]);

// Buffering for signals having fanout > 4
bufferH16$ buf8 (op2_b, op2_bf);
bufferH16$ buf9 (op3_b, op3_bf);
bufferH16$ buf10 (op4_b, op4_bf);
bufferH16$ buf11 (op5_b, op5_bf);
bufferH16$ buf12 (op6_b, op6_bf);

and4$ and1 (out1a, op15_b, op14_b, op13_b, op12_b);
and4$ and2 (out2a, opcode[11], opcode[10], opcode[9], opcode[8]);
and2$ and3 (out3a, out1a, out2a);

// Logic for ModRM present for 1 byte opcode
// modrm_present = (op7 &!op6 &!op5 &!op4 &op1 &op0) | (op7 &!op5 &!op4 &!op3 &!op2
//      &!op1) | (!op6 &!op5 &!op4 &op3 &!op2) | (op7 &op6 &op5 &op4 &op2 &op1) | (
//     !op7 &!op6 &!op4 &!op3 &!op2) | (op7 &op6 &!op5 &op4 &!op3 &!op2) | (op7 &!op6
//      &!op5 &!op4 &op3 &!op0) | (op7 &!op5 &!op4 &!op3 &op2 &op1);
and3$ and4 (out4a, op7_buf, op6_b, op5_b);
and3$ and5 (out5a, op4_b, op1_buf, opcode[0]);
and2$ and20 (out20a, out4a, out5a);

and3$ and6 (out6a, op7_buf, op5_b, op4_b);
and3$ and7 (out7a, op3_b, op2_b, op1_b);
and2$ and21 (out21a, out6a, out7a);

and3$ and8 (out8a, op6_b, op5_b, op4_b);
and3$ and9 (out9a, op3_buf, op2_b, out8a);

and3$ and10 (out10a, op7_buf, op6_buf, op5_buf);
and3$ and11 (out11a, op4_buf, op2_buf, op1_buf);
and2$ and22 (out22a, out10a, out11a);

and3$ and12 (out12a, op7_b, op6_b, op4_b);
and3$ and13 (out13a, op3_b, op2_b, out12a);

and3$ and14 (out14a, op7_buf, op6_buf, op5_b);
and3$ and15 (out15a, op4_buf, op3_b, op2_b);
and2$ and23 (out23a, out14a, out15a);

and3$ and16 (out16a, op7_buf, op6_b, op5_b);
and3$ and17 (out17a, op4_b, op3_buf, op0_b);
and2$ and24 (out24a, out16a, out17a);

and3$ and18 (out18a, op7_buf, op5_b, op4_b);
and3$ and19 (out19a, op3_b, op2_buf, op1_buf);
and2$ and25 (out25a, out18a, out19a);

or4$ or1 (out1r, out20a, out21a, out9a, out22a);
or4$ or2 (out2r, out13a, out23a, out24a, out25a);
or2$ or3 (out3r, out1r, out2r);

// Logic for modrm in case of opcode 
// modrm_present = (!op7 &op6 &!op5 &!op4 &!op3 &!op2 &op1 &!op0) | (op7 &!op6 &op5
//      &op4 &!op3 &!op2 &!op1) | (!op7 &op6 &op5 &op3 &op2 &op1 &op0) | (!op7 &op6 &op5
//      &op4 &!op3 &!op2 &!op1 &!op0) | (op7 &op6 &op5 &op3 &op2 &!op1 &op0) | (op7 &op6
//      &op5 &op4 &op3 &op2 &op1 &!op0);
and4$ andp1 (out1p, op7_b, op6_buf, op5_b, op4_b);
and4$ andp2 (out2p, op3_b, op2_b, op1_buf, op0_b);
and2$ andp3 (out3p, out1p, out2p);

and3$ andp4 (out4p, op7_buf, op6_b, op5_buf);
and3$ andp5 (out5p, op4_buf, op3_b, op2_b);
and3$ andp6 (out6p, op1_b, out4p, out5p);

and3$ andp7 (out7p, op7_b, op6_buf, op5_buf);
and3$ andp8 (out8p, op3_buf, op2_buf, op1_buf);
and3$ andp9 (out9p, opcode[0], out7p, out8p);

and4$ andp10 (out10p, op7_b, op6_buf, op5_buf, op4_buf);
and4$ andp11 (out11p, op3_b, op2_b, op1_b, op0_b);
and2$ andp12 (out12p, out2p, out11p);

and3$ andp13 (out13p, op7_buf, op6_buf, op5_buf);
and3$ andp14 (out14p, op3_buf, op2_buf, op1_b);
and3$ andp15 (out15p, opcode[0], out13p, out6p);

and4$ andp16 (out16p, op7_buf, op6_buf, op5_buf, op4_buf);
and4$ andp17 (out17p, op3_buf, op2_buf, op1_buf, op0_b);
and2$ andp18 (out18p, out16p, out17p);

or4$ or4 (out4r, out3p, out6p, out9p, out12p);
or3$ or5 (out5r, out4r, out15p, out18p);

// ModRM present??
// Assuming that opcode[15:8] is either 0F or 00
and2$ andm1 (outm1, out5r, out3a);
or2$ or6 (modrm_present, outm1, out3r);

endmodule
