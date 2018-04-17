module immediate_detector (
    input [15:0] opcode, 
    input operand_override,
    output imm_present,
    output [1:0] imm_size
);

wire op0_buf, op1_buf, op2_buf, op3_buf, op4_buf, op5_buf, op6_buf, op_buf7, operand_override_buf;
wire op0_b, op1_b, op2_b, op3_b, op4_b, op5_b, op6_b, op7_b, operand_override_b;
wire op0_bf, op1_bf, op2_bf, op3_bf, op4_bf, op5_bf, op6_bf, op7_bf, operand_override_bf;
wire out1a, out2a, out3a, out4a, out5a, out6a, out7a, out8a;
wire out9a, out10a, out11a, out12a, out13a, out14a, out15a;
wire out16a, out17a, out18a, out19a, out20a, out21a, out22a;
wire out23a, out24a, out25a;
wire out1r, out2r, out3r, out4r, out5r, out7r, out8r;
wire out1p, out2p, out3p, out4p, out5p, out6p, out7p, out8p;
wire out9p, out10p, out11p, out12p, out13p, out14p, out15p;
wire out16p, out17p, out18p, out19p;
wire out1s, out2s, out3s, out4s, out5s, out6s, out7s, out8s;
wire out9s, out10s, out11s, out12s, out13s, out14s, out15s;
wire out16s, out17s;
wire out1k, out2k, out3k, out4k, out5k, out6k;
wire op15_b, op14_b, op13_b, op12_b;

// Buffering for signals having fanout > 4
bufferH16$ buf0 (op0_buf, opcode[0]);
bufferH16$ buf1 (op1_buf, opcode[1]);
bufferH16$ buf2 (op2_buf, opcode[2]);
bufferH16$ buf3 (op3_buf, opcode[3]);
bufferH16$ buf4 (op4_buf, opcode[4]);
bufferH16$ buf5 (op5_buf, opcode[5]);
bufferH16$ buf6 (op6_buf, opcode[6]);
bufferH16$ buf7 (op7_buf, opcode[7]);
bufferH16$ buf16 (operand_override_buf, operand_override);

inv1$ inv0 (op0_bf, op0_buf);
inv1$ inv1 (op1_bf, op1_buf);
inv1$ inv2 (op2_bf, op2_buf);
inv1$ inv3 (op3_bf, op3_buf);
inv1$ inv4 (op4_bf, op4_buf);
inv1$ inv5 (op5_bf, op5_buf);
inv1$ inv6 (op6_bf, op6_buf);
inv1$ inv7 (op7_bf, op7_buf);
inv1$ inv8 (operand_override_bf, operand_override_buf);
inv1$ inv15 (op15_b, opcode[15]);
inv1$ inv14 (op14_b, opcode[14]);
inv1$ inv13 (op13_b, opcode[13]);
inv1$ inv12 (op12_b, opcode[12]);

// Buffering for signals having fanout > 4
bufferH16$ buf8 (op0_b, op0_bf);
bufferH16$ buf9 (op1_b, op1_bf);
bufferH16$ buf10 (op2_b, op2_bf);
bufferH16$ buf11 (op3_b, op3_bf);
bufferH16$ buf12 (op4_b, op4_bf);
bufferH16$ buf13 (op5_b, op5_bf);
bufferH16$ buf14 (op6_b, op6_bf);
bufferH16$ buf15 (op7_b, op7_bf);
bufferH16$ buf17 (operand_override_b, operand_override_bf);

//assign op7 = opcode[7];
//assign op6 = opcode[6];
//assign op5 = opcode[5];
//assign op4 = opcode[4];
//assign op3 = opcode[3];
//assign op2 = opcode[2];
//assign op1 = opcode[1];
//assign op0 = opcode[0];


// Logic for opcode[15:8] = 0F70
and4$ and1k (out1k, op15_b, op14_b, op13_b, op12_b);
and4$ and2k (out2k, opcode[11], opcode[10], opcode[9], opcode[8]);
and2$ and3k (out3k, out1k, out2k);

and4$ and4k (out4k, op7_b, op6_buf, op5_buf, op4_buf);
and4$ and5k (out5k, op3_b, op2_b, op1_b, op0_b);
and2$ and6k (out6k, out5k, out4k);


// Logic for imm_present
//assign out4r = (op7 &op6 &!op5 &!op4 &!op3 &op2 &op1 &op0 &!operand_override) | (
//    op7 &op6 &!op5 &!op4 &!op3 &op2 &op1 &op0 &operand_override) | (!op7
//     &op6 &op5 &!op4 &op3 &!op2 &!op0) | (op7 &op6 &!op5 &!op4 &!op3 &op1 &!op0) | (
//    op7 &op6 &!op5 &!op4 &!op2 &op1 &!op0) | (op7 &!op6 &!op5 &!op4 &!op3 &!op2 &op0) | (
//    !op7 &!op6 &!op4 &!op3 &op2 &!op1) | (op7 &!op5 &!op4 &!op3 &!op2 &!op1) | (
//    !op7 &!op6 &!op5 &!op4 &op2 &!op1) | (op7 &!op6 &op5 &op4);

and4$ and4 (out4a, op7_buf, op6_buf, op5_b, op4_b);
and4$ and5 (out5a, op3_b, op2_buf, op1_buf, op0_buf);
and3$ and6 (out6a, out4a, out5a, operand_override_b);

and4$ and7 (out7a, op7_buf, op6_buf, op5_b, op4_b);
and4$ and8 (out8a, op3_b, op2_buf, op1_buf, op0_buf);
and3$ and9 (out9a, out7a, out8a, operand_override_buf);

and4$ and10 (out10a, op7_b, op6_buf, op5_buf, op4_b);
and4$ and11 (out11a, op3_buf, op2_b, op0_b, out10a);

and4$ and12 (out12a, op7_buf, op6_buf, op5_b, op4_b);
and4$ and13 (out13a, op3_b, op1_buf, op0_b, out12a);

and4$ and14 (out14a, op7_buf, op6_buf, op5_b, op4_b);
and4$ and15 (out15a, op2_b, op1_buf, op0_b, out14a);

and4$ and16 (out16a, op7_buf, op6_b, op5_b, op4_b);
and4$ and17 (out17a, op3_b, op2_b, op0_buf, out16a);

and4$ and18 (out18a, op7_b, op6_b, op4_b, op3_b);
and3$ and19 (out19a, op2_buf, op1_b, out18a);

and4$ and20 (out20a, op7_b, op6_b, op5_b, op4_b);
and3$ and21 (out21a, op2_buf, op1_b, out20a);

and4$ and22 (out22a, op7_buf, op5_b, op4_b, op3_b);
and3$ and23 (out23a, op2_b, op1_b, out22a);

and3$ and24 (out24a, op7_buf, op6_b, op5_buf);
and2$ and25 (out25a, op4_buf, out24a);

or3$ or1 (out1r, out6a, out9a, out11a);
or4$ or2 (out2r, out13a, out15a, out17a, out19a);
or3$ or3 (out3r, out21a, out23a, out25a);
or3$ or4 (out4r, out1r, out2r, out3r);

mux2$ mux1 (imm_present, out4r, out6k, out3k);

//assign imm_size[1] = (!op7 &op6 &op5 &!op4 &op3 &!op2 &!op1 &!op0
//      &!operand_override) | (op7 &op6 &!op5 &!op4 &!op3 &op2 &op1 &op0
//      &!operand_override) | (op7 &!op6 &!op5 &!op4 &!op3 &!op2 &!op1 &op0
//      &!operand_override) | (!op7 &!op6 &!op4 &!op3 &op2 &!op1 &op0
//      &!operand_override) | (!op7 &!op6 &!op5 &!op4 &op2 &!op1 &op0
//      &!operand_override) | (op7 &!op6 &op5 &op4 &op3
//      &!operand_override);
and4$ and1s (out1s, op7_b, op6_buf, op5_buf, op4_b);
and4$ and2s (out2s, op3_buf, op2_b, op1_b, op0_b);
and3$ and3s (out3s, out1s, out2s, operand_override_b);

and4$ and4s (out4s, op7_buf, op6_buf, op5_b, op4_b);
and4$ and5s (out5s, op3_b, op2_buf, op1_buf, op0_buf);
and3$ and6s (out6s, out4s, out5s, operand_override_b);

and4$ and7s (out7s, op7_buf, op6_b, op5_b, op4_b);
and4$ and8s (out8s, op3_b, op2_b, op1_b, op0_buf);
and3$ and9s (out9s, out7s, out8s, operand_override_b);

and4$ and10s (out10s, op7_b, op6_b, op4_b, op3_b);
and4$ and11s (out11s, op2_buf, op1_b, op0_buf, operand_override_b);
and2$ and12s (out12s, out10s, out11s);

and4$ and13s (out13s, op7_b, op6_b, op5_b, op4_b);
and4$ and14s (out14s, op2_buf, op1_b, op0_buf, operand_override_b);
and2$ and15s (out15s, out13s, out14s);

and4$ and16s (out16s, op7_buf, op6_b, op5_buf, op4_buf);
and3$ and17s (out17s, op3_buf, operand_override_b, out16s);

or4$ or5 (out5r, out3s, out6s, out9s, out12s);
or3$ or6 (imm_size[1], out15s, out17s, out5r);

//assign imm_size[0] = (!op7 &op6 &op5 &!op4 &op3 &!op2 &!op1 &!op0
//      &operand_override) | (op7 &op6 &!op5 &!op4 &!op3 &op2 &op1 &op0
//      &operand_override) | (op7 &!op6 &!op5 &!op4 &!op3 &!op2 &!op1 &op0
//      &operand_override) | (!op7 &!op6 &!op4 &!op3 &op2 &!op1 &op0
//      &operand_override) | (!op7 &!op6 &!op5 &!op4 &op2 &!op1 &op0
//      &operand_override) | (op7 &!op6 &op5 &op4 &op3
//      &operand_override) | (op7 &op6 &!op5 &!op4 &!op2 &op1 &!op0);
and4$ and1p (out1p, op7_b, op6_buf, op5_buf, op4_b);
and4$ and2p (out2p, op3_buf, op2_b, op1_b, op0_b);
and3$ and3p (out3p, out1p, out2p, operand_override_buf);

and4$ and4p (out4p, op7_buf, op6_buf, op5_b, op4_b);
and4$ and5p (out5p, op3_b, op2_buf, op1_buf, op0_buf);
and3$ and6p (out6p, out4p, out5p, operand_override_buf);

and4$ and7p (out7p, op7_buf, op6_b, op5_b, op4_b);
and4$ and8p (out8p, op3_b, op2_b, op1_b, op0_buf);
and3$ and9p (out9p, out7p, out8p, operand_override_buf);

and4$ and10p (out10p, op7_b, op6_b, op4_b, op3_b);
and4$ and11p (out11p, op2_buf, op1_b, op0_buf, operand_override_buf);
and2$ and12p (out12p, out10p, out11p);

and4$ and13p (out13p, op7_b, op6_b, op5_b, op4_b);
and4$ and14p (out14p, op2_buf, op1_b, op0_buf, operand_override_buf);
and2$ and15p (out15p, out13p, out14p);

and4$ and16p (out16p, op7_buf, op6_b, op5_buf, op4_buf);
and3$ and17p (out17p, op3_buf, operand_override_buf, out16p);

and4$ and18p (out18p, op7_buf, op6_buf, op5_b, op4_b);
and4$ and19p (out19p, op2_b, op1_buf, op0_b, out18p);

or3$ or7 (out7r, out3p, out6p, out9p);
or3$ or8 (out8r, out12p, out15p, out17p);
or3$ or9 (imm_size[0], out19p, out7r, out8r);

endmodule
