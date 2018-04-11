module prefix_checker (
    input [7:0] instr_byte,
    output isPrefix,
    output isOpcode,
    output operand_override,
    output segment_override,
    output repeat_prefix,
    output [2:0] segID
);

wire i7_b, i6_b, i4_b, i3_b, i2_b, i1_b, i0_b;
wire out1, out2, out3, out4, out5, out6, out7, out8, out9;
wire out10, out11, out12, out15, out16, out17, out18, out19, out20, out21, out22;
wire out_or1;

// Inverted bits of instr_byte
inv1$ not1(i7_b, instr_byte[7]);
inv1$ not2(i6_b, instr_byte[6]);
inv1$ not3(i4_b, instr_byte[4]);
inv1$ not4(i3_b, instr_byte[3]);
inv1$ not5(i2_b, instr_byte[2]);
inv1$ not6(i1_b, instr_byte[1]);
inv1$ not7(i0_b, instr_byte[0]);

// Logic for isPrefix
// isprefix = (i7 &i6 &i5 &i4 &!i3 &!i2 &i1 &!i0) | (!i7 &i6 &i5 &!i4 &!i3 &i2 &!i1) | 
//      (!i7 &i6 &i5 &!i4 &!i3 &i2 &i1 &!i0) | (!i7 &!i6 &i5 &i2 &i1 &!i0);

and4$ and1 (out1, instr_byte[7], instr_byte[6], instr_byte[5], instr_byte[4]);
and4$ and2 (out2, i3_b, i2_b, instr_byte[1], i0_b);
and2$ and3 (out3, out1, out2);

and4$ and4 (out4, i7_b, instr_byte[6], instr_byte[5], i4_b);
and3$ and5 (out5, i3_b, instr_byte[2], i1_b);
and2$ and6 (out6, out4, out5);

and4$ and10 (out10, i7_b, instr_byte[6], instr_byte[5], i4_b);
and4$ and11 (out11, i3_b, instr_byte[2], instr_byte[1], i0_b);
and2$ and12 (out12, out10, out11);

and3$ and7 (out7, i7_b, i6_b, instr_byte[5]);
and3$ and8 (out8, instr_byte[2], instr_byte[1], i0_b);
and2$ and15 (out15, out7, out8);

and4$ and9 (out9, instr_byte[2], instr_byte[1], i0_b, instr_byte[3]);

or4$ or1 (isPrefix, out3, out6, out12, out15);

inv1$ inv1 (isOpcode, isPrefix);

// Logic for operand_override
// operand_override = (!i7 &i6 &i5 &!i4 &!i3 &i2 &i1 &!i0);
assign operand_override = out12; 

// Logic for segment_override

// segment_override = (!i7 &i6 &i5 &!i4 &!i3 &i2 &!i1) | (!i7 &!i6 &i5 &i2 &i1 &!i0);
or2$ or3 (segment_override, out6, out15);

// Logic for repeat_prefix
// repeat = (i7 &i6 &i5 &i4 &!i3 &!i2 &i1 &!i0);
assign repeat_prefix = out3;

// Logic for segID 
// segID2 = (!i7 &i6 &i5 &!i4 &!i3 &i2 &!i1);
// segID1 = (!i7 &!i6 &i5 &i4 &i3 &i2 &i1 &!i0) | (!i7 &i5 &!i4 &!i3 &i2 &i1 &!i0);
// segID0 = (!i7 &i6 &i5 &!i4 &!i3 &i2 &!i1 &i0) | (!i7 &!i6 &i5 &!i3 &i2 &i1 &!i0);

// segID1 = (!i7 &!i6 &i5 &i4 &i2 &i1 &!i0);
// segID0 = (!i7 &i6 &i5 &!i4 &!i3 &i2 &!i1 &i0) | (!i7 &!i6 &i5 &i3 &i2 &i1 &!i0);


assign segID[2] = out6;

and4$ and20 (out20, i7_b, i6_b, instr_byte[5], instr_byte[4]);
and3$ and21 (out21, instr_byte[2], instr_byte[1], i0_b);
and2$ and22 (segID[1], out20, out21);

and4$ and16 (out16, i3_b, instr_byte[2], i1_b, instr_byte[0]);
and2$ and18 (out18, out16, out4);
and2$ and17 (out17, out9, out7);
or2$ or4 (segID[0], out18, out17);

endmodule
