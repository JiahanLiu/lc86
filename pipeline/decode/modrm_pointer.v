module modrm_pointer (
    input opcode_size,
    input prefix_present,
    input [1:0] prefix_size,
    output [2:0] modrm_sel
);

wire out1a, out2a, out3a, out4a, out5a, out6a, out7a;
wire out1r;
wire prefix_present_b;
wire prefix_size0_b, prefix_size1_b, opcode_size_b;

inv1$ inv1 (prefix_size0_b, prefix_size[0]);
inv1$ inv2 (prefix_size1_b, prefix_size[1]);
inv1$ inv3 (opcode_size_b, opcode_size);
inv1$ inv4 (prefix_present_b, prefix_present);

// Logic for modrm_sel signal
// # MODRM location
// # 101 2
// # 110 3
// # 111 4
// # 100 5
// # 001 6
// modrm_sel2 = (prefix_present &!prefix_size1 &prefix_size0) | (prefix_size1
//      &!prefix_size0) | (prefix_size0 &!opcode_size) | (!prefix_present
//      &opcode_size) | (!prefix_present &!opcode_size);
// 
// modrm_sel1 = (prefix_present &prefix_size1 &!prefix_size0 &!opcode_size) | (
//     prefix_present &!prefix_size1 &prefix_size0) | (!prefix_present
//      &opcode_size);
// 
// modrm_sel0 = (prefix_present &prefix_size1 &!prefix_size0 &!opcode_size) | (
//     prefix_present &prefix_size0 &opcode_size) | (!prefix_present
//      &!opcode_size);

and3$ and1 (out1a, prefix_present, prefix_size1_b, prefix_size[0]);
and2$ and2 (out2a, prefix_size[1], prefix_size0_b);
and2$ and3 (out3a, prefix_size[0], opcode_size_b);
and2$ and4 (out4a, prefix_present_b, opcode_size);
and2$ and5 (out5a, prefix_present_b, opcode_size_b);
or3$ or1 (out1r, out1a, out2a, out3a);
or3$ or2 (modrm_sel[2], out1r, out5a, out4a);

and4$ and6 (out6a, prefix_present, prefix_size[1], prefix_size0_b, opcode_size_b);
or3$ or3 (modrm_sel[1], out6a, out1a, out4a);

and3$ and7 (out7a, prefix_present, prefix_size[0], opcode_size);
or3$ or4 (modrm_sel[0], out6a, out7a, out5a);

endmodule
