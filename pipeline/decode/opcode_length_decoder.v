module opcode_length_decoder (
    input isOpcode1, isOpcode2, isOpcode3, isOpcode4, isOpcode5,
    input [7:0] byte1, byte2, byte3, byte4, byte5,
    output [2:0] opcode_sel,
    output opcode_size
);

wire byte1_7b, byte1_6b, byte1_5b, byte1_4b;
wire byte2_7b, byte2_6b, byte2_5b, byte2_4b;
wire byte3_7b, byte3_6b, byte3_5b, byte3_4b;
wire byte4_7b, byte4_6b, byte4_5b, byte4_4b;
wire isOpcode1_b, isOpcode2_b, isOpcode3_b;
wire outa1, outa2, outa3, outa4, outa6;
wire outa7, outa8, outa9, outa11, outa12;
wire outa13, outa14, outa16, outa17, outa18;
wire outa19, outa21, outa22, outa23;

inv1$ inv1 (byte1_7b, byte1[7]);
inv1$ inv2 (byte1_6b, byte1[6]);
inv1$ inv3 (byte1_5b, byte1[5]);
inv1$ inv4 (byte1_4b, byte1[4]);

inv1$ inv5 (byte2_7b, byte2[7]);
inv1$ inv6 (byte2_6b, byte2[6]);
inv1$ inv7 (byte2_5b, byte2[5]);
inv1$ inv8 (byte2_4b, byte2[4]);

inv1$ inv9 (byte3_7b, byte3[7]);
inv1$ inv10 (byte3_6b, byte3[6]);
inv1$ inv11 (byte3_5b, byte3[5]);
inv1$ inv12 (byte3_4b, byte3[4]);

inv1$ inv13 (byte4_7b, byte4[7]);
inv1$ inv14 (byte4_6b, byte4[6]);
inv1$ inv15 (byte4_5b, byte4[5]);
inv1$ inv16 (byte4_4b, byte4[4]);

inv1$ inv21 (isOpcode1_b, isOpcode1);
inv1$ inv22 (isOpcode2_b, isOpcode2);
inv1$ inv23 (isOpcode3_b, isOpcode3);

// Check whether the bytes are 0F - which indicates a 2nd opcode
and4$ and1 (outa1, byte1_7b, byte1_6b, byte1_5b, byte1_4b);
and4$ and2 (outa2, byte2_7b, byte2_6b, byte2_5b, byte2_4b);
and4$ and3 (outa3, byte3_7b, byte3_6b, byte3_5b, byte3_4b);
and4$ and4 (outa4, byte4_7b, byte4_6b, byte4_5b, byte4_4b);

and4$ and6 (outa6, byte1[3], byte1[2], byte1[1], byte1[0]);
and4$ and7 (outa7, byte2[3], byte2[2], byte2[1], byte2[0]);
and4$ and8 (outa8, byte3[3], byte3[2], byte3[1], byte3[0]);
and4$ and9 (outa9, byte4[3], byte4[2], byte4[1], byte4[0]);

and2$ and11 (outa11, outa1, outa6);
and2$ and12 (outa12, outa2, outa7);
and2$ and13 (outa13, outa3, outa8);
and2$ and14 (outa14, outa4, outa9);

// Logic for opcode_sel
// opcode_sel2 = (!isop1 &!isop2 &!isop3 &isop4 &isop5 &op4) | (!isop1 &!isop2 &isop3
//      &isop4 &op3) | (isop1 &isop2 &op1) | (!isop1 &isop2 &isop3 &op2);
// opcode_sel1 = (!isop1 &!isop2 &!isop3 &isop4) | (!isop1 &!isop2 &isop3);
// opcode_sel0 = (!isop1 &!isop2 &!isop3 &isop4) | (!isop1 &isop2);
and4$ and16 (outa16, isOpcode1_b, isOpcode2_b, isOpcode3_b, isOpcode4);
and2$ and17 (outa17, isOpcode1_b, isOpcode2);
or2$ or1 (opcode_sel[0], outa16, outa17);

and3$ and18 (outa18, isOpcode1_b, isOpcode2_b, isOpcode3);
or2$ or2 (opcode_sel[1], outa16, outa18);

and3$ and19 (outa19, isOpcode5, outa14, outa16);
and3$ and21 (outa21, isOpcode4, outa13, outa18);
and3$ and22 (outa22, isOpcode1, isOpcode2, outa11);
and4$ and23 (outa23, isOpcode1_b, isOpcode2, isOpcode3, outa12);
or4$ or3 (opcode_sel[2], outa19, outa21, outa22, outa23);

// Opcode_size: 0 for 1 byte, 1 for 2bytes
assign opcode_size = opcode_sel[2];

endmodule
