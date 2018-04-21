module cross_icache_line_size_detector (
   input [3:0] OFFSET,

   output [4:0] SIZE1, SIZE2
);

/*
size1[4] = (!offset[3]&!offset[2]&!offset[1]&!offset[0]);

size1[3] = (offset[3]&!offset[2]&!offset[1]&!offset[0]) | (!offset[3]
    &offset[0]) | (!offset[3]&offset[2]) | (!offset[3]&offset[1]);

size1[2] = (offset[2]&!offset[1]&!offset[0]) | (!offset[2]&offset[1]) | (
    !offset[2]&offset[0]);

size1[1] = (offset[1]&!offset[0]) | (!offset[1]&offset[0]);

size1[0] = (offset[0]);
*/
   wire [3:0] offset_bar;
   wire and0_out, and1_out, and2_out, and3_out, and4_out,
        and5_out, and6_out, and7_out, and8_out, and9_out;
   wire or0_out, or1_out, or2_out;

   inv1$ inv_offset [3:0] (offset_bar, OFFSET);

   and4$ and9 (and9_out, offset_bar[3], offset_bar[2], offset_bar[1], offset_bar[0]);

   assign SIZE1[4] = and9_out;

   and4$ and0 (and0_out, OFFSET[3], offset_bar[2], offset_bar[1], offset_bar[0]);
   and2$
      and1 (and1_out, offset_bar[3], OFFSET[0]),
      and2 (and2_out, offset_bar[3], OFFSET[2]),
      and3 (and3_out, offset_bar[3], OFFSET[1]);
   or4$ or0 (or0_out, and0_out, and1_out, and2_out, and3_out);

   assign SIZE1[3] = or0_out;

   and3$ and4 (and4_out, OFFSET[2], offset_bar[1], offset_bar[0]);
   and2$
      and5 (and5_out, offset_bar[2], OFFSET[1]),
      and6 (and6_out, offset_bar[2], OFFSET[0]);
   or3$ or1 (or1_out, and4_out, and5_out, and6_out);

   assign SIZE1[2] = or1_out;

   and2$
      and7 (and7_out, OFFSET[1], offset_bar[0]),
      and8 (and8_out, offset_bar[1], OFFSET[0]);
   or2$ or2 (or2_out, and7_out, and8_out);

   assign SIZE1[1] = or2_out;
   assign SIZE1[0] = OFFSET[0];

   assign SIZE2[4:0] = {1'b0, OFFSET[3:0]};

endmodule


