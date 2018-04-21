module ifu_mask_detector (
   input [3:0] SIZE,

   output [127:0] MASK
);
/*
mask[15] = ;
mask[14] = (size[3]&size[2]&size[1]&size[0]);
mask[13] = (size[3]&size[2]&size[1]);
mask[12] = (size[3]&size[2]&size[0]) | (size[3]&size[2]&size[1]);
mask[11] = (size[3]&size[2]);
mask[10] = (size[3]&size[1]&size[0]) | (size[3]&size[2]);
mask[9] = (size[3]&size[1]) | (size[3]&size[2]);
mask[8] = (size[3]&size[0]) | (size[3]&size[1]) | (size[3]&size[2]);
mask[7] = (size[3]);
mask[6] = (size[2]&size[1]&size[0]) | (size[3]);
mask[5] = (size[2]&size[1]) | (size[3]);
mask[4] = (size[2]&size[0]) | (size[2]&size[1]) | (size[3]);
mask[3] = (size[2]) | (size[3]);
mask[2] = (size[1]&size[0]) | (size[2]) | (size[3]);
mask[1] = (size[1]) | (size[2]) | (size[3]);
mask[0] = (size[0]) | (size[1]) | (size[2]) | (size[3]);
*/
   wire [14:0] bitmask;

   // mask[14]
   and4$ and0 (and0_out, SIZE[3], SIZE[2], SIZE[1], SIZE[0]);
   assign bitmask[14] = and0_out;
   // mask[13]
   and3$ and1 (and1_out, SIZE[3], SIZE[2], SIZE[1]);
   assign bitmask[13] = and1_out;
   // mask[12]
   and3$ and2 (and2_out, SIZE[3], SIZE[2], SIZE[0]);
   or2$ or0 (or0_out, and1_out, and2_out);
   assign bitmask[12] = or0_out;
   // mask[11]
   and2$ and3 (and3_out, SIZE[3], SIZE[2]);
   assign bitmask[11] = and3_out;
   // mask[10]
   and3$ and4 (and4_out, SIZE[3], SIZE[1], SIZE[0]);
   or2$ or1 (or1_out, and4_out, and3_out);
   assign bitmask[10] = or1_out;
   // mask[9]
   and2$ and5 (and5_out, SIZE[3], SIZE[1]);
   or2$ or2 (or2_out, and5_out, and3_out);
   assign bitmask[9] = or2_out;
   // mask[8]
   and2$ and6 (and6_out, SIZE[3], SIZE[0]);
   or3$ or3 (or3_out, and6_out, and5_out, and3_out);
   assign bitmask[8] = or3_out;
   // mask[7] = SIZE[3]
   assign bitmask[7] = SIZE[3];
   // mask[6]
   and3$ and7 (and7_out, SIZE[2], SIZE[1], SIZE[0]);
   or2$ or4 (or4_out, and7_out, SIZE[3]);
   assign bitmask[6] = or4_out;
   // mask[5]
   and2$ and8 (and8_out, SIZE[2], SIZE[1]);
   or2$ or5 (or5_out, and8_out, SIZE[3]);
   assign bitmask[5] = or5_out;
   // mask[4]
   and2$ and9 (and9_out, SIZE[2], SIZE[0]);
   or3$ or6 (or6_out, and9_out, and8_out, SIZE[3]);
   assign bitmask[4] = or6_out;
   // mask[3]
   or2$ or7 (or7_out, SIZE[2], SIZE[3]);
   assign bitmask[3] =  or7_out;
   // mask[2]
   and2$ and10 (and10_out, SIZE[1], SIZE[0]);
   or3$ or8 (or8_out, and10_out, SIZE[2], SIZE[3]);
   assign bitmask[2] = or8_out;
   // mask[1]
   or3$ or9 (or9_out, SIZE[1], SIZE[2], SIZE[3]);
   assign bitmask[1] = or9_out;
   // mask[0]
   or4$ or10 (or10_out, SIZE[0], SIZE[1], SIZE[2], SIZE[3]);
   assign bitmask[0] = or10_out;

   wire [14:0] buffer_out;

   bufferH16$ buffer0 [14:0] (buffer_out, bitmask);

   assign MASK[127:120] = 8'b0;
   assign MASK[119:0] = {{8{buffer_out[14]}}, {8{buffer_out[13]}}, {8{buffer_out[12]}}, {8{buffer_out[11]}}, {8{buffer_out[10]}}, {8{buffer_out[9]}}, {8{buffer_out[8]}}, {8{buffer_out[7]}}, {8{buffer_out[6]}}, {8{buffer_out[5]}}, {8{buffer_out[4]}}, {8{buffer_out[3]}}, {8{buffer_out[2]}}, {8{buffer_out[1]}}, {8{buffer_out[0]}}};

endmodule


