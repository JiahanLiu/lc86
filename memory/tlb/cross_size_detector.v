module cross_size_detector (
   input [3:0] offset,
   input [1:0] size,

   output [3:0] cross_size,
   output [3:0] cross_size_next
);

   wire offset2_bar, offset1_bar, offset0_bar;
   wire and0_out, and1_out, and2_out, and3_out, and4_out,
	and5_out, and6_out, and7_out, and8_out, and9_out,
	and10_out, and11_out, and12_out, and13_out, and14_out;
   wire or0_out, or1_out, or2_out;
   
   wire and15_out, and16_out, and17_out, and18_out;
   wire or3_out, or4_out;
   
   /*
    cross_size[3] = 1'b0;
    cross_size[2] = offset[3]&offset[2] & offset1_bar&offset0_bar & size[1]&size[0] ||
                    offset[3]&offset2_bar&offset[1]&offset0_bar & size[1]&size[0] ||
                    offset[3]&offset2_bar&offset[0] & size[1]&size[0]
    delay: and4$ + and3$ + or3$
    
    cross_size[1] = offset[3]&offset2_bar&offset[1]&offset0_bar & size[1]&size[0] ||
                    offset[3]&offset[2]&offset[1]&offset0_bar & size [1] ||
                    offset[3]&offset1_bar & offset[0]&size[1]&size[0] ||
                    offset[3]&offset[2]&offset1_bar&offset[0]&size[1]
    delay: and4$ + and2$ + or4$
    
    cross_size[0] = offset[3]&offset[2]&offset[1]&offset[0]&size[0] ||
                    offset[3]&offset2_bar&offset[0] & size[1]&size[0] ||
                    offset[3]&offset[2]&offset[0]&size[1]
    delay: and4$ + and2$ + or3$
    
    cross_size_next[3] = 1'b0;
    cross_size_next[2] = offset[3]&offset[2]&size[1]&size[0]
    
    cross_size_next[1] = offset[3]&offset[2]&offset[1]&size[1] ||
                         offset[3]&offset[1]&size[1]&size[0]
    
    cross_size_next[0] = offset[3]&offset[2]&offset[0]&size[1] ||
                         offset[3]&offset[0]&size[1]&size[0] ||
                         offset[3]&offset[2]&offset[1]&offset[0]&size[0]
    delay: and4$ + and2$ + or3$
    */
   assign cross_size[3] = 1'b0;
   assign cross_size[2] = or0_out;
   assign cross_size[1] = or1_out;
   assign cross_size[0] = or2_out;
   
   inv1$
     inv0 (offset2_bar, offset[2]),
     inv1 (offset1_bar, offset[1]),
     inv2 (offset0_bar, offset[0]);

   // cross_size[2]
   and4$ and0 (and0_out, offset[3], offset[2], size[1], size[0]);
   and3$ and1 (and1_out, and0_out, offset1_bar, offset0_bar);
   and4$ and2 (and2_out, offset[3], offset[1], size[1], size[0]);
   and3$ and3 (and3_out, and2_out, offset2_bar, offset0_bar);
   and4$ and4 (and4_out, offset[3], offset[0], size[1], size[0]);
   and2$ and5 (and5_out, and4_out, offset2_bar);
   or3$ or0 (or0_out, and1_out, and3_out, and5_out);

   // cross_size[1]
   and4$ and6 (and6_out, offset[3], offset[2], offset[1], size[1]);
   and2$ and7 (and7_out, and6_out, offset0_bar);
   and4$ and8 (and8_out, offset[3], offset[0], size[1], size[0]);
   and2$ and9 (and9_out, and8_out, offset1_bar);
   and4$ and10 (and10_out, offset[3], offset[2], offset[0], size[1]);
   and2$ and11 (and11_out, and10_out, offset1_bar);
   or4$ or1 (or1_out, and3_out, and7_out, and9_out, and11_out);

   // cross_size[0]
   and4$ and12 (and12_out, offset[3], offset[2], offset[1], offset[0]);
   and2$ and13 (and13_out, and12_out, size[0]);
   and4$ and14 (and14_out, offset[3], offset[2], offset[0], size[1]);
   or3$ or2 (or2_out, and13_out, and5_out, and14_out);

   assign cross_size_next[3] = 1'b0;
   assign cross_size_next[2] = and15_out;
   assign cross_size_next[1] = or3_out;
   assign cross_size_next[0] = or4_out;
   
   // cross_size_next[2]
   and4$ and15 (and15_out, offset[3], offset[2], size[1], size[0]);

   // cross_size_next[1]
   and4$ and16 (and16_out, offset[3], offset[2], offset[1], size[1]);
   and4$ and17 (and17_out, offset[3], offset[1], size[1], size[0]);
   or2$ or3 (or3_out, and16_out, and17_out);

   // cross_size_next[0]
   and4$ and18 (and18_out, offset[3], offset[0], size[1], size[0]);
   or3$ or4 (or4_out, and14_out, and18_out, and13_out);
      
endmodule // cross_size_detector
