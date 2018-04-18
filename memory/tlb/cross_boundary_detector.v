module cross_boundary_detector (
   input [11:0] offset,
   input [1:0] size,

   output cross_page,
   output cross_cl
);

   wire and0_out, and1_out, and2_out, and3_out, and4_out,
	and5_out, and6_out, and7_out, and8_out, and9_out,
	and10_out;

   wire or0_out, or1_out, or2_out;
   
   /* 
    cross_cl = offset[3] & ( (offset[2]&size[1]&size[0] || offset[0]&size[1]&size[0] || 
                               offset[1]&size[1]&size[0] || offset[2]&offset[0]&size[1])
                 || (offset[2]&offset[1]&offset[0]&size[0] || offset[2]&offset[1]&size[1] ) )
    
    cross_cl --
    delay1: and4$ + or2$ + or2$ + and2$
    delay2: and3$ + or4$ + or2$ + and2$
    
    cross_page = (offset[11]&offset[10]&offset[9]&offset[8]) & 
                 (offset[7]&offset[6]&offset[5]&offset[4]) & cross_cl
    
    cross_page --
    delay3: and4$ + or2$ + or2$ + and3$
    delay4: and3$ + or4$ + or2$ + and3$
    */

   // cross_cl
   and3$
     and0 (and0_out, offset[2], size[1], size[0]),
     and1 (and1_out, offset[1], size[1], size[0]),
     and2 (and2_out, offset[0], size[1], size[0]),
     and3 (and3_out, offset[2], offset[0], size[1]);
   or4$
     or0 (or0_out, and0_out, and1_out, and2_out, and3_out);

   and4$
     and4 (and4_out, offset[2], offset[1], offset[0], size[0]);
   and3$
     and5 (and5_out, offset[2], offset[1], size[1]);
   or2$
     or1 (or1_out, and4_out, and5_out);

   or2$
     or2 (or2_out, or0_out, or1_out);
   and2$
     and6 (and6_out, offset[3], or2_out);

   // cross page
   and4$
     and7 (and7_out, offset[11], offset[10], offset[9], offset[8]),
     and8 (and8_out, offset[7], offset[6], offset[5], offset[4]);
   and3$
     and9 (and9_out, and7_out, and8_out, offset[3]);
   and2$
     and10 (and10_out, and9_out, or2_out);

   assign cross_page = and10_out;
   assign cross_cl = and6_out;

endmodule // cross_boundary_detector
