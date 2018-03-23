module prefix_decoder (
    input isPrefix1, isPrefix2, isPrefix3,
    input isSeg_ovrr1, isSeg_ovrr2, isSeg_ovrr3,
    output prefix_present,
    output [1:0] prefix_length,
    output [1:0] segID_sel
);

wire isPrefix_buf, isPrefix2_b;
wire outa2, outa3;

bufferH16$ buf1 (isPrefix1_buf, isPrefix1);
inv1$ inv1 (isPrefix2_b, isPrefix2);

// Logic for prefix length
// prefix_present = p1; 
// pl1 = (p1&p2);
// pl0 = (p1&p3) | (p1&!p2);
assign prefix_present = isPrefix1_buf;

and2$ and1 (prefix_length[1], isPrefix1_buf, isPrefix2);

and2$ and2 (outa2, isPrefix1_buf, isPrefix3);
and2$ and3 (outa3, isPrefix1_buf, isPrefix2_b);
or2$ or1 (prefix_length[0], outa2, outa3);

// Logic for segID_sel
// segID_sel1 = (isp1 &isp2 &isp3 &seg_ovr3);
// segID_sel0 = (isp1 &isp2 &seg_ovr2);
// segID_sel  SegID from byte
// 00           1
// 01           2
// 10           3
and4$ and4 (segID_sel[1], isPrefix1_buf, isPrefix2, isPrefix3, isSeg_ovrr3);
and3$ and5 (segID_sel[0], isPrefix1_buf, isPrefix2, isSeg_ovrr2);

endmodule
