module reg_scoreboard_generator (
   input [2:0] REG,

   output [7:0] SCOREBOARD,
   output [7:0] SCOREBOARD_BAR
);

   decoder3_8$ u_reg_scoreboard (REG, SCOREBOARD, SCOREBOARD_BAR);

endmodule

module gpr_scoreboard_generator (
   input [2:0] REG,
   input [2:0] REG_BAR,
   input [1:0] SIZE,
   input [1:0] SIZE_BAR,

   output [23:0] GPR_SCOREBOARD
);

   wire [2:0] ID7, ID6, ID5, ID4, ID3, ID2, ID1, ID0;

   wire and0_out, and1_out, and2_out, and3_out,
        and4_out, and5_out, and6_out, and7_out,
        and8_out, and9_out, and10_out, and11_out,
        and12_out, and13_out, and14_out, and15_out,
        and16_out, and17_out, and18_out, and19_out,
        and20_out, and21_out, and22_out, and23_out,
        and24_out, and25_out, and26_out, and27_out,
        and28_out, and29_out, and30_out, and31_out,
        and32_out, and33_out, and34_out, and35_out,
        and36_out, and37_out, and38_out, and39_out,
        and40_out, and41_out;
   wire or0_out, or1_out, or2_out, or3_out, or4_out,
        or5_out, or6_out, or7_out, or8_out, or9_out,
        or10_out, or11_out;

   // SRID7[2:0]
   and3$ and0 (and0_out, REG[2], REG[1], REG[0]); 
   and2$ and1 (and1_out, SIZE[1], SIZE_BAR[0]);
   and2$ and2 (and2_out, and0_out, and1_out);
   assign ID7[2] = and2_out;

   and2$ and3 (and3_out, SIZE_BAR[1], SIZE[0]);
   and2$ and4 (and4_out, and0_out, and3_out);
   or2$ or0 (or0_out, and4_out, and2_out);
   assign ID7[1] = or0_out;
   assign ID7[0] = or0_out;

   and3$ and5 (and5_out, REG[2], REG[1], REG_BAR[0]);
   and2$ and6 (and6_out, and5_out, and1_out);
   assign ID6[2] = and6_out;

   and2$ and7 (and7_out, and5_out, and3_out);
   or2$ or1 (or1_out, and7_out, and6_out);
   assign ID6[1] = or1_out;
   assign ID6[0] = or1_out;

   and3$ and8 (and8_out, REG[2], REG_BAR[1], REG[0]);
   and2$ and9 (and9_out, and8_out, and1_out);
   assign ID5[2] = and9_out;

   and2$ and10 (and10_out, and8_out, and3_out);
   or2$ or2 (or2_out, and10_out, and9_out);
   assign ID5[1] = or2_out;
   assign ID5[0] = or2_out;

   and3$ and11 (and11_out, REG[2], REG_BAR[1], REG_BAR[0]);
   and2$ and12 (and12_out, and11_out, and1_out);
   assign ID4[2] = and12_out;

   and2$ and13 (and13_out, and11_out, and3_out);
   or2$ or3 (or3_out, and13_out, and12_out);
   assign ID4[1] = or3_out;
   assign ID4[0] = or3_out;

   and3$ and14 (and14_out, REG_BAR[2], REG[1], REG[0]);
   and2$ and15 (and15_out, SIZE[1], SIZE_BAR[0]);
   and2$ and16 (and16_out, and14_out, and15_out);
   assign ID3[2] = and16_out;

   and2$ and17 (and17_out, SIZE_BAR[1], SIZE[0]);
   and2$ and18 (and18_out, and14_out, and17_out);
   and2$ and19 (and19_out, SIZE_BAR[1], SIZE_BAR[0]);
   and2$ and20 (and20_out, and0_out, and19_out);
   or3$ or4 (or4_out, and18_out, and16_out, and20_out);
   assign ID3[1] = or4_out;

   and2$ and21 (and21_out, and14_out, and17_out);
   and2$ and22 (and22_out, and14_out, SIZE_BAR[0]);
   or2$ or5 (or5_out, and21_out, and22_out);
   assign ID3[0] = or5_out;

   and3$ and23 (and23_out, REG_BAR[2], REG[1], REG_BAR[0]);
   and2$ and24 (and24_out, and23_out, and15_out);
   assign ID2[2] = and24_out;

   and2$ and25 (and25_out, and23_out, and17_out);
   and2$ and26 (and26_out, and5_out, and19_out);
   or3$ or6 (or6_out, and25_out, and24_out, and26_out);
   assign ID2[1] = or6_out;

   and2$ and27 (and27_out, and23_out, and17_out);
   and2$ and28 (and28_out, and23_out, SIZE_BAR[0]);
   or2$ or7 (or7_out, and27_out, and28_out);
   assign ID2[0] = or7_out;

   and3$ and29 (and29_out, REG_BAR[2], REG_BAR[1], REG[0]);
   and2$ and30 (and30_out, SIZE[1], SIZE_BAR[0]);
   and2$ and31 (and31_out, and29_out, and30_out);
   assign ID1[2] = and31_out;

   and2$ and32 (and32_out, SIZE_BAR[1], SIZE[0]);
   and2$ and33 (and33_out, and29_out, and32_out);
   and2$ and34 (and34_out, and8_out, and19_out);
   or3$ or8 (or8_out, and33_out, and31_out, and34_out);
   assign ID1[1] = or8_out;

   and2$ and35 (and35_out, and29_out, SIZE_BAR[0]);
   or2$ or9 (or9_out, and33_out, and35_out);
   assign ID1[0] = or9_out;

   and3$ and36 (and36_out, REG_BAR[2], REG_BAR[1], REG_BAR[0]);
   and2$ and37 (and37_out, and36_out, and30_out);
   assign ID0[2] = and37_out;

   and2$ and38 (and38_out, and36_out, and32_out);
   and2$ and39 (and39_out, and11_out, and19_out);
   or3$ or10 (or10_out, and38_out, and37_out, and39_out);
   assign ID0[1] = or10_out;

   and2$ and40 (and40_out, and36_out, and32_out);
   and2$ and41 (and41_out, and36_out, SIZE_BAR[0]);
   or2$ or11 (or11_out, and40_out, and41_out);
   assign ID0[0] = or11_out;

   assign GPR_SCOREBOARD = {ID7, ID6, ID5, ID4, ID3, ID2, ID1, ID0};

endmodule

