// 4-bit carry look ahead adder
// Worst case delay -> 12 nand gate for SUM

module carry_lookahead (sum, p, g, cout, a, b, cin);
    input cin;
    input [3:0] a, b;
    output [3:0] sum;
    output p, g, cout;

    wire p0, p1, p2, p3, g0, g1, g2, g3, c1, c2, c3;
    wire g0_b, g1_b, g2_b, g3_b;
    wire w1, w2, w3, w4, w5, w6, w7, w8, w9, w10;
    wire w11, w12, w13, w14, w15, w16, w17, w18, w19;

    full_adder f0 (sum[0], p0, g0, a[0], b[0], cin);
    full_adder f1 (sum[1], p1, g1, a[1], b[1], c1);
    full_adder f2 (sum[2], p2, g2, a[2], b[2], c2);
    full_adder f3 (sum[3], p3, g3, a[3], b[3], c3);

    inv1$ inv1 (g0_b, g0),
           inv2 (g1_b, g1),
           inv3 (g2_b, g2),
           inv4 (g3_b, g3);

    // Calculate the carry bits
    nand2$ nand1 (w1, p0, cin),
           nand2 (c1, w1, g0_b),

           nand3 (w2, c1, p1),
           nand4 (c2, w2, g1_b),

           nand5 (w3, c2, p2),
           nand6 (c3, w3, g2_b),

           nand7 (w4, c3, p3),
           nand8 (cout, w4, g3_b);

    // Calculate the PG bit
    nand2$ nand9 (w5, p0, p1),
          inv5 (w6, w5, w5),

          nand10 (w7, p2, p3),
          inv6 (w8, w7, w7),

          nand11 (w9, w6, w8),
          nand12 (p, w9, w9);

    // Calculate the GG bit
    nand2$ nand13 (w10, g2, p3),
          nand14 (w11, w10, g3_b),
          inv7 (w12, w11, w11),

          nand15 (w13, p1, p2),
          inv8 (w14, w13, w13),
          nand16 (w15, w14, g0),

          nand17 (w16, g1, p2),

          nand18 (w17, w15, w16),
          nand19 (w18, w17, p3),

          nand20 (g, w18, w12);

endmodule

module full_adder (sum, p, g, a, b, cin);
    input a, b, cin;
    output sum, p, g;

    wire w1;

    xor2$ xor1 (p, a, b),
          xor2 (sum, p, cin);

    nand2$ nand1 (w1, a, b),
           nand2 (g, w1, w1);

endmodule
