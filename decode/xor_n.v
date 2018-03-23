// xor gate with 2-input NAND gates
// Gate delay -> 3

module xor_n (out, in0, in1);
    input in0, in1;
    output out;

    wire w1, w2, w3;

    nand2$ nand1 (w1, in0, in1),

           nand2 (w2, in0, w1),
           nand3 (w3, in1, w1),

           nand4 (out, w2, w3);

endmodule
