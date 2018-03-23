// Full_adder with propagate and generate bits
// Gate delay: p=3, g=2, s=6

module full_adder (sum, p, g, a, b, cin);
    input a, b, cin;
    output sum, p, g;

    wire w1;

    xor_n xor1 (p, a, b),
          xor2 (sum, p, cin);

    nand2$ nand1 (w1, a, b),
           nand2 (g, w1, w1);

endmodule
