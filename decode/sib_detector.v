module sib_disp_detector (
    input [7:0] modrm,
    output disp_present,
    output disp_size,
    output sib_present
);

wire modrm7_b, modrm6_b, modrm1_b, modrm0_b;
wire out1a, out2a, out3a, out4a, out5a;

inv1$ inv1 (modrm7_b, modrm[7]);
inv1$ inv2 (modrm6_b, modrm[6]);
inv1$ inv4 (modrm1_b, modrm[1]);
inv1$ inv5 (modrm0_b, modrm[0]);

// Logic for sib_present
// sib_present = (!mod7 &rm2 &!rm1 &!rm0) | (!mod6 &rm2 &!rm1 &!rm0);
and4$ and1 (out1a, modrm7_b, modrm[2], modrm1_b, modrm0_b);
and4$ and2 (out2a, modrm6_b, modrm[2], modrm1_b, modrm0_b);
or2$ or1 (sib_present, out1a, out2a);

// disp_present = (!mod6 &rm2 &!rm1 &rm0) | (mod7 &!mod6) | (!mod7 &mod6);
and4$ and3 (out3a, modrm6_b, modrm[2], modrm1_b, modrm[0]);
and2$ and4 (out4a, modrm[7], modrm6_b);
and2$ and5 (out5a, modrm7_b, modrm[6]);
or3$ or3 (disp_present, out3a, out4a, out5a);

// size_of_disp = (!mod7 &mod6);
// size_of_disp - 0 for disp32 and disp8 
and2$ and6 (disp_size, modrm7_b, modrm[6]);

endmodule
