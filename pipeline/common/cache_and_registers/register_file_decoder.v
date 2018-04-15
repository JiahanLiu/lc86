module register_file_decoder (
    input [2:0] write_id,
    input [1:0] write_size,
    output [7:0] write_hh,
    output [7:0] write_hl,
    output [7:0] write_lh,
    output [7:0] write_ll,
    output sh
);

wire out1a, out2a, out4a, out5a, out7a, out8a, out10a, out11a;
wire out13a, out14a, out16a, out17a, out19a, out20a, out22a, out23a;
wire out1h, out2h, out3h, out4h, out5h, out6h, out7h, out8h, out9h;
wire out10h, out11h, out12h, out13h, out14h, out15h, out16h, out17h;
wire out18h, out19h, out20h, out21h, out22h, out23h, out24h, out25h;
wire out26h, out27h, out28h, out29h, out30h, out31h, out32h, out33h;
wire out34h, out35h, out36h, out37h, out38h, out39h, out40h, out50h;
wire out51h, out52h;
wire out1l, out2l, out3l, out4l, out5l, out6l, out7l, out8l, out9l;
wire out10l, out11l, out12l, out13l, out14l, out15l, out16l;
wire out1n, out2n, out3n, out4n, out5n, out6n, out7n, out8n, out9n, out10n, out11n, out12n;

inv1$ inv1 (write_size0_b, write_size[0]);
inv1$ inv2 (write_size1_b, write_size[1]);
inv1$ inv3 (write_id2_b, write_id[2]);
inv1$ inv4 (write_id1_b, write_id[1]);
inv1$ inv5 (write_id0_b, write_id[0]);

assign write_size1 = write_size[1];
assign write_size0 = write_size[0];
assign write_id2 = write_id[2];
assign write_id1 = write_id[1];
assign write_id0 = write_id[0];

// Shift the [7:0] to [15:8] for writing to the AH
// sh = (write_id2 &write_id1 &write_id0 &!write_size1 &!write_size0) | (write_id2 &write_id1
//      &!write_id0 &!write_size1 &!write_size0) | (write_id2 &!write_id1 &write_id0 &!write_size1
//      &!write_size0) | (write_id2 &!write_id1 &!write_id0 &!write_size1 &!write_size0);
and3$ and1n (out1n, write_id2, write_id1, write_id0);
and2$ and2n (out2n, write_size1_b, write_size0_b);
and2$ and3n (out3n, out1n, out2n);

and3$ and4n (out4n, write_id2, write_id1, write_id0_b);
and2$ and5n (out5n, write_size1_b, write_size0_b);
and2$ and6n (out6n, out4n, out5n);

and3$ and7n (out7n, write_id2, write_id1_b, write_id0);
and2$ and8n (out8n, write_size1_b, write_size0_b);
and2$ and9n (out9n, out7n, out8n);

and3$ and10n (out10n, write_id2, write_id1_b, write_id0_b);
and2$ and11n (out11n, write_size1_b, write_size0_b);
and2$ and12n (out12n, out10n, out11n);

or4$ or1n (sh, out3n, out6n, out9n, out12n);

//Write_en for reg[31:24]
// whh7 = (write_id2 &write_id1 &write_id0 &write_size1 &!write_size0);
and3$ and1 (out1a, write_id2, write_id1, write_id0);
and2$ and2 (out2a, write_size1, write_size0_b);
and2$ and3 (write_hh[7], out1a, out2a);

// whh6 = (write_id2 &write_id1 &!write_id0 &write_size1 &!write_size0);
and3$ and4 (out4a, write_id2, write_id1, write_id0_b);
and2$ and5 (out5a, write_size1, write_size0_b);
and2$ and6 (write_hh[6], out4a, out5a);

// whh5 = (write_id2 &!write_id1 &write_id0 &write_size1 &!write_size0);
and3$ and7 (out7a, write_id2, write_id1_b, write_id0);
and2$ and8 (out8a, write_size1, write_size0_b);
and2$ and9 (write_hh[5], out7a, out8a);

// whh4 = (write_id2 &!write_id1 &!write_id0 &write_size1 &!write_size0);
and3$ and10 (out10a, write_id2, write_id1_b, write_id0_b);
and2$ and11 (out11a, write_size1, write_size0_b);
and2$ and12 (write_hh[4], out10a, out11a);

// whh3 = (!write_id2 &write_id1 &write_id0 &write_size1 &!write_size0);
and3$ and13 (out13a, write_id2_b, write_id1, write_id0);
and2$ and14 (out14a, write_size1, write_size0_b);
and2$ and15 (write_hh[3], out13a, out14a);

// whh2 = (!write_id2 &write_id1 &!write_id0 &write_size1 &!write_size0);
and3$ and16 (out16a, write_id2_b, write_id1, write_id0_b);
and2$ and17 (out17a, write_size1, write_size0_b);
and2$ and18 (write_hh[2], out16a, out17a);

// whh1 = (!write_id2 &!write_id1 &write_id0 &write_size1 &!write_size0);
and3$ and19 (out19a, write_id2_b, write_id1_b, write_id0);
and2$ and20 (out20a, write_size1, write_size0_b);
and2$ and21 (write_hh[1], out19a, out20a);

// whh0 = (!write_id2 &!write_id1 &!write_id0 &write_size1 &!write_size0);
and3$ and22 (out22a, write_id2_b, write_id1_b, write_id0_b);
and2$ and23 (out23a, write_size1, write_size0_b);
and2$ and24 (write_hh[0], out22a, out23a);


// Write_en for reg[23:16]
assign write_hl[7:0] = write_hh[7:0];


// Write_en for reg[15:8]
// wlh7 = (write_id2 &write_id1 &write_id0 &!write_size1 &write_size0) | (write_id2
//     &write_id1 &write_id0 &write_size1 &!write_size0);
and3$ and1h (out1h, write_id2, write_id1, write_id0);
and2$ and2h (out2h, write_size1_b, write_size0);
and2$ and3h (out3h, out1h, out2h);

and2$ and4h (out4h, write_size1, write_size0_b);
and2$ and5h (out5h, out1h, out4h);
or2$ or1 (write_lh[7], out3h, out5h);

//wlh6 = (write_id2 &write_id1 &!write_id0 &!write_size1 &write_size0) | (write_id2
//     &write_id1 &!write_id0 &write_size1 &!write_size0);
and3$ and6h (out6h, write_id2, write_id1, write_id0_b);
and2$ and7h (out7h, write_size1_b, write_size0);
and2$ and8h (out8h, out6h, out7h);

and2$ and9h (out9h, write_size1, write_size0_b);
and2$ and10h (out10h, out6h, out9h);
or2$ or2 (write_lh[6], out8h, out10h);

//wlh5 = (write_id2 &!write_id1 &write_id0 &!write_size1 &write_size0) | (write_id2
//     &!write_id1 &write_id0 &write_size1 &!write_size0);
and3$ and11h (out11h, write_id2, write_id1_b, write_id0);
and2$ and12h (out12h, write_size1_b, write_size0);
and2$ and13h (out13h, out11h, out12h);

and2$ and14h (out14h, write_size1, write_size0_b);
and2$ and15h (out15h, out11h, out14h);
or2$ or3 (write_lh[5], out13h, out15h);

//wlh4 = (write_id2 &!write_id1 &!write_id0 &!write_size1 &write_size0) | (write_id2
//     &!write_id1 &!write_id0 &write_size1 &!write_size0);
and3$ and16h (out16h, write_id2, write_id1_b, write_id0_b);
and2$ and17h (out17h, write_size1_b, write_size0);
and2$ and18h (out18h, out16h, out17h);

and2$ and19h (out19h, write_size1, write_size0_b);
and2$ and20h (out20h, out16h, out19h);
or2$ or4 (write_lh[4], out18h, out20h);

//wlh3 = (!write_id2 &write_id1 &write_id0 &!write_size1 &write_size0) | (!write_id2
//     &write_id1 &write_id0 &write_size1 &!write_size0) | (write_id2 &write_id1 &write_id0
//     &!write_size1 &!write_size0);
and3$ and21h (out21h, write_id2_b, write_id1, write_id0);
and2$ and22h (out22h, write_size1_b, write_size0);
and2$ and23h (out23h, out21h, out22h);

and2$ and24h (out24h, write_size1, write_size0_b);
and2$ and25h (out25h, out21h, out24h);

and3$ and26h (out26h, write_id2, write_id1, write_id0);
and2$ and27h (out27h, write_size1_b, write_size0_b);
and2$ and28h (out28h, out26h, out27h);

or3$ or5 (write_lh[3], out23h, out25h, out28h);

//wlh2 = (!write_id2 &write_id1 &!write_id0 &!write_size1 &write_size0) | (!write_id2
//     &write_id1 &!write_id0 &write_size1 &!write_size0) | (write_id2 &write_id1 &!write_id0
//     &!write_size1 &!write_size0);
and3$ and29h (out29h, write_id2_b, write_id1, write_id0_b);
and2$ and30h (out30h, write_size1_b, write_size0);
and2$ and31h (out31h, out29h, out30h);

and2$ and32h (out32h, write_size1, write_size0_b);
and2$ and33h (out33h, out29h, out32h);

and3$ and34h (out34h, write_id2, write_id1, write_id0_b);
and2$ and35h (out35h, write_size1_b, write_size0_b);
and2$ and36h (out36h, out34h, out35h);

or3$ or6 (write_lh[2], out31h, out33h, out36h);

//wlh1 = (!write_id2 &!write_id1 &write_id0 &!write_size1 &write_size0) | (!write_id2
//     &!write_id1 &write_id0 &write_size1 &!write_size0) | (write_id2 &!write_id1 &write_id0
//     &!write_size1 &!write_size0);
and3$ and37h (out37h, write_id2_b, write_id1_b, write_id0);
and2$ and38h (out38h, write_size1_b, write_size0);
and2$ and39h (out39h, out37h, out38h);

and2$ and40h (out40h, write_size1, write_size0_b);
and2$ and41h (out41h, out37h, out40h);

and3$ and42h (out42h, write_id2, write_id1_b, write_id0);
and2$ and43h (out43h, write_size1_b, write_size0_b);
and2$ and44h (out44h, out42h, out43h);

or3$ or7 (write_lh[1], out39h, out41h, out44h);

//wlh0 = (!write_id2 &!write_id1 &!write_id0 &!write_size1 &write_size0) | (!write_id2
//     &!write_id1 &!write_id0 &write_size1 &!write_size0) | (write_id2 &!write_id1
//     &!write_id0 &!write_size1 &!write_size0);
and3$ and45h (out45h, write_id2_b, write_id1_b, write_id0_b);
and2$ and46h (out46h, write_size1_b, write_size0);
and2$ and47h (out47h, out45h, out46h);

and2$ and48h (out48h, write_size1, write_size0_b);
and2$ and49h (out49h, out45h, out48h);

and3$ and50h (out50h, write_id2, write_id1_b, write_id0_b);
and2$ and51h (out51h, write_size1_b, write_size0_b);
and2$ and52h (out52h, out50h, out51h);

or3$ or8 (write_lh[0], out47h, out49h, out52h);


// Write_en bits for reg[7:0]
assign write_ll[7:4] = write_lh[7:4];

// wll3 = (!write_id2 &write_id1 &write_id0 &!write_size1 &write_size0) | (!write_id2
//      &write_id1 &write_id0 &!write_size0);
and3$ and1l (out1l, write_id2_b, write_id1, write_id0);
and2$ and2l (out2l, write_size1_b, write_size0);
and2$ and3l (out3l, out1l, out2l);

and2$ and4l (out4l, out1l, write_size0_b);
or2$ or1l (write_ll[3], out3l, out4l);

// wll2 = (!write_id2 &write_id1 &!write_id0 &!write_size1 &write_size0) | (!write_id2
//      &write_id1 &!write_id0 &!write_size0);
and3$ and5l (out5l, write_id2_b, write_id1, write_id0_b);
and2$ and6l (out6l, write_size1_b, write_size0);
and2$ and7l (out7l, out5l, out6l);

and2$ and8l (out8l, out5l, write_size0_b);
or2$ or2l (write_ll[2], out7l, out8l);
 
// wll1 = (!write_id2 &!write_id1 &write_id0 &!write_size1 &write_size0) | (!write_id2
//      &!write_id1 &write_id0 &!write_size0);
and3$ and9l (out9l, write_id2_b, write_id1_b, write_id0);
and2$ and10l (out10l, write_size1_b, write_size0);
and2$ and11l (out11l, out9l, out10l);

and2$ and12l (out12l, out9l, write_size0_b);
or2$ or3l (write_ll[1], out11l, out12l);
 
// wll0 = (!write_id2 &!write_id1 &!write_id0 &!write_size1 &write_size0) | (!write_id2
//      &!write_id1 &!write_id0 &!write_size0);
and3$ and13l (out13l, write_id2_b, write_id1_b, write_id0_b);
and2$ and14l (out14l, write_size1_b, write_size0);
and2$ and15l (out15l, out13l, out14l);

and2$ and16l (out16l, out13l, write_size0_b);
or2$ or4l (write_ll[0], out15l, out16l);

endmodule
