module comp20 (out, out_bar, in0, in1);
   input [19:0] in0, in1;

   // outputs EQ or NEQ
   output out, out_bar;

   wire [19:0] xnor_out;
   wire and0_out, and1_out, and2_out, and3_out, and4_out, and5_out, and6_out;

   xnor2$ xnor0 [19:0] (xnor_out, in0, in1);
   and4$
      and0 (and0_out, xnor_out[3], xnor_out[2], xnor_out[1], xnor_out[0]),
      and1 (and1_out, xnor_out[7], xnor_out[6], xnor_out[5], xnor_out[4]),
      and2 (and2_out, xnor_out[11], xnor_out[10], xnor_out[9], xnor_out[8]),
      and3 (and3_out, xnor_out[15], xnor_out[14], xnor_out[13], xnor_out[12]),
      and4 (and4_out, xnor_out[19], xnor_out[18], xnor_out[17], xnor_out[16]);

   and3$
      and5 (and5_out, and0_out, and1_out, and2_out);
   and2$
      and6 (and6_out, and3_out, and4_out),
      and7 (out, and5_out, and6_out);

   nand2$ nand0 (out_bar, and5_out, and6_out);

endmodule

module mux8_32 (
   output [31:0] out,

   input [31:0] in0, in1, in2, in3,
   input [31:0] in4, in5, in6, in7,

   input [2:0] s
);

   wire [15:0] mux0_out, mux1_out, mux2_out, mux3_out;

   mux4_16$
      mux0 (mux0_out, in0[31:16], in1[31:16], in2[31:16], in3[31:16], s[0], s[1]),
      mux1 (mux1_out, in4[31:16], in5[31:16], in6[31:16], in7[31:16], s[0], s[1]),

      mux2 (mux2_out, in0[15:0], in1[15:0], in2[15:0], in3[15:0], s[0], s[1]),
      mux3 (mux3_out, in4[15:0], in5[15:0], in6[15:0], in7[15:0], s[0], s[1]);

   mux2_16$
      mux4 (out[31:16], mux0_out, mux1_out, s[2]),
      mux5 (out[15:0], mux2_out, mux3_out, s[2]);

endmodule

module mux8_64 (
   output [63:0] out,

   input [63:0] in0, in1, in2, in3,
   input [63:0] in4, in5, in6, in7,

   input [2:0] s
);

   mux8_32
      mux0 (out[63:32], in0[63:32], in1[63:32], in2[63:32], in3[63:32], in4[63:32], in5[63:32], in6[63:32], in7[63:32], s),
      mux1 (out[31:0], in0[31:0], in1[31:0], in2[31:0], in3[31:0], in4[31:0], in5[31:0], in6[31:0], in7[31:0], s);

endmodule

module tlb (
   input [19:0] VPN1, VPN1_END,
   input [19:0] VPN2, VPN2_END,

   output [23:0] VPN1_ENTRY, VPN1_END_ENTRY,
   output [23:0] VPN2_ENTRY, VPN2_END_ENTRY,

   output VPN1_MATCH, VPN1_END_MATCH,
   output VPN2_MATCH, VPN2_END_MATCH
);

/*
Virtual Page	Physical Page	Valid	Present	R/W PCD
20'h00000	20'h00000	1	1	0   0
20'h02000	20'h00002	1	1	1   0
20'h04000	20'h00005	1	1	1   0
20'h0b000	20'h00004	1	1	1   0
20'h0c000	20'h00007	1	1	1   0
20'h0a000	20'h00005	1	1	1   0
*/
   reg [43:0] ENTRY [0:7];

   wire [7:0] u_comp_tlb_vpn1_out, u_comp_tlb_vpn1_end_out;
   wire [7:0] u_comp_tlb_vpn2_out, u_comp_tlb_vpn2_end_out;

   wire [2:0] u_pencoder_vpn1_out, u_pencoder_vpn1_end_out;
   wire [2:0] u_pencoder_vpn2_out, u_pencoder_vpn2_end_out;

   wire [31:0] mux0_out, mux1_out, mux2_out, mux3_out;

`define TLB_VPN(entry) ENTRY[``entry``][43:24]
`define TLB_PTE(entry) {8'h00, ENTRY[``entry``][23:0]}
/*
`define TLB_RPN(entry) ENTRY[``entry``][23:4]
`define TLB_V(entry) ENTRY[``entry``][3]
`define TLB_P(entry) ENTRY[``entry``][2]
`define TLB_R(entry) ENTRY[``entry``][1]
`define TLB_PCD(entry) ENTRY[``entry``][0]
*/
/*
`define VPN1_END {VPN1[19:1], vpn1_0_bar}
`define VPN2_END {VPN2[19:1], vpn2_0_bar}

   inv1$
      inv0 (vpn1_0_bar, VPN1[0]),
      inv1 (vpn2_0_bar, VPN2[0]);
*/
   comp20
      u_comp_tlb0_vpn1 (u_comp_tlb_vpn1_out[0], , VPN1, `TLB_VPN(0)),
      u_comp_tlb1_vpn1 (u_comp_tlb_vpn1_out[1], , VPN1, `TLB_VPN(1)),
      u_comp_tlb2_vpn1 (u_comp_tlb_vpn1_out[2], , VPN1, `TLB_VPN(2)),
      u_comp_tlb3_vpn1 (u_comp_tlb_vpn1_out[3], , VPN1, `TLB_VPN(3)),
      u_comp_tlb4_vpn1 (u_comp_tlb_vpn1_out[4], , VPN1, `TLB_VPN(4)),
      u_comp_tlb5_vpn1 (u_comp_tlb_vpn1_out[5], , VPN1, `TLB_VPN(5)),
      u_comp_tlb6_vpn1 (u_comp_tlb_vpn1_out[6], , VPN1, `TLB_VPN(6)),
      u_comp_tlb7_vpn1 (u_comp_tlb_vpn1_out[7], , VPN1, `TLB_VPN(7));

   comp20
      u_comp_tlb0_vpn1_end (u_comp_tlb_vpn1_end_out[0], , VPN1_END, `TLB_VPN(0)),
      u_comp_tlb1_vpn1_end (u_comp_tlb_vpn1_end_out[1], , VPN1_END, `TLB_VPN(1)),
      u_comp_tlb2_vpn1_end (u_comp_tlb_vpn1_end_out[2], , VPN1_END, `TLB_VPN(2)),
      u_comp_tlb3_vpn1_end (u_comp_tlb_vpn1_end_out[3], , VPN1_END, `TLB_VPN(3)),
      u_comp_tlb4_vpn1_end (u_comp_tlb_vpn1_end_out[4], , VPN1_END, `TLB_VPN(4)),
      u_comp_tlb5_vpn1_end (u_comp_tlb_vpn1_end_out[5], , VPN1_END, `TLB_VPN(5)),
      u_comp_tlb6_vpn1_end (u_comp_tlb_vpn1_end_out[6], , VPN1_END, `TLB_VPN(6)),
      u_comp_tlb7_vpn1_end (u_comp_tlb_vpn1_end_out[7], , VPN1_END, `TLB_VPN(7));

   comp20
      u_comp_tlb0_vpn2 (u_comp_tlb_vpn2_out[0], , VPN2, `TLB_VPN(0)),
      u_comp_tlb1_vpn2 (u_comp_tlb_vpn2_out[1], , VPN2, `TLB_VPN(1)),
      u_comp_tlb2_vpn2 (u_comp_tlb_vpn2_out[2], , VPN2, `TLB_VPN(2)),
      u_comp_tlb3_vpn2 (u_comp_tlb_vpn2_out[3], , VPN2, `TLB_VPN(3)),
      u_comp_tlb4_vpn2 (u_comp_tlb_vpn2_out[4], , VPN2, `TLB_VPN(4)),
      u_comp_tlb5_vpn2 (u_comp_tlb_vpn2_out[5], , VPN2, `TLB_VPN(5)),
      u_comp_tlb6_vpn2 (u_comp_tlb_vpn2_out[6], , VPN2, `TLB_VPN(6)),
      u_comp_tlb7_vpn2 (u_comp_tlb_vpn2_out[7], , VPN2, `TLB_VPN(7));

   comp20
      u_comp_tlb0_vpn2_end (u_comp_tlb_vpn2_end_out[0], , VPN2_END, `TLB_VPN(0)),
      u_comp_tlb1_vpn2_end (u_comp_tlb_vpn2_end_out[1], , VPN2_END, `TLB_VPN(1)),
      u_comp_tlb2_vpn2_end (u_comp_tlb_vpn2_end_out[2], , VPN2_END, `TLB_VPN(2)),
      u_comp_tlb3_vpn2_end (u_comp_tlb_vpn2_end_out[3], , VPN2_END, `TLB_VPN(3)),
      u_comp_tlb4_vpn2_end (u_comp_tlb_vpn2_end_out[4], , VPN2_END, `TLB_VPN(4)),
      u_comp_tlb5_vpn2_end (u_comp_tlb_vpn2_end_out[5], , VPN2_END, `TLB_VPN(5)),
      u_comp_tlb6_vpn2_end (u_comp_tlb_vpn2_end_out[6], , VPN2_END, `TLB_VPN(6)),
      u_comp_tlb7_vpn2_end (u_comp_tlb_vpn2_end_out[7], , VPN2_END, `TLB_VPN(7));

   pencoder8_3v$
      u_pencoder_vpn1 (1'b0, u_comp_tlb_vpn1_out, u_pencoder_vpn1_out, VPN1_MATCH),
      u_pencoder_vpn1_end (1'b0, u_comp_tlb_vpn1_end_out, u_pencoder_vpn1_end_out, VPN1_END_MATCH),
      u_pencoder_vpn2 (1'b0, u_comp_tlb_vpn2_out, u_pencoder_vpn2_out, VPN2_MATCH),
      u_pencoder_vpn2_end (1'b0, u_comp_tlb_vpn2_end_out, u_pencoder_vpn2_end_out, VPN2_END_MATCH);

   mux8_32
      mux0 (mux0_out, `TLB_PTE(0), `TLB_PTE(1), `TLB_PTE(2), `TLB_PTE(3), `TLB_PTE(4), `TLB_PTE(5), `TLB_PTE(6), `TLB_PTE(7), u_pencoder_vpn1_out),
      mux1 (mux1_out, `TLB_PTE(0), `TLB_PTE(1), `TLB_PTE(2), `TLB_PTE(3), `TLB_PTE(4), `TLB_PTE(5), `TLB_PTE(6), `TLB_PTE(7), u_pencoder_vpn1_end_out),
      mux2 (mux2_out, `TLB_PTE(0), `TLB_PTE(1), `TLB_PTE(2), `TLB_PTE(3), `TLB_PTE(4), `TLB_PTE(5), `TLB_PTE(6), `TLB_PTE(7), u_pencoder_vpn2_out),
      mux3 (mux3_out, `TLB_PTE(0), `TLB_PTE(1), `TLB_PTE(2), `TLB_PTE(3), `TLB_PTE(4), `TLB_PTE(5), `TLB_PTE(6), `TLB_PTE(7), u_pencoder_vpn2_end_out);

   assign VPN1_ENTRY = mux0_out[23:0];
   assign VPN1_END_ENTRY = mux1_out[23:0];
   assign VPN2_ENTRY = mux2_out[23:0];
   assign VPN2_END_ENTRY = mux3_out[23:0];

endmodule

