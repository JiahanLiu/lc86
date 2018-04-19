module reg128e (
   input CLK,
   input [127:0] Din,

   output [127:0] Q,
   output [127:0] QBAR,

   input CLR,
   input PRE,
   input en);

reg64e$ low(CLK, Din[63:0], Q[63:0], QBAR[63:0], CLR, PRE, en);
reg64e$ high(CLK, Din[127:64], Q[127:64], QBAR[127:64], CLR, PRE, en);

endmodule

module sll128 (out, in, cnt);
   input [127:0] in;
   input [6:0] cnt;

   output [127:0] out;

   wire [127:0] ind0, ind1, ind2, ind3, ind4, ind5;

   mux2$
     mux0[127:0] (ind0, in, {in[63:0], 64'b0}, cnt[6]),
     mux1[127:0] (ind1, ind0, {ind0[95:0], 32'b0}, cnt[5]),
     mux2[127:0] (ind2, ind1, {ind1[111:0], 16'b0}, cnt[4]),
     mux3[127:0] (ind3, ind2, {ind2[119:0], 8'b0}, cnt[3]),
     mux4[127:0] (ind4, ind3, {ind3[123:0], 4'b0}, cnt[2]),
     mux5[127:0] (ind5, ind4, {ind4[125:0], 2'b0}, cnt[1]),
     mux6[127:0] (out, ind5, {ind5[126:0], 1'b0}, cnt[0]);

endmodule // sll128

module ifu_mask_detector (
   input [3:0] SIZE,

   output [127:0] MASK
);
/*
mask[15] = ;
mask[14] = (size[3]&size[2]&size[1]&size[0]);
mask[13] = (size[3]&size[2]&size[1]);
mask[12] = (size[3]&size[2]&size[0]) | (size[3]&size[2]&size[1]);
mask[11] = (size[3]&size[2]);
mask[10] = (size[3]&size[1]&size[0]) | (size[3]&size[2]);
mask[9] = (size[3]&size[1]) | (size[3]&size[2]);
mask[8] = (size[3]&size[0]) | (size[3]&size[1]) | (size[3]&size[2]);
mask[7] = (size[3]);
mask[6] = (size[2]&size[1]&size[0]) | (size[3]);
mask[5] = (size[2]&size[1]) | (size[3]);
mask[4] = (size[2]&size[0]) | (size[2]&size[1]) | (size[3]);
mask[3] = (size[2]) | (size[3]);
mask[2] = (size[1]&size[0]) | (size[2]) | (size[3]);
mask[1] = (size[1]) | (size[2]) | (size[3]);
mask[0] = (size[0]) | (size[1]) | (size[2]) | (size[3]);
*/
   wire [14:0] bitmask;

   // mask[14]
   and4$ and0 (and0_out, SIZE[3], SIZE[2], SIZE[1], SIZE[0]);
   assign bitmask[14] = and0_out;
   // mask[13]
   and3$ and1 (and1_out, SIZE[3], SIZE[2], SIZE[1]);
   assign bitmask[13] = and1_out;
   // mask[12]
   and3$ and2 (and2_out, SIZE[3], SIZE[2], SIZE[0]);
   or2$ or0 (or0_out, and1_out, and2_out);
   assign bitmask[12] = or0_out;
   // mask[11]
   and2$ and3 (and3_out, SIZE[3], SIZE[2]);
   assign bitmask[11] = and3_out;
   // mask[10]
   and3$ and4 (and4_out, SIZE[3], SIZE[1], SIZE[0]);
   or2$ or1 (or1_out, and4_out, and3_out);
   assign bitmask[10] = or1_out;
   // mask[9]
   and2$ and5 (and5_out, SIZE[3], SIZE[1]);
   or2$ or2 (or2_out, and5_out, and3_out);
   assign bitmask[9] = or2_out;
   // mask[8]
   and2$ and6 (and6_out, SIZE[3], SIZE[0]);
   or3$ or3 (or3_out, and6_out, and5_out, and3_out);
   assign bitmask[8] = or3_out;
   // mask[7] = SIZE[3]
   assign bitmask[7] = SIZE[3];
   // mask[6]
   and3$ and7 (and7_out, SIZE[2], SIZE[1], SIZE[0]);
   or2$ or4 (or4_out, and7_out, SIZE[3]);
   assign bitmask[6] = or4_out;
   // mask[5]
   and2$ and8 (and8_out, SIZE[2], SIZE[1]);
   or2$ or5 (or5_out, and8_out, SIZE[3]);
   assign bitmask[5] = or5_out;
   // mask[4]
   and2$ and9 (and9_out, SIZE[2], SIZE[0]);
   or3$ or6 (or6_out, and9_out, and8_out, SIZE[3]);
   assign bitmask[4] = or6_out;
   // mask[3]
   or2$ or7 (or7_out, SIZE[2], SIZE[3]);
   assign bitmask[3] =  or7_out;
   // mask[2]
   and2$ and10 (and10_out, SIZE[1], SIZE[0]);
   or3$ or8 (or8_out, and10_out, SIZE[2], SIZE[3]);
   assign bitmask[2] = or8_out;
   // mask[1]
   or3$ or9 (or9_out, SIZE[1], SIZE[2], SIZE[3]);
   assign bitmask[1] = or9_out;
   // mask[0]
   or4$ or10 (or10_out, SIZE[0], SIZE[1], SIZE[2], SIZE[3]);
   assign bitmask[0] = or10_out;

   wire [14:0] buffer_out;

   bufferH16$ buffer0 [14:0] (buffer_out, bitmask);

   assign MASK[127:120] = 8'b0;
   assign MASK[119:0] = {{8{buffer_out[14]}}, {8{buffer_out[13]}}, {8{buffer_out[12]}}, {8{buffer_out[11]}}, {8{buffer_out[10]}}, {8{buffer_out[9]}}, {8{buffer_out[8]}}, {8{buffer_out[7]}}, {8{buffer_out[6]}}, {8{buffer_out[5]}}, {8{buffer_out[4]}}, {8{buffer_out[3]}}, {8{buffer_out[2]}}, {8{buffer_out[1]}}, {8{buffer_out[0]}}};

endmodule

module cross_icache_line_size (
   input [3:0] OFFSET,

   output [4:0] SIZE1, SIZE2
);

/*
size1[4] = (!offset[3]&!offset[2]&!offset[1]&!offset[0]);

size1[3] = (offset[3]&!offset[2]&!offset[1]&!offset[0]) | (!offset[3]
    &offset[0]) | (!offset[3]&offset[2]) | (!offset[3]&offset[1]);

size1[2] = (offset[2]&!offset[1]&!offset[0]) | (!offset[2]&offset[1]) | (
    !offset[2]&offset[0]);

size1[1] = (offset[1]&!offset[0]) | (!offset[1]&offset[0]);

size1[0] = (offset[0]);
*/
   wire [3:0] offset_bar;
   wire and0_out, and1_out, and2_out, and3_out, and4_out,
        and5_out, and6_out, and7_out, and8_out, and9_out;
   wire or0_out, or1_out, or2_out;

   inv1$ inv_offset [3:0] (offset_bar, OFFSET);

   and4$ and9 (and9_out, offset_bar[3], offset_bar[2], offset_bar[1], offset_bar[0]);

   assign SIZE1[4] = and9_out;

   and4$ and0 (and0_out, OFFSET[3], offset_bar[2], offset_bar[1], offset_bar[0]);
   and2$
      and1 (and1_out, offset_bar[3], OFFSET[0]),
      and2 (and2_out, offset_bar[3], OFFSET[2]),
      and3 (and3_out, offset_bar[3], OFFSET[1]);
   or4$ or0 (or0_out, and0_out, and1_out, and2_out, and3_out);

   assign SIZE1[3] = or0_out;

   and3$ and4 (and4_out, OFFSET[2], offset_bar[1], offset_bar[0]);
   and2$
      and5 (and5_out, offset_bar[2], OFFSET[1]),
      and6 (and6_out, offset_bar[2], OFFSET[0]);
   or3$ or1 (or1_out, and4_out, and5_out, and6_out);

   assign SIZE1[2] = or1_out;

   and2$
      and7 (and7_out, OFFSET[1], offset_bar[0]),
      and8 (and8_out, offset_bar[1], OFFSET[0]);
   or2$ or2 (or2_out, and7_out, and8_out);

   assign SIZE1[1] = or2_out;
   assign SIZE1[0] = OFFSET[0];

   assign SIZE2[4:0] = {1'b0, OFFSET[3:0]};

endmodule

module ifu_controller (
   input CLK, CLR, PRE,

   input V_MEM_RD,
   input [31:0] RA_RD_ADDR1,
   input [4:0] RA_RD_SIZE1,
   input RD_ADDR1_V,

   input [31:0] RA_RD_ADDR2,
   input [4:0] RA_RD_SIZE2,
   input RD_ADDR2_V,

   // inputs from cache
   input [127:0] ICACHE_RD_DATA,
   input ICACHE_READY,

   // outputs to cache
   output [31:0] ICACHE_ADDR_OUT,
   output [4:0] ICACHE_SIZE_OUT,
   output ICACHE_EN,

   output ICACHE_RD_STALL,

   output [127:0] RD_DATA_OUT
);

/*
RD.OP1 = (!ICACHE.R&!RD.OP2&RD.V&RD.ADDR1.V);

RD.OP2 = (!ICACHE.R&!RD.OP1&RD.OP2&RD.V&RD.ADDR1.V&RD.ADDR2.V) | (
    ICACHE.R&!RD.OP2&RD.V&RD.ADDR1.V&RD.ADDR2.V);
*/
   wire [31:0] state, stateQ, stateQBAR;
   wire Drd_op1, Drd_op2,
        rd_op1, rd_op2, rd_op1_bar, rd_op2_bar;

   assign state[1:0] = {Drd_op1, Drd_op2};
   assign {rd_op1, rd_op2} = stateQ[1:0];
   assign {rd_op1_bar, rd_op2_bar} = stateQBAR[1:0];

   reg32e$ u_ifu_state (CLK, state, stateQ, stateQBAR, CLR, PRE, 1'b1);

   wire icache_ready_bar;
   wire and0_out, and1_out, and2_out, and3_out, and4_out,
        and5_out, and6_out, and7_out, or0_out;

   assign Drd_op1 = and1_out;
   assign Drd_op2 = or0_out;

   inv1$ inv0 (icache_ready_bar, ICACHE_READY);

   and2$ and0 (and0_out, V_MEM_RD, RD_ADDR1_V);
   and3$ and1 (and1_out, icache_ready_bar, rd_op2_bar, and0_out); 

   and3$
      and2 (and2_out, icache_ready_bar, rd_op1_bar, rd_op2),
      and3 (and3_out, V_MEM_RD, RD_ADDR1_V, RD_ADDR2_V),

      and4 (and4_out, ICACHE_READY, rd_op2_bar, V_MEM_RD);

   and2$
      and5 (and5_out, and2_out, and3_out),

      and6 (and6_out, RD_ADDR1_V, RD_ADDR2_V),
      and7 (and7_out, and4_out, and6_out);

   or2$ or0 (or0_out, and5_out, and7_out);

   mux2_32 mux0 (ICACHE_ADDR_OUT, RA_RD_ADDR1, RA_RD_ADDR2, rd_op2);
   mux2_4 mux1 (ICACHE_SIZE_OUT[3:0], RA_RD_SIZE1[3:0], RA_RD_SIZE2[3:0], rd_op2);
   mux2$ mux2 (ICACHE_SIZE_OUT[4], RA_RD_SIZE1[4], 1'b0, rd_op2);

   assign ICACHE_EN = V_MEM_RD;

   or2$ or1 (ICACHE_RD_STALL, Drd_op1, Drd_op2);

   wire [127:0] rd_addr1_data;
   wire and_rd_op2_out;

   and2$ and_rd_op2 (and_rd_op2_out, ICACHE_READY, Drd_op2);
   reg128e reg_rd_data (CLK, ICACHE_RD_DATA[127:0], rd_addr1_data, , CLR, PRE, and_rd_op2_out);

   wire [127:0] ra_rd_mask, sll_rd_data_out, and_rd_data_mask_out, or_rd_data_out;

   ifu_mask_detector u_ifu_mask_detector (RA_RD_SIZE1[3:0], ra_rd_mask);
   sll128 sll_rd_data (sll_rd_data_out, ICACHE_RD_DATA[127:0], {RA_RD_SIZE1[3:0], 3'b0});
   
   and2$ and_rd_data_mask [127:0] (and_rd_data_mask_out, rd_addr1_data, ra_rd_mask);
   or2$ or_rd_data [127:0] (or_rd_data_out, and_rd_data_mask_out, sll_rd_data_out);

   wire [127:0] mux_rd_data_out;
   mux2_128 mux_rd_data (mux_rd_data_out, ICACHE_RD_DATA, or_rd_data_out, rd_op2);

   assign RD_DATA_OUT = {mux_rd_data_out[7:0], mux_rd_data_out[15:8], mux_rd_data_out[23:16], mux_rd_data_out[31:24], mux_rd_data_out[39:32], mux_rd_data_out[47:40], mux_rd_data_out[55:48], mux_rd_data_out[63:56], mux_rd_data_out[71:64], mux_rd_data_out[79:72], mux_rd_data_out[87:80], mux_rd_data_out[95:88], mux_rd_data_out[103:96], mux_rd_data_out[111:104], mux_rd_data_out[119:112], mux_rd_data_out[127:120]};

endmodule

module ifu (
   input CLK, CLR, PRE,

   // inputs from FETCH stage
   input V_MEM_RD,
   input [31:0] VA_RD_ADDR,
   input [15:0] CSEG,

   // input [4:0] LA_RD_SIZE, // only supports 16B ICACHE reads

   // inputs from ICACHE
   input [127:0] ICACHE_RD_DATA,
   input ICACHE_READY,

   output [31:0] ICACHE_ADDR_OUT,
   output [4:0] ICACHE_SIZE_OUT,
   output ICACHE_RW_OUT,
   output ICACHE_EN_OUT,

   output ICACHE_RD_STALL_OUT,
   output [127:0] RD_DATA_OUT
);

   wire [31:0] la_rd_addr, add_rd_cl_out, add_rd_pg_out;
   wire [23:0] rd_addr1_entry, rd_addr2_entry;
   wire rd_addr1_match, rd_addr2_match;

   carry_lookahead32
      add_cseg (la_rd_addr, , , , , VA_RD_ADDR, {CSEG, 16'b0}, 1'b0, 1'b0);
   carry_lookahead32
      add_rd_cl (add_rd_cl_out, , , , , {24'b0, la_rd_addr[11:4]}, 32'b0, 1'b1, 1'b0),
      add_rd_pg (add_rd_pg_out, , , , , {12'b0, la_rd_addr[31:12]}, 32'b0, 1'b1, 1'b0);

   tlb itlb (la_rd_addr[31:12], add_rd_pg_out[19:0], , , rd_addr1_entry, rd_addr2_entry, , ,
             rd_addr1_match, rd_addr2_match, , );

   // cross cache line if last 4 bits of addr nonzero
   // cross page if [11:4] = 1 && last 4 bits of addr nonzero
   wire or0_out, and4_out, and5_out, and6_out;
   wire cross_cl, cross_pg;

   or4$ or0 (or0_out, la_rd_addr[3], la_rd_addr[2], la_rd_addr[1], la_rd_addr[0]);
   and4$
      and4 (and4_out, la_rd_addr[11], la_rd_addr[10], la_rd_addr[9], la_rd_addr[8]),
      and5 (and5_out, la_rd_addr[7], la_rd_addr[6], la_rd_addr[5], la_rd_addr[4]);
   and3$ and6 (and6_out, and4_out, and5_out, or0_out);

   assign cross_cl = or0_out;
   assign cross_pg = and6_out;

   wire [4:0] cross_size1, cross_size2;
   wire and0_out, and1_out, and2_out, and3_out;
   wire xor0_out, xor1_out, nand0_out, nand1_out;
   wire rd_addr1_entry_v, rd_addr1_entry_v_bar;
   wire rd_addr1_v, rd_addr2_v;

   wire [31:0] mux_rd_addr2_out;
   wire rd_page_fault_exception;
   wire icache_en, icache_rd_stall;

   cross_icache_line_size u_cross_icache_line_size (la_rd_addr[3:0], cross_size1, cross_size2);

   ifu_controller u_ifu_controller (CLK, CLR, PRE, V_MEM_RD, {rd_addr1_entry[23:4], la_rd_addr[11:0]}, cross_size1, rd_addr1_v, mux_rd_addr2_out, cross_size2, rd_addr2_v, ICACHE_RD_DATA, ICACHE_READY, ICACHE_ADDR_OUT, ICACHE_SIZE_OUT, icache_en, icache_rd_stall, RD_DATA_OUT);

   mux2_32 mux_rd_addr2 (mux_rd_addr2_out, {rd_addr1_entry[23:4], add_rd_cl_out[7:0], 4'b0}, {rd_addr2_entry[23:4], 12'b0}, cross_pg);

   // rd_addr1_entry_v
   and2$ and0 (and0_out, rd_addr1_match, rd_addr1_entry[`PTE_V]);
   xor2$ xor0 (xor0_out, rd_addr1_entry[`PTE_P], rd_addr1_entry[`PTE_PCD]);
   and2$ and1 (and1_out, and0_out, xor0_out);
   assign rd_addr1_entry_v = and1_out;

   nand2$ nand0 (nand0_out, and0_out, xor0_out);
   assign rd_addr1_entry_v_bar = nand0_out;

   assign rd_addr1_v = rd_addr1_entry_v; // INPUT to CONTROLLER

   // rd_addr2_entry_v
   and2$ and2 (and2_out, rd_addr2_match, rd_addr2_entry[`PTE_V]);
   xor2$ xor1 (xor1_out, rd_addr2_entry[`PTE_P], rd_addr2_entry[`PTE_PCD]);
   and2$ and3 (and3_out, and2_out, xor1_out);
   assign rd_addr2_entry_v = and3_out;

   nand2$ nand1 (nand1_out, and2_out, xor1_out);
   assign rd_addr2_entry_v_bar = nand1_out;

   wire and_rd_addr2_v_out;
   and3$ and_rd_addr2_v (and_rd_addr2_v_out, and2_out, xor1_out, cross_pg); // INPUT to CONTROLLER
   or2$ or_rd_addr2_v (rd_addr2_v, and_rd_addr2_v_out, cross_cl);

   wire and_rd_addr1_fault_out, and_rd_addr2_fault_out;

   // rd_page_fault_exception
   and2$ and_rd_addr1_fault (and_rd_addr1_fault_out, V_MEM_RD, rd_addr1_entry_v_bar);
   and3$ and_rd_addr2_fault (and_rd_addr2_fault_out, V_MEM_RD, cross_pg, rd_addr2_entry_v_bar);
   or2$ or_rd_page_fault (rd_page_fault_exception, and_rd_addr1_fault_out, and_rd_addr2_fault_out);

   assign ICACHE_RW_OUT = 1'b0;
   inv1$ inv0 (rd_page_fault_exception_bar, rd_page_fault_exception);
   and2$ and_icache_en (ICACHE_EN_OUT, icache_en, rd_page_fault_exception_bar);
   and2$ and_stall (ICACHE_RD_STALL_OUT, icache_rd_stall, rd_page_fault_exception_bar);

endmodule

