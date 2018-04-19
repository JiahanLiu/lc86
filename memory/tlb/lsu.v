module mux2_4 (Y, IN0, IN1, S0);
   output [3:0] Y;

   input [3:0] IN0, IN1;
   input S0;

   wire [7:0] in0, in1;
   wire [3:0] Y_NC;

   assign in0[3:0] = IN0;
   assign in1[3:0] = IN1;

   mux2_8$ mux0 ({Y_NC, Y}, in0, in1, S0);

endmodule

module mux4_4 (Y, IN0, IN1, IN2, IN3, S0, S1);
   output [3:0] Y;

   input [3:0] IN0, IN1, IN2, IN3;
   input S0, S1;

   wire [7:0] in0, in1, in2, in3;
   wire [3:0] Y_NC;

   assign in0[3:0] = IN0;
   assign in1[3:0] = IN1;
   assign in2[3:0] = IN2;
   assign in3[3:0] = IN3;

   mux4_8$ mux0 ({Y_NC, Y}, in0, in1, in2, in3, S0, S1);

endmodule

module mux2_32 (Y, IN0, IN1, S0);
   output [31:0] Y;

   input [31:0] IN0, IN1;
   input S0;

   mux2_16$
      muxhi (Y[31:16], IN0[31:16], IN1[31:16], S0),
      muxlo (Y[15:0], IN0[15:0], IN1[15:0], S0);

endmodule

module mux2_64 (Y, IN0, IN1, S0);
   output [63:0] Y;

   input [63:0] IN0, IN1;
   input S0;

   mux2_32
      muxhi (Y[63:32], IN0[63:32], IN1[63:32], S0),
      muxlo (Y[31:0], IN0[31:0], IN1[31:0], S0);

endmodule

module mux2_128 (Y, IN0, IN1, S0);
   output [127:0] Y;

   input [127:0] IN0, IN1;
   input S0;

   mux2_64
      muxhi (Y[127:64], IN0[127:64], IN1[127:64], S0),
      muxlo (Y[63:0], IN0[63:0], IN1[63:0], S0);

endmodule

module lsu_controller (
   input CLK, CLR, PRE,

   input V_MEM_RD,
   input [31:0] RA_RD_ADDR1,
   input [3:0] RA_RD_SIZE1,
   input RD_ADDR1_V,

   input [31:0] RA_RD_ADDR2,
   input [3:0] RA_RD_SIZE2,
   input RD_ADDR2_V,

   input V_MEM_WR,
   input [31:0] RA_WR_ADDR1,
   input [3:0] RA_WR_SIZE1,
   input WR_ADDR1_V,

   input [31:0] RA_WR_ADDR2,
   input [3:0] RA_WR_SIZE2,
   input WR_ADDR2_V,

   input [63:0] WR_DATA,

   // inputs from cache
   input [127:0] DCACHE_RD_DATA,
   input DCACHE_READY,

   // outputs to cache
   output [31:0] DCACHE_ADDR_OUT,
   output [3:0] DCACHE_SIZE_OUT,
   output DCACHE_RW_OUT,
   output DCACHE_EN,

   output [63:0] DCACHE_WR_DATA_OUT,

   // stall signals
   output DCACHE_RD_STALL,
   output DCACHE_WR_STALL,

   // output to stage
   output [63:0] RD_DATA_OUT
);

   wire dcache_ready_bar, wr_v_bar, wr_addr1_v_bar, wr_addr2_v_bar;

   wire and0_out, and1_out, and2_out, and3_out,
        and4_out, and5_out, and6_out, and7_out,
        and8_out, and9_out, and10_out, and11_out,
        and12_out, and13_out, and14_out, and15_out,
        and16_out, and17_out, and18_out, and19_out,
        and20_out, and21_out;
   wire or0_out, or1_out, or2_out;

/*
RD.OP1 = (!DCACHE.R&!RD.OP2&!WR.OP1&!WR.OP2&RD.V&RD.ADDR1.V&!WR.V
    &!WR.ADDR1.V&!WR.ADDR2.V) | (!DCACHE.R&RD.OP1&!RD.OP2&!WR.OP1&!WR.OP2
    &RD.V&RD.ADDR1.V);

RD.OP2 = (DCACHE.R&!RD.OP2&!WR.OP1&!WR.OP2&RD.V&RD.ADDR1.V&RD.ADDR2.V
    &!WR.V&!WR.ADDR1.V&!WR.ADDR2.V) | (DCACHE.R&RD.OP1&!RD.OP2&!WR.OP1
    &!WR.OP2&RD.V&RD.ADDR1.V&RD.ADDR2.V) | (!DCACHE.R&!RD.OP1&RD.OP2
    &!WR.OP1&!WR.OP2&RD.V&RD.ADDR1.V&RD.ADDR2.V);

WR.OP1 = (!DCACHE.R&!RD.OP1&!RD.OP2&!WR.OP2&WR.V&WR.ADDR1.V);

WR.OP2 = (DCACHE.R&!RD.OP1&!RD.OP2&!WR.OP2&WR.V&WR.ADDR1.V&WR.ADDR2.V) | (
    !DCACHE.R&!RD.OP1&!RD.OP2&!WR.OP1&WR.OP2&WR.V&WR.ADDR1.V&WR.ADDR2.V);
*/

   wire [31:0] state, stateQ, stateQBAR;
   wire Drd_op1, Drd_op2, Dwr_op1, Dwr_op2,
        rd_op1, rd_op2, wr_op1, wr_op2,
        rd_op1_bar, rd_op2_bar, wr_op1_bar, wr_op2_bar;

   assign state[3:0] = {Drd_op1, Drd_op2, Dwr_op1, Dwr_op2};
   assign {rd_op1, rd_op2, wr_op1, wr_op2} = stateQ[3:0];
   assign {rd_op1_bar, rd_op2_bar, wr_op1_bar, wr_op2_bar} = stateQBAR[3:0];

   always @(*) begin
      $strobe("state %h @ %0t", stateQ[3:0], $time);
   end

   reg32e$ u_lsu_state (CLK, state, stateQ, stateQBAR, CLR, PRE, 1'b1);

   assign Drd_op1 = or0_out;
   assign Drd_op2 = or1_out;
   assign Dwr_op1 = and15_out;
   assign Dwr_op2 = or2_out;

   inv1$
      inv0 (dcache_ready_bar, DCACHE_READY),
      inv1 (wr_v_bar, V_MEM_WR),
      inv2 (wr_addr1_v_bar, WR_ADDR1_V),
      inv3 (wr_addr2_v_bar, WR_ADDR2_V);

   // Drd_op1 input to next state
   and3$
      and0 (and0_out, dcache_ready_bar, rd_op2_bar, wr_op1_bar),
      and1 (and1_out, wr_op2_bar, V_MEM_RD, RD_ADDR1_V),
      and2 (and2_out, wr_v_bar, wr_addr1_v_bar, wr_addr2_v_bar),
      and3 (and3_out, and0_out, and1_out, and2_out),

      and4 (and4_out, dcache_ready_bar, rd_op1, rd_op2_bar),
      and5 (and5_out, wr_op1_bar, wr_op2_bar, V_MEM_RD),
      and6 (and6_out, and4_out, and5_out, RD_ADDR1_V);

   or2$ or0 (or0_out, and3_out, and6_out);

   // Drd_op2
   and4$
      and22 (and22_out, DCACHE_READY, rd_op2_bar, wr_op1_bar, wr_op2_bar),
      and23 (and23_out, V_MEM_RD, RD_ADDR1_V, RD_ADDR2_V, wr_v_bar);
   and2$
      and24 (and24_out, wr_addr1_v_bar, wr_addr2_v_bar);
   and3$
      and25 (and25_out, and22_out, and23_out, and24_out);

   and4$
      and7 (and7_out, DCACHE_READY, rd_op1, rd_op2_bar, wr_op1_bar),
      and8 (and8_out, wr_op2_bar, V_MEM_RD, RD_ADDR1_V, RD_ADDR2_V),

      and9 (and9_out, dcache_ready_bar, rd_op1_bar, rd_op2, wr_op1_bar),
      and10 (and10_out, wr_op2_bar, V_MEM_RD, RD_ADDR1_V, RD_ADDR2_V);

   and2$
      and11 (and11_out, and7_out, and8_out),
      and12 (and12_out, and9_out, and10_out);

   or3$ or1 (or1_out, and11_out, and12_out, and25_out);

   // Dwr_op1
   and3$
      and13 (and13_out, dcache_ready_bar, rd_op1_bar, rd_op2_bar),
      and14 (and14_out, wr_op2_bar, V_MEM_WR, WR_ADDR1_V);
   and2$ and15 (and15_out, and13_out, and14_out);

   // Dwr_op2
   and3$
      and16 (and16_out, DCACHE_READY, rd_op1_bar, rd_op2_bar),
      and17 (and17_out, wr_op2_bar, V_MEM_WR, WR_ADDR1_V),
      and20 (and20_out, and16_out, and17_out, WR_ADDR2_V);

   and4$
      and18 (and18_out, dcache_ready_bar, rd_op1_bar, rd_op2_bar, wr_op1_bar),
      and19 (and19_out, wr_op2, V_MEM_WR, WR_ADDR1_V, WR_ADDR2_V);

   and2$
      and21 (and21_out, and18_out, and19_out);

   or2$ or2 (or2_out, and20_out, and21_out);

   wire [31:0] mux_rd_addr_out, mux_wr_addr_out;
   wire [3:0] mux_rd_size_out, mux_wr_size_out;

   mux2_32
      mux_rd_addr (mux_rd_addr_out, RA_RD_ADDR1, RA_RD_ADDR2, rd_op2),
      mux_wr_addr (mux_wr_addr_out, RA_WR_ADDR1, RA_WR_ADDR2, wr_op2),
      mux_rw_addr (DCACHE_ADDR_OUT, mux_rd_addr_out, mux_wr_addr_out, V_MEM_WR);

   mux2_4
      mux_rd_size (mux_rd_size_out, RA_RD_SIZE1, RA_RD_SIZE2, rd_op2),
      mux_wr_size (mux_wr_size_out, RA_WR_SIZE1, RA_WR_SIZE2, wr_op2),
      mux_rw_size (DCACHE_SIZE_OUT, mux_rd_size_out, mux_wr_size_out, V_MEM_WR);

   assign DCACHE_RW_OUT = V_MEM_WR;
   or2$ or3 (DCACHE_EN, V_MEM_RD, V_MEM_WR);

   wire and_rd_op2_out, and_wr_op2_out;
   wire [63:0] sll_rd_data_out, slr_wr_data_out;
   wire [63:0] rd_addr1_data, wr_addr2_data; // outputs from temp registers

   wire [63:0] mux_rd_mask_out;
   wire [63:0] and_rd_data_out, or_rd_data_out;

`define MASK55_0 64'h00FFFFFFFFFFFFFF
`define MASK47_0 64'h0000FFFFFFFFFFFF
`define MASK39_0 64'h000000FFFFFFFFFF
`define MASK31_0 64'h00000000FFFFFFFF
`define MASK23_0 64'h0000000000FFFFFF
`define MASK15_0 64'h000000000000FFFF
`define MASK7_0  64'h00000000000000FF

   and2$
      and_rd_op2 (and_rd_op2_out, DCACHE_READY, Drd_op2),
      and_wr_op2 (and_wr_op2_out, DCACHE_READY, Dwr_op2);
   slr64 slr_wr_data (slr_wr_data_out, WR_DATA, {RA_WR_SIZE1[2:0], 3'b0});

   reg64e$
      reg_rd_data (CLK, DCACHE_RD_DATA[63:0], rd_addr1_data, , CLR, PRE, and_rd_op2_out),
      reg_wr_data (CLK, slr_wr_data_out, wr_addr2_data, , CLR, PRE, and_wr_op2_out);

   mux2_64 mux_wr_data (DCACHE_WR_DATA_OUT, WR_DATA, wr_addr2_data, wr_op2);

   mux8_64 mux_rd_mask (mux_rd_mask_out, 64'h0, `MASK7_0, `MASK15_0, `MASK23_0, `MASK31_0, `MASK39_0, `MASK47_0, `MASK55_0, RA_RD_SIZE1[2:0]);
   and2$ and_rd_data [63:0] (and_rd_data_out, mux_rd_mask_out, rd_addr1_data);

   sll64 sll_rd_data (sll_rd_data_out, DCACHE_RD_DATA[63:0], {RA_RD_SIZE1[2:0], 3'b0});
   or2$ or_rd_data [63:0] (or_rd_data_out, sll_rd_data_out, and_rd_data_out);

   mux2_64 mux_rd_data (RD_DATA_OUT, DCACHE_RD_DATA[63:0], or_rd_data_out, rd_op2);

   wire or4_out, or5_out;

   or4$ or4 (or4_out, Drd_op1, Drd_op2, Dwr_op1, Dwr_op2);
   and2$ and_rd_stall (DCACHE_RD_STALL, V_MEM_RD, or4_out);

   or2$ or5 (or5_out, Dwr_op1, Dwr_op2);
   and2$ and_wr_stall (DCACHE_WR_STALL, V_MEM_WR, or5_out);

endmodule  

module lsu (
   input CLK, RST,

   // inputs from MEMORY Stage
   input V_MEM_RD,
   input [31:0] LA_RD_ADDR,
   input [1:0] LA_RD_SIZE,

   // inputs from WRITEBACK Stage
   input V_MEM_WR,
   input [31:0] LA_WR_ADDR,
   input [1:0] LA_WR_SIZE,

   input [63:0] WR_DATA,

   // inputs from DCACHE
   input [127:0] DCACHE_RD_DATA,
   input DCACHE_READY,

   output [31:0] DCACHE_ADDR_OUT,
   output [3:0] DCACHE_SIZE_OUT,
   output DCACHE_RW_OUT,
   output DCACHE_EN_OUT,

   output [63:0] DCACHE_WR_DATA_OUT,

   output DCACHE_RD_STALL_OUT, DCACHE_WR_STALL_OUT,
   output [63:0] RD_DATA_OUT
);

   wire [23:0] rd_addr1_entry, rd_addr2_entry,
               wr_addr1_entry, wr_addr2_entry;

   wire rd_addr1_match, rd_addr2_match,
        wr_addr1_match, wr_addr2_match;

   wire rd_addr_cross_page, rd_addr_cross_cl,
	wr_addr_cross_page, wr_addr_cross_cl;

   wire [3:0] rd_addr1_cross_size, rd_addr2_cross_size,
	      wr_addr1_cross_size, wr_addr2_cross_size;
   
   wire [31:0] add_rd_cl_out, add_rd_pg_out, mux_rd_addr2_out,
               add_wr_cl_out, add_wr_pg_out, mux_wr_addr2_out;

   carry_lookahead32
      add_rd_cl (add_rd_cl_out, , , , , {24'b0, LA_RD_ADDR[11:4]}, 32'b0, 1'b1, 1'b0),
      add_rd_pg (add_rd_pg_out, , , , , {12'b0, LA_RD_ADDR[31:12]}, 32'b0, 1'b1, 1'b0),
      add_wr_cl (add_wr_cl_out, , , , , {24'b0, LA_WR_ADDR[11:4]}, 32'b0, 1'b1, 1'b0),
      add_wr_pg (add_wr_pg_out, , , , , {12'b0, LA_WR_ADDR[31:12]}, 32'b0, 1'b1, 1'b0);

   tlb dtlb (LA_RD_ADDR[31:12], add_rd_pg_out[19:0], LA_WR_ADDR[31:12], add_wr_pg_out[19:0],
             rd_addr1_entry, rd_addr2_entry, wr_addr1_entry, wr_addr2_entry,
             rd_addr1_match, rd_addr2_match, wr_addr1_match, wr_addr2_match);
   cross_boundary_detector
      u_cross_boundary_detector_rd (LA_RD_ADDR[11:0], LA_RD_SIZE[1:0], rd_addr_cross_page, rd_addr_cross_cl),
      u_cross_boundary_detector_wr (LA_WR_ADDR[11:0], LA_WR_SIZE[1:0], wr_addr_cross_page, wr_addr_cross_cl);
   cross_size_detector
      u_cross_size_detector_rd (LA_RD_ADDR[3:0], LA_RD_SIZE[1:0], rd_addr1_cross_size, rd_addr2_cross_size),
      u_cross_size_detector_wr (LA_WR_ADDR[3:0], LA_WR_SIZE[1:0], wr_addr1_cross_size, wr_addr2_cross_size);
 
   initial
      begin
//         $monitor("LA_RD_ADDR:%h LA_WR_ADDR:%h rd_entry:%h rd_entry2:%h wr_entry:%h wr_entry2:%h rd_match:%h rd_end_match:%h wr_match:%h wr_end_match:%h @ %0t", LA_RD_ADDR, LA_WR_ADDR, rd_addr1_entry, rd_addr2_entry, wr_addr1_entry, wr_addr2_entry, rd_addr1_match, rd_addr2_match, wr_addr1_match, wr_addr2_match, $time);
	 $monitor("LA_RD_ADDR:%h size:%d cross page:%d cross cache line:%d @ %0t", LA_RD_ADDR, LA_RD_SIZE, rd_addr_cross_page, rd_addr_cross_cl, $time);
      end  

   always @(*)
     begin
	$strobe("cross size:%d cross next: %d @ %0t", rd_addr1_cross_size, rd_addr2_cross_size, $time);
     end
   
   wire [3:0] mux_rd_data_size_out, mux_wr_data_size_out,
              mux_rd_cross_size_out, mux_wr_cross_size_out;

   wire rd_addr1_v, rd_addr2_v, wr_addr1_v, wr_addr2_v;
   wire rd_addr1_entry_v, rd_addr2_entry_v, wr_addr1_entry_v, wr_addr2_entry_v;
   wire rd_addr1_entry_v_bar, rd_addr2_entry_v_bar, wr_addr1_entry_v_bar, wr_addr2_entry_v_bar;

`define PTE_V 3
`define PTE_P 2
`define PTE_RW 1
`define PTE_PCD 0
 
   // rd_addr1_v = rd_addr1_match && rd_addr1_entry[V] && (rd_addr1_entry[P] XOR rd_addr1_entry[PCD])
   // rd_addr2_v = rd_addr2_match && rd_addr2_entry[V] && (rd_addr2_entry[P] XOR rd_addr2_entry[PCD]) && rd_addr_cross_page || rd_addr_cross_cl
   // wr_addr1_v = wr_addr1_match && wr_addr1_entry[V] && (wr_addr1_entry[P] XOR wr_addr1_entry[PCD]) && wr_addr1_entry[R/W]
   // wr_addr2_v = wr_addr2_match && wr_addr2_entry[V] && (wr_addr2_entry[P] XOR wr_addr2_entry[PCD]) && wr_addr2_entry[R/W] && wr_addr_cross_page || wr_addr_cross_cl
    
   // rd_page_fault_exception = (V_MEM_RD && rd_addr1_v_bar) || (V_MEM_RD && rd_addr_cross_cl && rd_addr_end_valid_bar)
   // wr_page_fault_exception = (V_MEM_WR && wr_addr_v_bar) || (V_MEM_WR && wr_addr_cross_cl && wr_addr_end_valid_bar)
   //
   // general_protection_exception = (V_MEM_WR && wr_addr_v && wr_addr1_entry[R/W]_bar) || (V_MEM_WR && wr_addr_cross_cl && wr_addr_end_v && wr_addr2_entry[R/W]_bar

   wire and0_out, and1_out, and2_out, and3_out, and4_out, and5_out, and6_out, and7_out;
   wire xor0_out, xor1_out, xor2_out, xor3_out;
   wire nand0_out, nand1_out, nand2_out, nand3_out;

   wire rd_page_fault_exception, wr_page_fault_exception, general_protection_exception;

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
   and3$ and_rd_addr2_v (and_rd_addr2_v_out, and2_out, xor1_out, rd_addr_cross_page); // INPUT to CONTROLLER
   or2$ or_rd_addr2_v (rd_addr2_v, and_rd_addr2_v_out, rd_addr_cross_cl);

   wire and_rd_addr1_fault_out, and_rd_addr2_fault_out;

   // rd_page_fault_exception
   and2$ and_rd_addr1_fault (and_rd_addr1_fault_out, V_MEM_RD, rd_addr1_entry_v_bar);
   and3$ and_rd_addr2_fault (and_rd_addr2_fault_out, V_MEM_RD, rd_addr_cross_page, rd_addr2_entry_v_bar);
   or2$ or_rd_page_fault (rd_page_fault_exception, and_rd_addr1_fault_out, and_rd_addr2_fault_out);

   // wr_addr1_entry_v
   and2$ and4 (and4_out, wr_addr1_match, wr_addr1_entry[`PTE_V]);
   xor2$ xor2 (xor2_out, wr_addr1_entry[`PTE_P], wr_addr1_entry[`PTE_PCD]);
   and2$ and5 (and5_out, and4_out, xor2_out);
   assign wr_addr1_entry_v = and5_out;

   nand2$ nand2 (nand2_out, and4_out, xor2_out);
   assign wr_addr1_entry_v_bar = nand2_out;

   and3$ and_wr_addr1_v (wr_addr1_v, and4_out, xor2_out, wr_addr1_entry[`PTE_RW]); // INPUT to CONTROLLER

   // wr_addr2_entry_v
   and2$ and6 (and6_out, wr_addr2_match, wr_addr2_entry[`PTE_V]);
   xor2$ xor3 (xor3_out, wr_addr2_entry[`PTE_P], wr_addr2_entry[`PTE_PCD]);
   and2$ and7 (and7_out, and6_out, xor3_out);
   assign wr_addr2_entry_v = and7_out;

   nand2$ nand3 (nand3_out, and6_out, xor3_out);
   assign wr_addr2_entry_v_bar = nand3_out;

   wire and_wr_addr2_v_out;
   and2$ and_wr_addr2_rw (and_wr_addr2_rw_out, wr_addr2_entry[`PTE_RW], wr_addr_cross_page);
   and3$ and_wr_addr2_v (and_wr_addr2_v_out, and6_out, xor3_out, and_wr_addr2_rw_out); // INPUT to CONTROLLER
   or2$ or_wr_addr2_v (wr_addr2_v, and_wr_addr2_v_out, wr_addr_cross_cl);

   wire and_wr_addr1_fault_out, and_wr_addr2_fault_out, wr_addr1_entry_rw_bar, wr_addr2_entry_rw_bar;
   wire and_wr_addr1_gprot_out, and_wr_addr1_gprot2_out, and_wr_addr2_gprot_out, and_wr_addr2_gprot2_out;

   // wr_page_fault_exception
   and2$ and_wr_addr1_fault (and_wr_addr1_fault_out, V_MEM_WR, wr_addr1_entry_v_bar);
   and3$ and_wr_addr2_fault (and_wr_addr2_fault_out, V_MEM_WR, wr_addr_cross_page, wr_addr2_entry_v_bar);
   or2$ or_wr_page_fault (wr_page_fault_exception, and_wr_addr1_fault_out, and_wr_addr2_fault_out);

   // general_protection_exception
   inv1$ inv_wr_addr1_entry_rw (wr_addr1_entry_rw_bar, wr_addr1_entry[`PTE_RW]);
   inv1$ inv_wr_addr2_entry_rw (wr_addr2_entry_rw_bar, wr_addr2_entry[`PTE_RW]);

   and3$ and_wr_addr1_gprot (and_wr_addr1_gprot_out, V_MEM_WR, and4_out, xor2_out);
   and2$ and_wr_addr1_gprot2 (and_wr_addr1_gprot2_out, and_wr_addr1_gprot_out, wr_addr1_entry_rw_bar);

   and2$ and_wr_addr2_gprot (and_wr_addr2_gprot_out, V_MEM_WR, wr_addr_cross_page);
   and3$ and_wr_addr2_gprot2 (and_wr_addr2_gprot2_out, and_wr_addr2_gprot_out, wr_addr2_entry_v, wr_addr2_entry_rw_bar);
   or2$ or_wr_addr_gprot (general_protection_exception, and_wr_addr1_gprot2_out, and_wr_addr2_gprot2_out);

   mux4_4
      mux_rd_data_size (mux_rd_data_size_out, 4'b0001, 4'b0010, 4'b0100, 4'b1000, LA_RD_SIZE[0], LA_RD_SIZE[1]),
      mux_wr_data_size (mux_wr_data_size_out, 4'b0001, 4'b0010, 4'b0100, 4'b1000, LA_WR_SIZE[0], LA_WR_SIZE[1]);

   mux2_4
      mux_rd_cross_size (mux_rd_cross_size_out, mux_rd_data_size_out, rd_addr1_cross_size, rd_addr_cross_cl),
      mux_wr_cross_size (mux_wr_cross_size_out, mux_wr_data_size_out, wr_addr1_cross_size, wr_addr_cross_cl);

   mux2_32
      mux_rd_addr2 (mux_rd_addr2_out, {rd_addr1_entry[23:4], add_rd_cl_out[7:0], 4'b0}, {rd_addr2_entry[23:4], 12'b0}, rd_addr_cross_page),
      mux_wr_addr2 (mux_wr_addr2_out, {wr_addr1_entry[23:4], add_wr_cl_out[7:0], 4'b0}, {wr_addr2_entry[23:4], 12'b0}, wr_addr_cross_page);

   wire dcache_en, dcache_rd_stall;

   lsu_controller u_lsu_controller (CLK, RST, 1'b1, V_MEM_RD, {rd_addr1_entry[23:4], LA_RD_ADDR[11:0]}, mux_rd_cross_size_out, rd_addr1_v, mux_rd_addr2_out, rd_addr2_cross_size, rd_addr2_v, V_MEM_WR, {wr_addr1_entry[23:4], LA_WR_ADDR[11:0]}, mux_wr_cross_size_out, wr_addr1_v, mux_wr_addr2_out, wr_addr2_cross_size, wr_addr2_v, WR_DATA, DCACHE_RD_DATA, DCACHE_READY, DCACHE_ADDR_OUT, DCACHE_SIZE_OUT, DCACHE_RW_OUT, dcache_en, DCACHE_WR_DATA_OUT, dcache_rd_stall, DCACHE_WR_STALL_OUT, RD_DATA_OUT);

   wire nor_exception_out;

   nor3$ nor_exception (nor_exception_out, rd_page_fault_exception, wr_page_fault_exception, general_protection_exception);
   and2$ and_dcache_en (DCACHE_EN_OUT, dcache_en, nor_exception_out);
   and2$ and_rd_stall (DCACHE_RD_STALL_OUT, dcache_rd_stall, nor_exception_out);

/* general protection exception: write a read only page
   page fault exception: page not in TLB OR page not present

   if cross 16B boundary, need to get two cache lines
   if cross page boundary, still only need to get two cache lines
      second addr always ends in 12'h000, data_size changes
*/
//   always @(posedge CLK)
//      begin
//         if (state == 0) begin
//	    
//         end
endmodule

