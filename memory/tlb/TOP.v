module TOP;
   reg clk, rst;

   reg LA_V;
   reg [31:0] LA_RD_ADDR, LA_WR_ADDR;
   reg [1:0] LA_RD_SIZE, LA_WR_SIZE;

`define half_cycle 10
   initial 
     begin
	clk = 1'b0;
	rst = 1'b0;

	#(`half_cycle)
	rst = 1'b1;
        LA_RD_ADDR = 31'h02000FFF;
	LA_RD_SIZE = 2'b00;
        LA_WR_ADDR = 31'h04000FFF;
	LA_WR_SIZE = 2'b00;
		     
	#(`half_cycle*4)

        LA_RD_ADDR = 31'h0200001F;
	LA_RD_SIZE = 2'b01;
        LA_WR_ADDR = 31'h0400001F;
	LA_WR_SIZE = 2'b01;
	
	#(`half_cycle*4)

	LA_RD_ADDR = 31'h02000FFF;
	LA_RD_SIZE = 2'b10;
        LA_WR_ADDR = 31'h04000FFF;
	LA_WR_SIZE = 2'b10;

	#(`half_cycle*4)

	LA_RD_ADDR = 31'h0200004A;
	LA_RD_SIZE = 2'b11;
        LA_WR_ADDR = 31'h0400003A;
	LA_WR_SIZE = 2'b11;
	
     end
   
   always #(`half_cycle) clk = ~clk;

   // Run simulation.  
   initial #(`half_cycle*50*2) $finish;

   // Dump all waveforms
   initial
      begin
	 //$dumpfile ("d_latch.dump");
	 //$dumpvars (0, TOP);
	 $vcdplusfile("lsu.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin

//  TLB ENTRY        VPN        RPN        V     PRE   R/W   PCD
`define TLB_ENTRY_0 {20'h00000, 20'h00000, 1'b1, 1'b1, 1'b0, 1'b0}
`define TLB_ENTRY_1 {20'h02000, 20'h00002, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_2 {20'h04000, 20'h00005, 1'b1, 1'b1, 1'b0, 1'b0}
`define TLB_ENTRY_3 {20'h0b000, 20'h00004, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_4 {20'h0c000, 20'h00007, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_5 {20'h0a000, 20'h00005, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_6 {20'h10000, 20'h10000, 1'b1, 1'b0, 1'b1, 1'b1}
`define TLB_ENTRY_7 {20'h02001, 20'h2FFFF, 1'b1, 1'b0, 1'b1, 1'b1}
 
/*
Virtual Page	Physical Page	Valid	Present	R/W PCD
20'h00000	20'h00000	1	1	0   0
20'h02000	20'h00002	1	1	1   0
20'h04000	20'h00005	1	1	1   0
20'h0b000	20'h00004	1	1	1   0
20'h0c000	20'h00007	1	1	1   0
20'h0a000	20'h00005	1	1	1   0
*/
   initial
      begin
         u_lsu.dtlb.ENTRY[0] = `TLB_ENTRY_0;
         u_lsu.dtlb.ENTRY[1] = `TLB_ENTRY_1;
         u_lsu.dtlb.ENTRY[2] = `TLB_ENTRY_2;
         u_lsu.dtlb.ENTRY[3] = `TLB_ENTRY_3;
         u_lsu.dtlb.ENTRY[4] = `TLB_ENTRY_4;
         u_lsu.dtlb.ENTRY[5] = `TLB_ENTRY_5;
         u_lsu.dtlb.ENTRY[6] = `TLB_ENTRY_6;
         u_lsu.dtlb.ENTRY[7] = `TLB_ENTRY_7;
      end

   wire V_MEM_RD, V_MEM_WR;
   wire [63:0] WR_DATA;
   wire [127:0] DCACHE_RD_DATA;
   wire DCACHE_READY;
   wire [31:0] DCACHE_ADDR_OUT;
   wire [3:0] DCACHE_SIZE_OUT;
   wire DCACHE_RW_OUT, DCACHE_EN;
   wire [63:0] DCACHE_WR_DATA_OUT, RD_DATA_OUT;
   wire DCACHE_RD_STALL, DCACHE_WR_STALL;

   reg rd_v, wr_v;
//   reg rd_addr1_v, rd_addr2_v, wr_addr1_v, wr_addr2_v;
   reg dcache_ready;
   reg [127:0] dcache_rd_data;
   reg [63:0] wr_data;

   assign V_MEM_RD = rd_v;
   assign V_MEM_WR = wr_v;
   assign DCACHE_READY = dcache_ready;
   assign DCACHE_RD_DATA = dcache_rd_data;
   assign WR_DATA = wr_data;

   initial begin
      rd_v = 1'b1;
      wr_v = 1'b1;
//      rd_addr1_v = 1'b1;
//      rd_addr2_v = 1'b0;
//      wr_addr1_v = 1'b1;
//      wr_addr2_v = 1'b0;
      dcache_ready = 1'b0;
      dcache_rd_data = 64'hCAFEBEEFDEADBABE;
      wr_data = 64'hDEADBEEFCAFEBABE;

      #(80*2)
      dcache_ready = 1'b1;

      #90
      dcache_ready = 1'b0;
//      rd_addr2_v = 1'b1;
//      wr_addr2_v = 1'b1;

   end


   lsu u_lsu (clk, rst, V_MEM_RD, LA_RD_ADDR, LA_RD_SIZE, V_MEM_WR, LA_WR_ADDR, LA_WR_SIZE, WR_DATA, DCACHE_RD_DATA, DCACHE_READY, DCACHE_ADDR_OUT, DCACHE_SIZE_OUT, DCACHE_RW_OUT, DCACHE_EN, DCACHE_WR_DATA_OUT, DCACHE_RD_STALL, DCACHE_WR_STALL, RD_DATA_OUT);

   wire V_FETCH;
   wire [31:0] EIP;
   wire [15:0] CSEG;
   wire [127:0] ICACHE_RD_DATA;
   wire ICACHE_READY;

   wire [31:0] ICACHE_ADDR_OUT;
   wire [4:0] ICACHE_SIZE_OUT;
   wire ICACHE_RW_OUT, ICACHE_EN_OUT, ICACHE_RD_STALL;
   wire [127:0] IR_DATA_OUT;

   reg v_fetch;
   reg [31:0] eip;
   reg [15:0] cseg;
   reg [127:0] icache_rd_data;
   reg icache_ready;

   assign V_FETCH = v_fetch;
   assign EIP = eip;
   assign CSEG = cseg;
   assign ICACHE_RD_DATA = icache_rd_data;
   assign ICACHE_READY = icache_ready;

   initial
      begin
         u_ifu.itlb.ENTRY[0] = `TLB_ENTRY_0;
         u_ifu.itlb.ENTRY[1] = `TLB_ENTRY_1;
         u_ifu.itlb.ENTRY[2] = `TLB_ENTRY_2;
         u_ifu.itlb.ENTRY[3] = `TLB_ENTRY_3;
         u_ifu.itlb.ENTRY[4] = `TLB_ENTRY_4;
         u_ifu.itlb.ENTRY[5] = `TLB_ENTRY_5;
         u_ifu.itlb.ENTRY[6] = `TLB_ENTRY_6;
         u_ifu.itlb.ENTRY[7] = `TLB_ENTRY_7;
      end

   initial begin
      v_fetch = 1'b1;
      eip = 32'h00000FF0;
      cseg = 16'h0000;
      icache_rd_data = 128'hDEADBEEFCAFEBABEDEADBEEFCAFEBABE;
      icache_ready = 1'b0;

      #(`half_cycle*4)
      icache_ready = 1'b1;
   end

   ifu u_ifu (clk, rst, 1'b1, V_FETCH, EIP, CSEG, ICACHE_RD_DATA, ICACHE_READY, ICACHE_ADDR_OUT, ICACHE_SIZE_OUT, ICACHE_RW_OUT, ICACHE_EN_OUT, ICACHE_RD_STALL, IR_DATA_OUT);
//reg32e$(CLK, Din, Q, QBAR, CLR, PRE,en)

//   wire [31:0] Qout;
//   wire        clk_bar;
   
//   reg32e$
//     testreg (clk_bar, LA_RD_ADDR, Qout, , 1'b1, 1'b1, 1'b1);

//   inv1$ (clk_bar, clk);
/*   
   always @(Qout)
     begin
	$strobe("Qout changed %h @ %0t", Qout, $time);
     end
*/   
endmodule // TOP

