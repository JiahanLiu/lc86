module TOP;
   reg clk, rst;

   reg LA_V;
   reg [31:0] LA_RD_ADDR, LA_WR_ADDR;
   reg [1:0] LA_RD_SIZE, LA_WR_SIZE;

   wire [31:0] RA_RD_ADDR;
   wire [1:0] RA_RD_SIZE;

`define half_cycle 50
   initial 
     begin
	clk = 1'b0;
	rst = 1'b0;

        LA_RD_ADDR = 31'h02000FFF;

	#(`half_cycle*2)

        LA_RD_ADDR = 31'h020000FF;

	rst = 1'b1;
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
`define TLB_ENTRY_2 {20'h04000, 20'h00005, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_3 {20'h0b000, 20'h00004, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_4 {20'h0c000, 20'h00007, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_5 {20'h0a000, 20'h00005, 1'b1, 1'b1, 1'b1, 1'b0}
`define TLB_ENTRY_6 {20'h10000, 20'h10000, 1'b1, 1'b0, 1'b1, 1'b1}
`define TLB_ENTRY_7 {20'h20000, 20'h20000, 1'b1, 1'b0, 1'b1, 1'b1}
 
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

   lsu u_lsu (clk, rst, LA_V, LA_RD_ADDR, LA_WR_ADDR, LA_RD_SIZE, LA_WR_SIZE, RA_RD_ADDR, RA_RD_SIZE);

endmodule // TOP
