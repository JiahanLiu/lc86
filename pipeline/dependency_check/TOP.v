module TOP;
   reg clk, rst;

   reg rd_v, me_v, ex_v;
   reg rd_addr1_v, rd_addr2_v, me_addr1_v, me_addr2_v, ex_addr1_v, ex_addr2_v;
   reg [31:0] rd_addr1, rd_addr2, me_addr1, me_addr2, ex_addr1, ex_addr2;
   reg [3:0] rd_size1, rd_size2, me_size1, me_size2, ex_size1, ex_size2;
`define half_cycle 10
   initial 
     begin
	clk = 1'b0;
	rst = 1'b0;

        rd_v = 1'b1;
        me_v = 1'b1;
        ex_v = 1'b1;

        rd_addr1_v = 1'b0;
        rd_addr2_v = 1'b1;
        me_addr1_v = 1'b0;
        me_addr2_v = 1'b1;
        ex_addr1_v = 1'b0;
        ex_addr2_v = 1'b1;

        rd_addr1 = 32'h0;
        rd_size1 = 4'h8;
        rd_addr2 = 32'h00002FFF;
        rd_size2 = 4'h8;

        me_addr1 = 32'h8;
        me_size1 = 4'h8;
        me_addr2 = 32'h00002FF8;
        me_size2 = 4'h8;

        ex_addr1 = 32'h8;
        ex_size1 = 4'h8;
        ex_addr2 = 32'h7;
        ex_size2 = 4'h8;

//	#(`half_cycle)
//	rst = 1'b1;
//
//		     
//	#(`half_cycle*4)
//
//	
//	#(`half_cycle*4)
//
//
//	#(`half_cycle*4)

	
     end
   
   always #(`half_cycle) clk = ~clk;

   // Run simulation.  
   initial #(`half_cycle*50*2) $finish;

   // Dump all waveforms
   initial
      begin
	 //$dumpfile ("d_latch.dump");
	 //$dumpvars (0, TOP);
	 $vcdplusfile("mem_dep.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin

   wire RD_V, ME_V, EX_V;
   wire RD_ADDR1_V, RD_ADDR2_V, ME_ADDR1_V, ME_ADDR2_V, EX_ADDR1_V, EX_ADDR2_V;
   wire [31:0] RD_ADDR1, RD_ADDR2, ME_ADDR1, ME_ADDR2, EX_ADDR1, EX_ADDR2;
   wire [3:0] RD_SIZE1, RD_SIZE2, ME_SIZE1, ME_SIZE2, EX_SIZE1, EX_SIZE2;

   assign RD_V = rd_v;
   assign ME_V = me_v;
   assign EX_V = ex_v;
   assign RD_ADDR1_V = rd_addr1_v;
   assign RD_ADDR2_V = rd_addr2_v;
   assign ME_ADDR1_V = me_addr1_v;
   assign ME_ADDR2_V = me_addr2_v;
   assign EX_ADDR1_V = ex_addr1_v;
   assign EX_ADDR2_V = ex_addr2_v;
   assign RD_ADDR1 = rd_addr1;
   assign RD_ADDR2 = rd_addr2;
   assign ME_ADDR1 = me_addr1;
   assign ME_ADDR2 = me_addr2;
   assign EX_ADDR1 = ex_addr1;
   assign EX_ADDR2 = ex_addr2;
   assign RD_SIZE1 = rd_size1;
   assign RD_SIZE2 = rd_size2;
   assign ME_SIZE1 = me_size1;
   assign ME_SIZE2 = me_size2;
   assign EX_SIZE1 = ex_size1;
   assign EX_SIZE2 = ex_size2;

   wire MEM_DEP_STALL_OUT;

   mem_dependency_check u_mem_dependency_check (RD_V, RD_ADDR1_V, RD_ADDR1, RD_SIZE1, RD_ADDR2_V, RD_ADDR2, RD_SIZE2,
                                                ME_V, ME_ADDR1_V, ME_ADDR1, ME_SIZE1, ME_ADDR2_V, ME_ADDR2, ME_SIZE2,
                                                EX_V, EX_ADDR1_V, EX_ADDR1, EX_SIZE1, EX_ADDR2_V, EX_ADDR2, EX_SIZE2,
                                                MEM_DEP_STALL_OUT);

   always @(*) begin
      $strobe("MEM_DEP_STALL %d RD_V %d RD_ADDR1_V %d RD_ADDR1 %0h RD_SIZE1 %0h RD_ADDR2_V %d RD_ADDR2 %0h RD_SIZE2 %0h @ %0t", MEM_DEP_STALL_OUT, RD_V, RD_ADDR1_V, RD_ADDR1, RD_SIZE1, RD_ADDR2_V, RD_ADDR2, RD_SIZE2, $time);
      $strobe("MEM_DEP_STALL %d ME_V %d ME_ADDR1_V %d ME_ADDR1 %0h ME_SIZE1 %0h ME_ADDR2_V %d ME_ADDR2 %0h ME_SIZE2 %0h @ %0t", MEM_DEP_STALL_OUT, ME_V, ME_ADDR1_V, ME_ADDR1, ME_SIZE1, ME_ADDR2_V, ME_ADDR2, ME_SIZE2, $time);
      $strobe("MEM_DEP_STALL %d EX_V %d EX_ADDR1_V %d EX_ADDR1 %0h EX_SIZE1 %0h EX_ADDR2_V %d EX_ADDR2 %0h EX_SIZE2 %0h @ %0t", MEM_DEP_STALL_OUT, EX_V, EX_ADDR1_V, EX_ADDR1, EX_SIZE1, EX_ADDR2_V, EX_ADDR2, EX_SIZE2, $time);
   end

endmodule

