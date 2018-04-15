/*
module cross_cache_line (
   input [3:0] offset,
   input [1:0] size,

   output cross_cl
);

   wire and0_out, and1_out, and2_out, and3_out, and4_out,
	and5_out, and6_out;

   wire or0_out, or1_out, or2_out;
   
   // cross_cl = offset[3] & ( (offset[2]&size[1]&size[0] || offset[0]&size[1]&size[0] || offset[1]&size[1]&size[0] || offset[2]&offset[0]&size[1])
   //              || (offset[2]&offset[1]&offset[0]&size[0] || offset[2]&offset[1]&size[1] ) )
    
   // delay: and4$ + or2$ + or2$ + and2$
   // or = and3$ + or4$ + or2$ + and2$
   

   and3$
     and0 (and0_out, offset[2], size[1], size[0]),
     and1 (and1_out, offset[1], size[1], size[0]),
     and2 (and2_out, offset[0], size[1], size[0]),
     and3 (and3_out, offset[2], offset[0], size[1]);
   or4$
     or0 (or0_out, and0_out, and1_out, and2_out, and3_out);

   and4$
     and4 (and4_out, offset[2], offset[1], offset[0], size[0]);
   and3$
     and5 (and5_out, offset[2], offset[1], size[1]);
   or2$
     or1 (or1_out, and4_out, and5_out);

   or2$
     or2 (or2_out, or0_out, or1_out);
   and2$
     and6 (and6_out, offset[3], or2_out);

   assign cross_cl = and6_out;
   
endmodule
*/
 
module lsu (
   input CLK, RST, LA_V,

   input [31:0] LA_RD_ADDR, LA_WR_ADDR,
   input [1:0] LA_RD_SIZE, LA_WR_SIZE,

   output [31:0] RA_RD_ADDR,
   output [1:0] RA_RD_SIZE
);

   wire [31:0] la_rd_addr_end, la_wr_addr_end;

   wire [23:0] rd_addr_entry, rd_addr_end_entry,
               wr_addr_entry, wr_addr_end_entry;

   wire rd_addr_match, rd_addr_end_match,
        wr_addr_match, wr_addr_end_match;

   tlb dtlb (LA_RD_ADDR[31:12], la_rd_addr_end[31:12], LA_WR_ADDR[31:12], la_wr_addr_end[31:12],
             rd_addr_entry, rd_addr_end_entry, wr_addr_entry, wr_addr_end_entry,
             rd_addr_match, rd_addr_end_match, wr_addr_match, wr_addr_end_match);

   initial
      begin
         $monitor("LA_RD_ADDR:%h LA_WR_ADDR:%h rd_entry:%h rd_end_entry:%h wr_entry:%h wr_end_entry:%h rd_match:%h rd_end_match:%h wr_match:%h wr_end_match:%h @ %0t", LA_RD_ADDR, LA_WR_ADDR, rd_addr_entry, rd_addr_end_entry, wr_addr_entry, wr_addr_end_entry, rd_addr_match, rd_addr_end_match, wr_addr_match, wr_addr_end_match, $time);
      end  

   reg state;

//   initial
//      begin
//         state = 0;
//      end

/* general protection exception: write a read only page
   page fault exception: page not in TLB OR page not present

   if cross 16B boundary, need to get two cache lines
   if cross page boundary, still only need to get two cache lines
      second addr always ends in 12'h000, data_size changes
*/
//   always @(posedge CLK)
//      begin
//         if (state == 0) begin
	    
//         end
endmodule

