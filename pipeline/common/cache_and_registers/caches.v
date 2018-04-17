// caches.v
`define half_cycle 50

/* 
Q: Should I use the SRAM module for the cache or can I use the RAM module?
A: Please use SRAM parts for main memory and RAM parts for the cache.
 
// ram8b8w$             8-bits x 8 words RAM
// ram8b4w$             8-bits x 4 words RAM

module  ram8b8w$ (A,DIN,OE,WR, DOUT);
module  ram16b8w$ (A, DIN, OE, WRH, WRL, DOUT);
 
Cache Line Size = 16 Bytes (128-bits) 
Physically Indexed, Physically Tagged (PIPT) 
 to avoid invalidate on context switch
*/
module icache (CLK, RST, PADDR, R, DOUT);
   input CLK, RST;
   input [31:0] PADDR;  // Physical Address
   
   output 	R;      // Ready Signal
   output [127:0] DOUT; // 16B output

   // Temporary behavioral constructs
   reg [31:0] 	  paddr_temp;
   
   reg [127:0] 	  data_store [0:31]; // 512B total
   reg [127:0]	  current_data;

   reg [31:0] 	  tag_store [0:31]; 

   reg 		  tag_match;
   reg [4:0] 	  i;
   reg 		  ready;
   
   initial
     begin
	$readmemh("icache_data_store.list", data_store);
	$readmemh("icache_tag_store.list", tag_store);
     end

   always @(posedge CLK)
     paddr_temp = PADDR;
       
   always @(paddr_temp)
     begin
	tag_match = 1'b0;
	ready = 1'b0;
	
	for (i = 0; i < 32; i++)
	  begin
	     if (tag_store[i][31:4] == paddr_temp[31:4])
	       tag_match = 1'b1;
	  end
     end

   always @(posedge tag_match)
     begin
	current_data = data_store[i];

	$strobe("at time %0d, icache read %x: %x\n", $time, paddr_temp, current_data);
	
	#(`half_cycle*3)

	ready = 1'b1;
     end
   
   assign DOUT = current_data;
   assign R = ready;
   
endmodule // icache

module dcache (CLK, RST, PADDR, DIN, SIZE, WE, R, DOUT);
   input CLK, RST;
   
   input [31:0] PADDR;  // Physical Address
   input [63:0] DIN;    // always 64-bit input
   input [2:0] 	SIZE;   // number of bytes
   input 	WE;     // write enable
   
   output 	R;      // Ready Signal
   output [63:0] DOUT;  // always 64-bit output

   // Temporary behavioral constructs
   reg [31:0] 	  paddr_temp;
   reg [63:0] 	  din_temp;
   reg [2:0] 	  size_temp;
   reg 		  we_temp; 	  
   
   reg [7:0] 	  data_store [0:511]; // 512B total
   reg [63:0]	  current_data;

   reg [31:0] 	  tag_store [0:31]; 

   reg 		  tag_match;
   reg [4:0] 	  i;
   reg 		  ready;
   
   initial
     begin
	$readmemh("dcache_data_store.list", data_store);
	$readmemh("dcache_tag_store.list", tag_store);
     end

   always @(posedge CLK)
     begin
	paddr_temp = PADDR;
	din_temp = DIN;
	size_temp = size;
	we_temp = WE;
     end
       
   always @(paddr_temp, din_temp, size_temp, we_temp)
     begin
	tag_match = 1'b0;
	ready = 1'b0;

	for (i = 0; i < 32; i++)
	  begin
	     if (tag_store[i][31:4] == paddr_temp[31:4])
	       tag_match = 1'b1;
	  end	
     end

   always @(posedge tag_match)
     begin
	if (WE == 1'b0)
	  begin
	     case (size_temp)
	       1: begin
		  current_data[7:0] = data_store[i<<4][7:0];
		  $strobe("at time %0d, dcache read size 1", $time);
	       end
	       2: begin
		  current_data[7:0] = data_store[i<<4][7:0];
		  current_data[15:8] = data_store[(i<<4)+1][7:0];
		  $strobe("at time %0d, dcache read size 2", $time);
	       end
	       4: begin
		  current_data[7:0] = data_store[i<<4][7:0];
		  current_data[15:8] = data_store[(i<<4)+1][7:0];
		  current_data[23:16] = data_store[(i<<4)+2][7:0];
		  current_data[31:24] = data_store[(i<<4)+3][7:0];
		  $strobe("at time %0d, dcache read size 4", $time);
	       end	       
	       8: begin
		  current_data[7:0] = data_store[i<<4][7:0];
		  current_data[15:8] = data_store[(i<<4)+1][7:0];
		  current_data[23:16] = data_store[(i<<4)+2][7:0];
		  current_data[31:24] = data_store[(i<<4)+3][7:0];
		  current_data[39:32] = data_store[i<<4+4][7:0];
		  current_data[47:40] = data_store[(i<<4)+5][7:0];
		  current_data[55:48] = data_store[(i<<4)+6][7:0];
		  current_data[63:56] = data_store[(i<<4)+7][7:0];
		  $strobe("at time %0d, dcache read size 8", $time);
	       end
	     endcase // case (size_temp)
	     
	     $strobe(", data %x: %x\n", paddr_temp, current_data);
	     
	     #(`half_cycle*3)
	     
	     ready = 1'b1;
	  end // if (WE == 1'b0)
	
	else
	  begin
	     $strobe("at time %0d, dcache write data %x: %x", $time, paddr_temp, din_temp);
	     case (size_temp)
	       1: begin
		  data_store[i<<4][7:0] = din_temp[7:0];
		  $strobe(", size 1\n", $time);
	       end
	       2: begin
		  data_store[i<<4][7:0] = din_temp[7:0];
		  data_store[(i<<4)+1][7:0] = din_temp[15:8];
		  $strobe(", size 2\n", $time);  
	       end
	       4: begin
		  data_store[i<<4][7:0] = din_temp[7:0];
		  data_store[(i<<4)+1][7:0] = din_temp[15:8];
		  data_store[(i<<4)+2][7:0] = din_temp[23:16];
		  data_store[(i<<4)+3][7:0] = din_temp[31:24];
		  $strobe(", size 4\n", $time);
	       end	       
	       8: begin
		  data_store[i<<4][7:0] = din_temp[7:0];
		  data_store[(i<<4)+1][7:0] = din_temp[15:8];
		  data_store[(i<<4)+2][7:0] = din_temp[23:16];
		  data_store[(i<<4)+3][7:0] = din_temp[31:24];
		  data_store[i<<4+4][7:0] = din_temp[39:32];
		  data_store[(i<<4)+5][7:0] = din_temp[47:40];
		  data_store[(i<<4)+6][7:0] = din_temp[55:48];
		  data_store[(i<<4)+7][7:0] = din_temp[63:56];
		  $strobe(", size 8\n", $time);
	       end
	     endcase // case (size_temp)
	     
	     #(`half_cycle*5)
	     
	     ready = 1'b1;
	  end   
     end
   
   assign DOUT = current_data;
   assign R = ready;
   
endmodule // dcache
