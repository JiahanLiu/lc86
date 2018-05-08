`timescale 1ns/1ps

module TOP;
    // Inputs
    reg clk;
    reg rst, set;
   
   //interface with dcache
    reg DC_EN; //simple signal saying we have a request
    reg DC_WR;
    reg [15:0] DC_A;
    reg [127:0] DC_WRITE_DATA;
    wire [127:0] DC_READ_DATA;
    wire DC_R;

   //interface with icache
       reg IC_EN; //simple signal saying we have a request
    reg IC_WR;
    reg [15:0] IC_A;
    reg [127:0] IC_WRITE_DATA;
    wire [127:0] IC_READ_DATA;
    wire IC_R;

   //interface with interrupt
   reg 	 INTR_EN; //simple signal saying we have a request
    reg INTR_WR;
    reg [15:0] INTR_A;
    reg [127:0] INTR_WRITE_DATA;
    wire [127:0] INTR_READ_DATA;
    wire INTR_R;


    integer half_cycle=16;
    integer clk_cycle=32;
    

   FULL_MEMORY full_memory_u(
			     DC_EN,
			     DC_WR,
			     DC_A,
			     DC_WRITE_DATA,
			     DC_READ_DATA,
			     DC_R,
   
			     IC_EN, 
			     IC_WR,
			     IC_A,
			     IC_WRITE_DATA,
			     IC_READ_DATA,
			     IC_R,

			     //not used yet
			     INTR_EN,
			     INTR_WR,
			     INTR_A,
			     INTR_WRITE_DATA,
			     INTR_READ_DATA,
			     INTR_R,


			     //The Bus clock and other signals
			     clk,
			     rst, set);



    // By default, setting everything as output, change the wr signal for
    // making it input
    initial begin
       DC_EN = 1'b0;
       DC_A = 16'hA000;
       DC_WR = 1'b1;
       IC_EN = 1'b0;
       IC_A = 16'hA000;
       IC_WR = 1'b0;
       IC_WRITE_DATA= 128'hFEED_BEEF;
       DC_WRITE_DATA= 128'hABCD_1234;
       clk = 1'b0;
       rst = 1'b0;
       set = 1'b1;
       

        #(half_cycle)
        //u_bus_cntrl.state_reg.Q = 16'h0001;
        rst = 1'b1;


       #(clk_cycle -2)
       DC_EN = 1'b1;
       IC_EN = 1'b1;

       # (clk_cycle * 12)
       DC_EN = 1'b0;
              
       # (clk_cycle * 8)
       DC_EN = 1'b0;
       IC_EN = 1'b0;
       

       
         //     #(half_cycle-2)
    //    wr_size = 1'b1;
      //  size = 3'd4;

  //     # (3*clk_cycle)
//        din = 32'hAAAA_AAAA;
    //   # (clk_cycle)
//        din = 32'hBBBB_BBBB;

      //  #(2*clk_cycle)
//       DEST_IN = 0;
//               wr_size = 1'b0;
//        wr_d = 1'b0;
//        wr_a = 1'b0;
//        wr_master = 1'b0;
//        wr_dest = 1'b0;
//        wr_RW = 1'b0;
//        wr_ack = 1'b0;
//       MOD_EN = 1;
//       MOD_WR = 1;
//       MOD_A = 16'hABC0;
//       MOD_WRITE_DATA = 128'h11111111_22222222_33333333_44444444;
//        BG = 1'b1;


       // #(2*clk_cycle)
       
        



    end

    always #(half_cycle) clk = ~clk;

    // Run simulation.  
    initial #(clk_cycle*30) $finish;

    // Dump all waveforms
    initial begin
       $vcdplusfile("all_mem.dump.vpd");
        $vcdpluson(0, TOP); 
    end // initial begin

endmodule


