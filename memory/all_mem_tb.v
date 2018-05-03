`timescale 1ns/1ps

module TOP;
    // Inputs
    reg clk;
    reg rst, set;
    reg [2:0] MY_ID;
    wire  [31:0] D;
    wire  [15:0] A;
    wire  [2:0] MASTER;
    wire  [2:0] DEST;
    wire  [11:0] SIZE;
    wire  RW;
   
    //interface with arbitrator
    wire BR;
    reg BG;
    wire ACK_OUT;
    reg   ACK_IN;
    reg 	  DEST_IN;
    wire 	  DEST_OUT;
   

    //interface with work unit
    reg MOD_EN; //simple signal saying we have a request
    reg MOD_WR;
    reg [15:0] MOD_A;
    reg [127:0] MOD_WRITE_DATA;
    wire [127:0] MOD_READ_DATA;
    wire MOD_R;

    integer half_cycle=10;
    integer clk_cycle=20;

    bus_controller u_bus_cntrl (//interface with bus
      clk,
      rst, set,
      D,
      A,
      SIZE,
      RW,
      BR,
      BG,
      ACK_OUT,
      ACK_IN,
      DEST_OUT,
      DEST_IN,
      MOD_EN,
      MOD_WR,
      MOD_A,
      MOD_WRITE_DATA,
      MOD_READ_DATA,
      MOD_R
    );

    reg size, rw, ack_v;
    reg [31:0] din;
    reg [15:0] addr;
    reg [2:0] master, dest;
    reg wr_size, wr_d, wr_a, wr_master, wr_dest, wr_RW, wr_ack;
    // inout signals
    // for using it as input, set wr_size to 1, and set size
    // for using it as output, set wr_size to 0 
    assign SIZE = wr_size?size:12'bz;
    assign D = wr_d?din:32'bz;
    assign A = wr_a?addr:16'bz;
    assign MASTER = wr_master?master:3'bz;
    assign DEST = wr_dest?dest:3'bz;
    assign RW = wr_RW?rw:1'bz;


    // By default, setting everything as output, change the wr signal for
    // making it input
    initial begin
        MOD_EN = 1'b0;
        MOD_A = 16'h0B;
        clk = 1'b0;
       
       rst = 1'b0;
       set = 1'b1;
       

        #(half_cycle)
        u_bus_cntrl.state_reg.Q = 16'h0001;
        rst = 1'b1;
       DEST_IN = 1'b1;
       MY_ID = 3'd5;
        wr_size = 1'b0;
        wr_d = 1'b1;
        wr_a = 1'b1;
        wr_master = 1'b1;
        wr_dest = 1'b1;
        wr_RW = 1'b1;
        wr_ack = 1'b0;
        size = 3'd4;
        dest = 3'd5;
        rw = 1'b1;
        din = 32'h1234_1234;
        addr = 16'hA000;
        ACK_IN = 1;
       
      //  ack_v = 1'b0;
        master = 3'd3;

       #(half_cycle-2)
        wr_size = 1'b1;
        size = 3'd4;

       # (3*clk_cycle)
        din = 32'hAAAA_AAAA;
       # (clk_cycle)
        din = 32'hBBBB_BBBB;

        #(2*clk_cycle)
       DEST_IN = 0;
               wr_size = 1'b0;
        wr_d = 1'b0;
        wr_a = 1'b0;
        wr_master = 1'b0;
        wr_dest = 1'b0;
        wr_RW = 1'b0;
        wr_ack = 1'b0;
       MOD_EN = 1;
       MOD_WR = 1;
       MOD_A = 16'hABC0;
       MOD_WRITE_DATA = 128'h11111111_22222222_33333333_44444444;
        BG = 1'b1;


       // #(2*clk_cycle)
       
        



    end

    always #(half_cycle) clk = ~clk;

    // Run simulation.  
    initial #(clk_cycle*30) $finish;

    // Dump all waveforms
    initial begin
        $vcdplusfile("bus_controller.dump.vpd");
        $vcdpluson(0, TOP); 
    end // initial begin

endmodule


