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
    wire  ACK;
    //interface with arbitrator
    wire BR;
    reg BG;
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
      MY_ID,
      D,
      A,
      MASTER,
      DEST,
      SIZE,
      RW,
      ACK,
      BR,
      BG,
      MOD_EN,
      MOD_WR,
      MOD_A,
      MOD_WRITE_DATA,
      MOD_READ_DATA,
      MOD_R
    );

    wire ACK_IN;

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
    assign ACK = wr_ack?ack_v:1'bz;

    assign ACK_IN = ACK;

    // By default, setting everything as output, change the wr signal for
    // making it input
    initial begin
        MOD_EN = 1'b0;
        MOD_A = 16'h0B;
        clk = 1'b0;
        u_bus_cntrl.state_reg.Q = 16'h0001;


        #(half_cycle)
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
        rw = 1'b0;
        din = 32'h1234_1234;
        addr = 16'hA;
      //  ack_v = 1'b0;
        master = 3'd3;

//        #(half_cycle-2)
//        wr_size = 1'b0;
//        wr_d = 1'b0;
//        wr_a = 1'b0;
//        wr_master = 1'b0;
//        wr_dest = 1'b0;
//        wr_RW = 1'b0;
//        wr_ack = 1'b0;


        #(half_cycle-2)
        wr_size = 1'b1;
        size = 3'd4;

        #(2*clk_cycle)
        BG = 1'b1;
        



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


