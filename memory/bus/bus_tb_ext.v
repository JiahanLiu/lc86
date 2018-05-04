`timescale 1ns/1ps

module TOP;
    // Inputs
    reg clk;
    reg rst, set;
    wire  [31:0] D;
    wire  [15:0] A;
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

    integer half_cycle=20;
    integer clk_cycle=40;

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
    reg wr_size, wr_d, wr_a, wr_RW, wr_ack;
    // inout signals
    // for using it as input, set wr_size to 1, and set size
    // for using it as output, set wr_size to 0 
    assign SIZE = wr_size?size:12'bz;
    assign D = wr_d?din:32'bz;
    assign A = wr_a?addr:16'bz;
    assign RW = wr_RW ?rw:1'bz;

    integer cycles=0;
    integer seed=0;
    integer n_ST_BR, n_MSTR, n_SLV, n_ST_WR, n_ST_RD;

    parameter IDLE  = 8'b0000_0001,
        ST_BR  = 8'b0000_0010,
        MSTR = 8'b0000_0100,
        ST_WR = 8'b0000_1000,
        SLV = 8'b0001_0000,
        ST_RD = 8'b0010_0000;

    initial begin
        #(half_cycle+clk_cycle-2);
        forever begin
            cycles = cycles+1;
            
            $display("Waiting for IDLE state at time %0d", $time);
            wait(u_bus_cntrl.current_state === IDLE);
            #5
            ACK_IN = 1'b0;
            din = {$random(seed)};
            wr_a = 1'b1;
            wr_d = 1'b1;
            addr[15] = 0;
            addr[14:0] = {$random(seed)};
            MOD_EN = {$random(seed)%2};
            MOD_WR = {$random(seed)%2};
            wr_RW = 1'b1;
            wr_size = 1'b1;
            MOD_WRITE_DATA = {$random(seed)};
            rw = {$random(seed)%2};

            if(MOD_EN) begin
                DEST_IN = 1'b0;
                $display("Waiting for ST_BR at time %0d", $time);
                n_ST_BR = n_ST_BR +1;
                wait(u_bus_cntrl.current_state === ST_BR);
                #5;
                BG = {$random(seed)%2};
            
                if(BG) begin
                    $display("Waiting for MSTR at time %0d", $time);
                    n_MSTR = n_MSTR +1;
                    wait(u_bus_cntrl.current_state === MSTR);
                    #5;
                    wr_RW = 1'b0;
                    wr_size = 1'b0;
                    ACK_IN = 1'b1;
                    #1;
                    if(MOD_WR===1'b1) begin
                        $display("Waiting for ST_WR at time %0d", $time);
                        n_ST_WR = n_ST_WR+1;
                        wait(u_bus_cntrl.current_state === ST_WR);
                        #5;
                    end 
                end

                else begin
                    DEST_IN = 1'b1;
                    $display("Waiting for SLV at time %0d", $time);
                    n_SLV = n_SLV +1;
                    wait(u_bus_cntrl.current_state === SLV);
                    #5;
                    if(rw===1'b1) begin
                        $display("Waiting for ST_RD after SLV at time %0d", $time);
                        n_ST_RD = n_ST_RD +1;
                        wait(u_bus_cntrl.current_state ===ST_RD);
                        #5;
                        wait(u_bus_cntrl.DONE);
                        if(MOD_READ_DATA !== D) 
                            $display("Read data error at time %0d, MOD_READ_DATA = %h, D = %h", $time, MOD_READ_DATA, D);
                        if(MOD_A !== A) 
                            $display("Read address error at time %0d", $time);
                    end
                end    
            end     // MOD_EN end
            
            else if(!MOD_EN) begin
                // Setting dest to myid to check the ack state
                DEST_IN = 1'b1;
                $display("Waiting for SLV, !MOD_EN at time %0d", $time);
                n_SLV = n_SLV +1;
                wait(u_bus_cntrl.current_state === SLV);
                if(rw===1'b1) begin
                    $display("Waiting for ST_RD after SLV at time %0d", $time);
                    n_ST_RD = n_ST_RD +1;
                    wait(u_bus_cntrl.current_state === ST_RD);
                end
            end
        end
    end

        
    // By default, setting everything as output, change the wr signal for
    // making it input
    initial begin
        MOD_EN = 1'b0;
        MOD_A = 16'h0B;
        clk = 1'b0;
        rst = 1'b0;
        set = 1'b1;
        n_ST_BR=0;
        n_MSTR=0;
        n_SLV=0;
        n_ST_WR=0;
        n_ST_RD=0;

        #(half_cycle)
        rst = 1'b1;
        size = 12'b0;
        wr_size = 1'b1;
        u_bus_cntrl.state_reg.Q = 16'h0001;
        wr_RW = 1'b1;
        rw = {$random(seed)%2};
        BG = 1'b0;
        ACK_IN = 1'b1;
        DEST_IN = 3'd4;
    end
       

//        wr_size = 1'b0;
//        wr_d = 1'b1;
//        wr_a = 1'b1;
//        wr_RW = 1'b1;
//        wr_ack = 1'b0;
//        size = 3'd4;
//        rw = 1'b1;
//        din = 32'h1234_1234;
//        addr = 16'hA000;
//        ACK_IN = 1;
//       
//       #(half_cycle-2)
//        wr_size = 1'b1;
//        size = 3'd4;
//
//       # (3*clk_cycle)
//        din = 32'hAAAA_AAAA;
//       # (clk_cycle)
//        din = 32'hBBBB_BBBB;
//
//        #(2*clk_cycle)
//               wr_size = 1'b0;
//        wr_d = 1'b0;
//        wr_a = 1'b0;
//        wr_RW = 1'b0;
//        wr_ack = 1'b0;
//       MOD_EN = 1;
//       MOD_WR = 1;
//       MOD_A = 16'hABC0;
//       MOD_WRITE_DATA = 128'h11111111_22222222_33333333_44444444;
//        BG = 1'b1;




    always #(half_cycle) clk = ~clk;

    // Run simulation.  
    initial begin 
        #(clk_cycle*500);
        $display("Cycles :%0d", cycles);
        $display("n_ST_WR :%0d", n_ST_WR);
        $display("n_ST_BR :%0d", n_ST_BR);
        $display("n_ST_RD :%0d", n_ST_RD);
        $display("n_MSTR :%0d", n_MSTR);
        $display("n_SLV :%0d", n_SLV);
        $finish;
    end

    // Dump all waveforms
    initial begin
        $vcdplusfile("bus_controller.dump.vpd");
        $vcdpluson(0, TOP); 
    end // initial begin

endmodule


