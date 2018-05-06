`timescale 1ns/1ps

module TOP;
    // Inputs
    reg [14:0] addr;
    reg WR, en;
    reg [2:0] write_size;
    wire [255:0] data_buf;

    integer half_cycle=10;
    integer clk_cycle=20;

    reg wr_data;
    reg [255:0] data;
    assign data_buf = wr_data?data:256'bz;

    main_memory u_main_memory (
        addr, 
        WR, en,
        write_size,
        data_buf
    );

    initial begin
        write_size = 3'd2;
        wr_data = 1'b1;
        WR = 1'b1;
        addr = 15'hA;
        data = 128'h98435334;

        #274
        wr_data = 1'b0;

        #26
        write_size = 3'd3;
        WR = 1'b0;

        #1
        addr = 15'h80;
        data = 128'h1276976975;

        #26
        WR = 1'b1;
        wr_data = 1'b1;

        #200
        wr_data = 1'b0;
        
        #26
        WR = 1'b0;

        #1 
        addr = 15'hA;

        #1
        addr = 15'h80;

        #2
        $finish;
    end


    // Run simulation.  
//    initial #(clk_cycle*30) $finish;

    always@(data_buf)
        $display("DIO: %h at time %0d", data_buf, $time);

    // Dump all waveforms
    initial begin
        $vcdplusfile("main_memory.dump.vpd");
        $vcdpluson(0, TOP); 
    end // initial begin

endmodule


