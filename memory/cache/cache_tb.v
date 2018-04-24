`timescale 1ns/1ps
`define half_cycle 50
`define clk_cycle 100

module TOP;
    // Inputs
    reg clk, pre, clr;
	reg [127:0] data_write;
	reg RW;
	reg enable;
	reg [15:0] address;
	reg [3:0] size;
	reg BUS_R;
	reg [127:0] BUS_READ;

    // Outputs
	wire [127:0] data_read;
	wire ready;
	wire BUS_WR;
	wire BUS_EN;
	wire [15:0] BUS_ADDR;
	wire [127:0] BUS_WRITE;


    always @(posedge clk)

    cache dcache (clk, pre, clr, 
        data_write,
        RW,
        enable,
        address,
        size,
        data_read,
        ready,
        BUS_WR,
        BUS_EN,
        BUS_ADDR,
        BUS_WRITE,
        BUS_R,
        BUS_READ
    );

    initial begin
        clk = 1'b0;
        pre = 1'b1;
        clr = 1'b1;

        #(half_cycle-2)
        enable = 1;
        address = 16'h000A;
        data_write = 16'h1234;
        RW = 1;
        
        // Cache tests:
        // One read
        // One write
        // Both at the same time
        // Multiple reads
        // Multiple writes 
        // Cache thrashing
        //
    end

    always #(`half_cycle) clk = ~clk;

    // Run simulation.  
    initial #(`clk_cycle*10) $finish;

    // Dump all waveforms
    initial begin
        $vcdplusfile("cache.dump.vpd");
        $vcdpluson(0, TOP); 
    end // initial begin

endmodule


