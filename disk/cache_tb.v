`timescale 1ns/1ps

module TOP;
    // Inputs
    reg clk, WE, EN, RST;
    reg [31:0] addr;
    reg [11:0] size;
    wire [32767:0] data_out;

    integer half_cycle=50;
    integer clk_cycle=100;

    disk u_disk (clk, addr, size, RST, WE, EN, data_out);


    initial begin
        clk = 1'b0;
        EN = 1'b1;
        WE = 1'b0;
        RST = 1'b0;
        addr = 32'h1FFF_FFFE;
//        addr = 32'h5;      
        size = 12'h4;
    $readmemh("ram0.list", u_disk.mem0);
    $readmemh("ram0.list", u_disk.mem1);
    $readmemh("ram0.list", u_disk.mem2);
    $readmemh("ram0.list", u_disk.mem3);
    $readmemh("ram0.list", u_disk.mem4);
    $readmemh("ram0.list", u_disk.mem5);
    $readmemh("ram0.list", u_disk.mem6);
    $readmemh("ram0.list", u_disk.mem7);

        forever #(half_cycle) clk = ~clk;
    end

    // Run simulation.  
    initial #(clk_cycle*5) $finish;

    always @(*) begin
        $display("DATA OUT: %h", data_out);
    end

    // Dump all waveforms
    initial begin
        $vcdplusfile("cache.dump.vpd");
        $vcdpluson(0, TOP); 
    end // initial begin

endmodule


