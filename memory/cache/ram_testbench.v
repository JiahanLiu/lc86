module TOP;

reg [2:0] A;
reg [7:0] DIN;
reg WR, OE;
wire [7:0] DOUT;
reg clk;

ram8b8w$ u_ram (A, DIN, WR, OE, DOUT);

// Cache values (same values for addr[2:0]):
// 000 -> 128'h000000..
// 001 -> 128'h010101..
// 010 -> 128'h020202..
// 011 -> 128'h030303..
// ...

initial begin
    $readmemh("ram0.list", u_ram.mem);
end

initial begin
    clk = 1'b0;

    #3
    WR = 1'b0;
//    DIN = 8'hAA;
    A = 3'd3;
    OE = 1'b1;

    #8
    WR = 1'b1;
    DIN = 8'h1A;
    A = 3'd3;
    OE = 1'b1;

    #5
    WR = 1'b0;
    A = 3'd3;
    DIN = 8'hAA;
    OE = 1'b1;

end

always #5 clk = ~clk;

initial #80 $finish;

initial begin 
    $vcdplusfile("ram.dump.vpd");
    $vcdpluson(0, TOP);
end

always @(DOUT) begin
    $display("Time: %0d, DOUT = %h", $time, DOUT);
end

endmodule
