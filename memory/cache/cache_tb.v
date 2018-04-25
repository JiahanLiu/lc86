`timescale 1ns/1ps

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

    integer half_cycle=50;
    integer clk_cycle=100;

    cache u_cache (clk, pre, clr, 
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


    // Cache values (same values for addr[2:0]):
    // 000 -> 128'h000000..
    // 001 -> 128'h010101..
    // 010 -> 128'h020202..
    // 011 -> 128'h030303..
    // ...
    initial begin
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram0.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram1.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram2.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram3.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram4.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram5.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram6.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram7.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram8.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram9.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram10.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram11.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram12.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram13.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram14.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line0.ram15.mem);

        $readmemh("ram0.list", u_cache.data_u.data_line1.ram0.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram1.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram2.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram3.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram4.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram5.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram6.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram7.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram8.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram9.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram10.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram11.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram12.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram13.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram14.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line1.ram15.mem);

        $readmemh("ram0.list", u_cache.data_u.data_line2.ram0.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram1.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram2.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram3.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram4.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram5.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram6.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram7.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram8.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram9.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram10.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram11.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram12.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram13.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram14.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line2.ram15.mem);

        $readmemh("ram0.list", u_cache.data_u.data_line3.ram0.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram1.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram2.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram3.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram4.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram5.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram6.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram7.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram8.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram9.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram10.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram11.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram12.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram13.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram14.mem);
        $readmemh("ram0.list", u_cache.data_u.data_line3.ram15.mem);

        $readmemh("tag_ram0.list", u_cache.tagstore_u.u_tag_ram0.mem);
        $readmemh("tag_ram0.list", u_cache.tagstore_u.u_tag_ram1.mem);
        $readmemh("tag_ram0.list", u_cache.tagstore_u.u_tag_ram2.mem);
        $readmemh("tag_ram0.list", u_cache.tagstore_u.u_tag_ram3.mem);

        u_cache.tagstore_u.valid_store.Q = 32'h00FF;
        u_cache.state.Q = 16'h0001;

    end

    initial begin
        clk = 1'b0;
        pre = 1'b1;
        clr = 1'b1;

        // Cache tests:
        // One read
        // One write
        // Write hit, write miss
        // Read hit, read miss
        
        // Write
        #(half_cycle-2)
        enable = 1;
        address = 16'h000A;
        data_write = 16'h1234;
        RW = 1;

        // Read
        #(2*clk_cycle-2)
        enable = 1;
        address = 16'h000A;
        data_write = 16'h5634;
        RW = 0;

        //Write miss
        #(2*clk_cycle-2)
        enable = 1;
        address = 16'h010A;
        data_write = 16'h5634;
        RW = 1;

        // Write hit
        #(2*clk_cycle-2)
        enable = 1;
        address = 16'h010A;
        data_write = 16'h5634;
        RW = 1;
        
        // Read miss
        #(2*clk_cycle-2)
        enable = 1;
        address = 16'h010B;
        data_write = 16'h5634;
        RW = 0;        

        // Read hit
        #(2*clk_cycle-2)
        enable = 1;
        address = 16'h010A;
        data_write = 16'h5634;
        RW = 0;
    end

    always #(half_cycle) clk = ~clk;

    // Run simulation.  
    initial #(clk_cycle*30) $finish;

    // Dump all waveforms
    initial begin
        $vcdplusfile("cache.dump.vpd");
        $vcdpluson(0, TOP); 
    end // initial begin

endmodule


