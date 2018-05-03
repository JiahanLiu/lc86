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

    integer half_cycle=8;
    integer clk_cycle=16;

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

        u_cache.tagstore_u.valid_store.Q = 32'h0000;
        u_cache.state.Q = 16'h0001;

    end


       parameter IDLE  = 16'b0000_0000_0000_0001,
	       RD = 16'b0000_0000_0000_0010,
	       RDHIT = 16'b0000_0000_0000_0100,
	       RDMISS = 16'b0000_0000_0000_1000,
	       RDEVICT = 16'b0000_0000_0001_0000,
	       WR = 16'b0000_0000_0010_0000,
	       WRHIT = 16'b0000_0000_0100_0000,
	       WRMISS = 16'b0000_0000_1000_0000,
	       WREVICT = 16'b0000_0001_0000_0000;


    // 16 byte cache, 32 cache lines
    reg [127:0] dcache [31:0];
    reg [6:0] tagcache [31:0];
    reg [31:0] valid;
    integer read_hit, read_miss, read_evict;
    integer write_hit, write_miss, write_evict;
    integer j;
    integer cycles = 0;

    wire [6:0] tag;
    wire [4:0] cache_line;
    wire [3:0] offset;

    assign cache_line = address[8:4];
    assign tag = address[15:9];
    assign offset =  address[3:0];
    integer seed;

    initial begin
        valid = 32'h0;
        clk = 1'b0;
        pre = 1'b1;
        clr = 1'b1;
        enable = 1'b1;
        read_hit = 0;
        read_miss = 0;
        write_hit = 0;
        write_miss =0;
        write_evict = 0;
        read_evict = 0;
        seed =0;

        for(j=0; j<32; j=j+1) begin
            dcache[j] = 128'b0;
            tagcache[j] = 7'h0;
        end
        
   end
 

    initial begin
        #(half_cycle-2);
        forever begin
            cycles = cycles+1;
            wait(u_cache.current_state === IDLE);     
            address[15] = 0;
            address[8:4] = {$random(seed)%20};
            address[14:9] = {$random(seed)%10};
            address[3:0] = {$random(seed)};

            if(offset == 4'd15)
                size = 1;
            else if(offset < 4'd15 && offset >= 4'd13)
                size = (cycles%2)+1;
            else if(offset < 4'd13 && offset >= 4'd9)
                size = 4;       //1, 2, or 4
            else if(offset < 4'd9 && offset >= 4'd1)
                size = 8;        // 1, 2, 4, 8
            else if(offset == 4'd0)
                size = 16;      //1, 2, 4, or 16

            RW = cycles%2;

            #2
            if(!valid[cache_line]) begin
                if(RW===1) begin
                    write_miss = write_miss+1;
                    $display("Write miss at time %0d", $time);
                    wait(u_cache.current_state === WRMISS);
                    #2;
                    BUS_READ = {$random(seed)};
                    BUS_R = 1;
                    dcache[cache_line] = BUS_READ;
                    tagcache[cache_line] = tag;
                    valid[cache_line] = 1;
                end else begin
                    read_miss = read_miss+1;
                    $display("Read miss at time %0d", $time);
                    wait(u_cache.current_state === RDMISS);
                    #2;
                    BUS_READ = {$random(seed)};
                    BUS_R = 1;
                    valid[cache_line] = 1;
                    wait(u_cache.current_state === RDHIT);
                    #2;
                    dcache[cache_line] = BUS_READ;
                    tagcache[cache_line] = tag;
                    if(BUS_READ !== data_read) 
                        $display("Read error at time %0d, data_read: %h, BUS_READ: %h", $time, data_read, BUS_READ);
                end
            end 
            
            else if(valid[cache_line] && tag === tagcache[cache_line]) begin
                if(RW == 1) begin
                    write_hit = write_hit+1;
                    $display("Write hit at time %0d", $time);
                    wait(u_cache.current_state === WRHIT);
                    #2;
                    if(size==0)
                        dcache[cache_line] = data_write;
                    else if(size==1)
                        dcache[cache_line][offset] = data_write[7:0];
                    else if(size==2) begin
                        dcache[cache_line][offset+1] = data_write[15:8];
                        dcache[cache_line][offset] = data_write[7:0];
                    end else if(size==4) begin
                        dcache[cache_line][offset+3] = data_write[31:24];
                        dcache[cache_line][offset+2] = data_write[23:16];
                        dcache[cache_line][offset+1] = data_write[15:8];
                        dcache[cache_line][offset] = data_write[7:0];
                    end else if(size==8) begin
                        dcache[cache_line][offset+7] = data_write[63:56];
                        dcache[cache_line][offset+6] = data_write[55:48];
                        dcache[cache_line][offset+5] = data_write[47:40];
                        dcache[cache_line][offset+4] = data_write[39:32];
                        dcache[cache_line][offset+3] = data_write[31:24];
                        dcache[cache_line][offset+2] = data_write[23:16];
                        dcache[cache_line][offset+1] = data_write[15:8];
                        dcache[cache_line][offset+0] = data_write[7:0];
                    end


                    valid[cache_line] = 1;
                end else begin
                    read_hit = read_hit+1;
                    $display("Read hit at time %0d", $time);
                    wait(u_cache.current_state === RDHIT);
                    #2;
                    if(dcache[cache_line] !== data_read) 
                        $display("Read error at time %0d, data_read: %h, my_data: %h", $time, data_read, dcache[cache_line]);
                    valid[cache_line] = 1;
                end
            end
            
            else if(valid[cache_line] && tag !== tagcache[cache_line]) begin
                if(RW==1) begin
                    write_evict = write_evict+1;
                    write_miss = write_miss+1;
                    $display("Write evict at time %0d", $time);
                    wait(u_cache.current_state === WREVICT);
                    #2;
                    BUS_R = 1;
                    $display("Write evict at time %0d", $time);
                    wait(u_cache.current_state === WRMISS);
                    #2;
                    BUS_READ = {$random(seed)};
                    dcache[cache_line] = BUS_READ;
                    tagcache[cache_line] = tag;
                    valid[cache_line] = 1;
                    $display("Write evict at time %0d", $time);
                end else begin
                    read_evict = read_evict+1;
                    read_miss = read_miss+1;
                    $display("Read evict at time %0d, tag: %h", $time, tag);
                    $display("Read evict tagcache %0d, cache_line: %h", tagcache[cache_line], cache_line);
                    wait(u_cache.current_state === RDEVICT);
                    #2;
                    BUS_R = 1;
                    wait(u_cache.current_state === RDMISS);
                    #2;
                    BUS_READ = {$random(seed)};
                    valid[cache_line] = 1;
                    wait(u_cache.current_state === RDHIT);
                    #2;
                    dcache[cache_line] = BUS_READ;
                    tagcache[cache_line] = tag;
                    if(BUS_READ !== data_read) 
                        $display("Read error at time %0d, data_read: %h, BUS_READ: %h", $time, data_read, BUS_READ);
                end
            end
        end
    end

                
    always #(half_cycle) clk = ~clk;

    // Run simulation.  
    initial begin
        #(clk_cycle*5000) 
        $display("READ_MISS = %0d", read_miss);
        $display("READ_HIT = %0d", read_hit);
        $display("READ_EVICT = %0d", read_evict);
        $display("WRITE_MISS = %0d", write_miss);
        $display("WRITE_HIT = %0d", write_hit);
        $display("WRITE_EVICT = %0d", write_evict);
        $display("Cycles = %0d", cycles);
        
        $finish;
    end

    // Dump all waveforms
    initial begin
        $vcdplusfile("cache.dump.vpd");
        $vcdpluson(0, TOP); 
    end // initial begin

endmodule


