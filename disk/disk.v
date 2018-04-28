module disk (
    input clk,
    input [31:0] addr, 
    // Size is from 0 to (2^12)-1
    input [11:0] size,  
    input RST,
    input WE,
    input EN, 
    output [32767:0] data_out
);

parameter
    IDLE = 0,
    READ = 1,
    READ_SPLIT = 2;

reg [7:0] mem0 [2**29-1:0];          //[28:0]
reg [7:0] mem1 [2**29-1:0];          //[28:0]
reg [7:0] mem2 [2**29-1:0];          //[28:0]
reg [7:0] mem3 [2**29-1:0];          //[28:0]
reg [7:0] mem4 [2**29-1:0];          //[28:0]
reg [7:0] mem5 [2**29-1:0];          //[28:0]
reg [7:0] mem6 [2**29-1:0];          //[28:0]
reg [7:0] mem7 [2**29-1:0];          //[28:0]

reg [32767:0] data, data_start, data_end, data_updt1, data_updt2;
reg [31:0] addr_updt;
wire [31:0] addr_end;
reg [31:0] addr_read_start, addr_read_end;
reg [1:0] STATE, NEXT_STATE;
reg read;
integer i, j;
reg split;

assign data_out = (EN && !WE) ? (data_updt1 | data_updt2) : 32768'bz;

assign addr_end = addr+size;
assign unaligned = (addr_end[29]!=addr[29])?1'b1:1'b0;
// For Split Access
wire [31:0] addr_split_end = {addr[31:29], 29'h1FFF_FFFF};

initial begin
    STATE = IDLE;
    NEXT_STATE = IDLE;
end

always @(posedge clk) begin : disk_ctrl
    STATE = NEXT_STATE;
    if(RST)
        STATE <= IDLE;
    else begin
        case(STATE)
            IDLE: begin
                if(EN && !WE) begin 
                    NEXT_STATE <= READ;
                end  
                read <= 0;
                split <= 0;
            end

            READ: begin
                data_start <= 0;
                split <= 0;
                if(!unaligned) begin
                    NEXT_STATE <= IDLE;
                    read <= 1;
                    addr_read_start <= addr;
                    addr_read_end <= addr_end;
                    data_end <= addr_end-addr;
                end else begin
                    NEXT_STATE <= READ_SPLIT;
                    read <= 1;
                    addr_read_start <= addr;
                    addr_read_end <= addr_split_end;
                    data_end <= addr_split_end-addr;
                end
            end

            READ_SPLIT: begin
                read <= 1;
                NEXT_STATE <= IDLE;
                addr_read_start <= addr_split_end+1;
                addr_read_end <= addr_end;
                data_start <= data_end+1;
                data_end <= addr_end-addr_split_end+1;
                split <= 1;
            end
        endcase
    end
end



// Disk Read
always @ (posedge clk) begin : MEM_READ
    if (read) begin
        for(i=addr_read_start[28:0]; i<=addr_read_end[28:0]; i=i+1) begin
            case(addr_read_start[31:29])
                3'b000: begin
                    data[(i-addr_read_start[28:0])*8 +: 8] = mem0[i];
                    $display("MEM0[%0d]: %h", i, mem0[i] );
                end
                3'b001: begin
                    data[(i-addr_read_start[28:0])*8 +: 8] = mem1[i];
                    $display("MEM1[%0d]: %h", i, mem1[i] );
                end
                3'b010: data[(i-addr_read_start[28:0])*8 +: 8] = mem2[i];
                3'b011: data[(i-addr_read_start[28:0])*8 +: 8] = mem3[i];
                3'b100: data[(i-addr_read_start[28:0])*8 +: 8] = mem4[i];
                3'b101: data[(i-addr_read_start[28:0])*8 +: 8] = mem5[i];
                3'b110: data[(i-addr_read_start[28:0])*8 +: 8] = mem6[i];
                3'b111: data[(i-addr_read_start[28:0])*8 +: 8] = mem7[i];
            endcase
        end

        for(j=(addr_read_end+1-addr_read_start[28:0])*8; j<=37267; j=j+1) begin
            data[j] = 0;
        end

        if(split)
            data_updt2 = data << (addr_read_end-addr_read_start)*8;
        else begin
            data_updt1 = data;
            data_updt2 = 0;
        end

//        $display("DATA_UPDT: %h", data_updt1);
    end
end

endmodule
