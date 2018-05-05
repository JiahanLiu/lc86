//WRITE_SIZE one bit hot for amnt, 0 is the full line
//SRC, IC=0, DC=1, DMA=2

module main_memory (
    input [14:0] ADDR,
    input WR, EN,//BS_R removed because no use
    input [2:0] WRITE_SIZE,
    inout [255:0] DATA_BUF
);


wire [31:0] bit_lines;
wire [1023:0] word_lines, word_lines_b;
wire [9:0] row_address;
wire [4:0] column_address;
wire [31:0] write_mask1, write_mask2, write_mask3, write_out, write_out_b, write_read_mask, write_out_final;
wire [31:0] shift1, shift2, shift3;
wire [7:0] OE, OE_BAR;
wire en1_b;
wire [31:0] ROW_BUF_D;
wire [3:0] shift_amt;

assign column_address = ADDR[4:0];
assign row_address = ADDR[14:5];

// Address decoder
decoder5to32 u_column_decoder (bit_lines, column_address);
decoder10to1024 u_row_decoder (word_lines, row_address);

inv1$ inv_row [1023:0] (word_lines, word_lines_b);

// Read-write mask logic
//if (read)
//    WR = 31'hFFFF_FFFF;
//else (write) begin
//    if(size==1)
//        WR = bit_lines;
//    else if(size==2)
//        WR = bit_lines | (bit_lines >> 1);
//    else if(size==3)
//        WR = bit_lines | (bit_lines >> 1) | (bit_lines >> 2);
//    else if(size==4)
//        WR = bit_lines | (bit_lines >> 1) | (bit_lines >> 2) | bit_lines >> 3);
//end

shift_arithmetic_left u_SAL1 (shift1, bit_lines, 32'h2);
shift_arithmetic_left u_SAL2 (shift2, bit_lines, 32'h3);
shift_arithmetic_left u_SAL3 (shift3, bit_lines, 32'h4);

or2$ or1[31:0] (write_mask1, bit_lines, shift1);
or3$ or2[31:0] (write_mask2, bit_lines, shift1, shift2);
or4$ or3[31:0] (write_mask3, bit_lines, shift1, shift2, shift3);

mux32_4way mux4_write (write_out, write_mask3, bit_lines, write_mask1, write_mask2, WRITE_SIZE[1:0]);

or3$ or_all (write_all, WRITE_SIZE[0], WRITE_SIZE[1], WRITE_SIZE[2]);
mux32_2way mux2_write (write_out_final, write_out, 32'hFFFF_FFFF, write_all);
inv1$ inv1_wr[31:0] (write_out_b, write_out_final);

// write is active low for sram
mux32_2way mux3_write (write_read_mask, 32'hFFFF_FFFF, write_out_b, WR);

// OE for the correct block
decoder3_8$ u_decoder3to8 (ADDR[14:12], OE, OE_BAR);

word_lines128 blk_line0 (ADDR[11:5], DATA_BUF, OE_BAR[0], write_read_mask, 1'b0);
word_lines128 blk_line1 (ADDR[11:5], DATA_BUF, OE_BAR[1], write_read_mask, 1'b0);
word_lines128 blk_line2 (ADDR[11:5], DATA_BUF, OE_BAR[2], write_read_mask, 1'b0);
word_lines128 blk_line3 (ADDR[11:5], DATA_BUF, OE_BAR[3], write_read_mask, 1'b0);
word_lines128 blk_line4 (ADDR[11:5], DATA_BUF, OE_BAR[4], write_read_mask, 1'b0);
word_lines128 blk_line5 (ADDR[11:5], DATA_BUF, OE_BAR[5], write_read_mask, 1'b0);
word_lines128 blk_line6 (ADDR[11:5], DATA_BUF, OE_BAR[6], write_read_mask, 1'b0);
word_lines128 blk_line7 (ADDR[11:5], DATA_BUF, OE_BAR[7], write_read_mask, 1'b0);



endmodule



module buffer_io (
    input [127:0] bus_read,
    inout [255:0] ram_out,
    input WR, CLK,
    input CLR, PRE,
    input section_sel,
    input [3:0] shift_amount,
    output [127:0] BUS_OUT
);

// Connect DIO to buffer for write
// Bus is connected to the low 31 bits of the buffer
// While writing to the memory, always read from low 31 bits of buffer
// While reading from memory, fill all 256 bits of buffer
// column_address[5] will determine whether to read from low 128 or high 128

wire [255:0] Q_OUT, DIN;
wire [255:0] BUF_OUT;

mux2_128 mux_out (BUS_OUT, Q_OUT[127:0], Q_OUT[255:128], section_sel);

mux2_128 mux_in1 (DIN[127:0], ram_out[127:0], bus_read[127:0], WR);
mux2_128 mux_in2 (DIN[255:128], ram_out[255:128], bus_read[127:0], WR);
// Low 128
ioreg16$ ioreg0 (CLK, DIN[15:0], Q_OUT[15:0], , CLR, PRE);
ioreg16$ ioreg1 (CLK, DIN[31:16], Q_OUT[31:16], , CLR, PRE);
ioreg16$ ioreg2 (CLK, DIN[47:32], Q_OUT[47:32], , CLR, PRE);
ioreg16$ ioreg3 (CLK, DIN[63:48], Q_OUT[63:48], , CLR, PRE);
ioreg16$ ioreg4 (CLK, DIN[79:64], Q_OUT[79:64], , CLR, PRE);
ioreg16$ ioreg5 (CLK, DIN[95:80], Q_OUT[95:80], , CLR, PRE);
ioreg16$ ioreg6 (CLK, DIN[111:96], Q_OUT[111:96], , CLR, PRE);
ioreg16$ ioreg7 (CLK, DIN[127:112], Q_OUT[127:112], , CLR, PRE);

// High 128
ioreg16$ ioreg8 (CLK, DIN[143:128], Q_OUT[143:128], , CLR, PRE);
ioreg16$ ioreg9 (CLK, DIN[159:144], Q_OUT[159:144], , CLR, PRE);
ioreg16$ ioreg10 (CLK, DIN[175:160], Q_OUT[175:160], , CLR, PRE);
ioreg16$ ioreg11 (CLK, DIN[191:176], Q_OUT[191:176], , CLR, PRE);
ioreg16$ ioreg12 (CLK, DIN[207:192], Q_OUT[207:192], , CLR, PRE);
ioreg16$ ioreg13 (CLK, DIN[223:208], Q_OUT[223:208], , CLR, PRE);
ioreg16$ ioreg14 (CLK, DIN[239:224], Q_OUT[239:224], , CLR, PRE);
ioreg16$ ioreg15 (CLK, DIN[255:240], Q_OUT[255:240], , CLR, PRE);

shiftleft u_shifterleft1 (BUF_OUT[127:0], Q_OUT[127:0], shift_amount);
shiftleft u_shifterleft2 (BUF_OUT[255:128], Q_OUT[255:128], shift_amount);

// Connect DIO to buffer for read
// in is buffer out and out is DATA_BUF
inv1$ inv_tri_en (en1_b, WR);

// Low 128
tristate16L$ buf0 (en1_b, BUF_OUT[15:0], ram_out[15:0]);
tristate16L$ buf1 (en1_b, BUF_OUT[31:16], ram_out[31:16]);
tristate16L$ buf2 (en1_b, BUF_OUT[47:32], ram_out[47:32]);
tristate16L$ buf3 (en1_b, BUF_OUT[63:48], ram_out[63:48]);
tristate16L$ buf4 (en1_b, BUF_OUT[79:64], ram_out[79:64]);
tristate16L$ buf5 (en1_b, BUF_OUT[95:80], ram_out[95:80]);
tristate16L$ buf6 (en1_b, BUF_OUT[111:96], ram_out[111:96]);
tristate16L$ buf7 (en1_b, BUF_OUT[127:112], ram_out[127:112]);

// High 128
tristate16L$ buf8 (en1_b, BUF_OUT[143:128], ram_out[143:128]);
tristate16L$ buf9 (en1_b, BUF_OUT[159:144], ram_out[159:144]);
tristate16L$ buf10 (en1_b, BUF_OUT[175:160], ram_out[175:160]);
tristate16L$ buf11 (en1_b, BUF_OUT[191:176], ram_out[191:176]);
tristate16L$ buf12 (en1_b, BUF_OUT[207:192], ram_out[207:192]);
tristate16L$ buf13 (en1_b, BUF_OUT[223:208], ram_out[223:208]);
tristate16L$ buf14 (en1_b, BUF_OUT[239:224], ram_out[239:224]);
tristate16L$ buf15 (en1_b, BUF_OUT[255:240], ram_out[255:240]);


endmodule 




module shiftleft(
    output [127:0] Dout,
    input [127:0] Din,
    input [3:0] amnt

);


wire [127:0] array [15:0];
wire [127:0] mux_array [3:0];
   wire [127:0] zero = 127'h0000_0000_0000_0000;
   
genvar i;
generate
for(i=1;i<16;i=i+1)
  begin : shifter
  //Allowed since i is constant when the loop is unrolled
  assign array[i] = {Din[127-i*8:0], zero[127:127-i*8+1]};
  end
    endgenerate
   assign array[0] = Din;
   
//muxes to select shifted value, first round of muxes
mux4_128 mux1 (mux_array[0],array[0],array[1],array[2],array[3],amnt[0],amnt[1]);
mux4_128 mux2 (mux_array[1],array[4],array[5],array[6],array[7],amnt[0],amnt[1]);
mux4_128 mux3 (mux_array[2],array[8],array[9],array[10],array[11],amnt[0],amnt[1]);
mux4_128 mux4 (mux_array[3],array[12],array[13],array[14],array[15],amnt[0],amnt[1]);

//last round of muxes
mux4_128 mux5 (Dout,mux_array[0],mux_array[1],mux_array[2],mux_array[3],amnt[2],amnt[3]);
	

endmodule


module word_lines128 (
    input [6:0] A,
    input [255:0] DIO,
    input  OE,
    input [31:0] WR, 
    input CE
);

sram128x8$ sram0 (A, DIO[7:0], OE, WR[0], CE);
sram128x8$ sram1 (A, DIO[15:8], OE, WR[1], CE);
sram128x8$ sram2 (A, DIO[23:16], OE, WR[2], CE);
sram128x8$ sram3 (A, DIO[31:24], OE, WR[3], CE);
sram128x8$ sram4 (A, DIO[39:32], OE, WR[4], CE);
sram128x8$ sram5 (A, DIO[47:40], OE, WR[5], CE);
sram128x8$ sram6 (A, DIO[55:48], OE, WR[6], CE);
sram128x8$ sram7 (A, DIO[63:56], OE, WR[7], CE);
sram128x8$ sram8 (A, DIO[71:64], OE, WR[8], CE);
sram128x8$ sram9 (A, DIO[79:72], OE, WR[9], CE);
sram128x8$ sram10 (A, DIO[87:80], OE, WR[10], CE);
sram128x8$ sram11 (A, DIO[95:88], OE, WR[11], CE);
sram128x8$ sram12 (A, DIO[103:96], OE, WR[12], CE);
sram128x8$ sram13 (A, DIO[111:104], OE, WR[13], CE);
sram128x8$ sram14 (A, DIO[119:112], OE, WR[14], CE);
sram128x8$ sram15 (A, DIO[127:120], OE, WR[15], CE);
sram128x8$ sram16 (A, DIO[135:128], OE, WR[16], CE);
sram128x8$ sram17 (A, DIO[143:136], OE, WR[17], CE);
sram128x8$ sram18 (A, DIO[151:144], OE, WR[18], CE);
sram128x8$ sram19 (A, DIO[159:152], OE, WR[19], CE);
sram128x8$ sram20 (A, DIO[167:160], OE, WR[20], CE);
sram128x8$ sram21 (A, DIO[175:168], OE, WR[21], CE);
sram128x8$ sram22 (A, DIO[183:176], OE, WR[22], CE);
sram128x8$ sram23 (A, DIO[191:184], OE, WR[23], CE);
sram128x8$ sram24 (A, DIO[199:192], OE, WR[24], CE);
sram128x8$ sram25 (A, DIO[207:200], OE, WR[25], CE);
sram128x8$ sram26 (A, DIO[215:208], OE, WR[26], CE);
sram128x8$ sram27 (A, DIO[223:216], OE, WR[27], CE);
sram128x8$ sram28 (A, DIO[231:224], OE, WR[28], CE);
sram128x8$ sram29 (A, DIO[239:232], OE, WR[29], CE);
sram128x8$ sram30 (A, DIO[247:240], OE, WR[30], CE);
sram128x8$ sram31 (A, DIO[255:248], OE, WR[31], CE);

endmodule
