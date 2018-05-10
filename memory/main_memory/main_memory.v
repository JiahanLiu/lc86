//WRITE_SIZE one bit hot for amnt, 0 is the full line
//SRC, IC=0, DC=1, DMA=2

module main_memory (
    input [14:0] ADDR,
    input WR, EN,//BS_R removed because no use
    input [2:0] WRITE_SIZE,
    inout [255:0] DATA_BUF
);


wire [31:0] bit_lines;
wire [1023:0] word_lines;
wire [9:0] row_address;
wire [4:0] column_address;
wire [31:0] write_mask1, write_mask2, write_mask3, write_out, write_out_b, write_read_mask, write_out_final;
wire [31:0] shift1, shift2, shift3;
wire [7:0] CE, CE_BAR, CE_EN;

assign column_address = ADDR[4:0];
assign row_address = ADDR[14:5];

// Address decoder
decoder5to32 u_column_decoder (bit_lines, column_address);
decoder10to1024 u_row_decoder (word_lines, row_address);


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

//STEVEN: should these shift amounts be 2, 3, and 4?
// I would expect 1, 2, 3    
shift_arithmetic_left u_SAL1 (shift1, bit_lines, 32'h1);
shift_arithmetic_left u_SAL2 (shift2, bit_lines, 32'h2);
shift_arithmetic_left u_SAL3 (shift3, bit_lines, 32'h3);

or2$ or1[31:0] (write_mask1, bit_lines, shift1);
or3$ or2[31:0] (write_mask2, bit_lines, shift1, shift2);
or4$ or3[31:0] (write_mask3, bit_lines, shift1, shift2, shift3);

mux32_4way mux4_write (write_out, write_mask3, bit_lines, write_mask1, write_mask2, WRITE_SIZE[1:0]);

nor3$ or_all (write_all, WRITE_SIZE[0], WRITE_SIZE[1], WRITE_SIZE[2]);
   //STEVEN: write all should write 16bytes, not 32bytes
mux32_4way mux2_write (write_out_final, write_out, write_out, 32'h0000_FFFF, 32'hFFFF_0000, {write_all, ADDR[4]});
inv1$ inv1_wr[31:0] (write_out_b, write_out_final);

// write is active low for sram
mux32_2way mux3_write (write_read_mask, 32'hFFFF_FFFF, write_out_b, WR);

// OE for the correct block
decoder3_8$ u_decoder3to8 (ADDR[14:12], CE, CE_BAR);
nand2$ chip_en[7:0] (CE_EN, EN, CE);

wire [31:0] CE_out, CE_final0, CE_final1, CE_final2, CE_final3, CE_final4, CE_final5, CE_final6, CE_final7;
xnor2$ xor1[31:0] (CE_out, write_read_mask, WR);
or2$ or0_ce[31:0] (CE_final0, CE_EN[0], CE_out);
or2$ or1_ce[31:0] (CE_final1, CE_EN[1], CE_out);
or2$ or2_ce[31:0] (CE_final2, CE_EN[2], CE_out);
or2$ or3_ce[31:0] (CE_final3, CE_EN[3], CE_out);
or2$ or4_ce[31:0] (CE_final4, CE_EN[4], CE_out);
or2$ or5_ce[31:0] (CE_final5, CE_EN[5], CE_out);
or2$ or6_ce[31:0] (CE_final6, CE_EN[6], CE_out);
or2$ or7_ce[31:0] (CE_final7, CE_EN[7], CE_out);

word_lines128 blk_line0 (ADDR[11:5], DATA_BUF, 1'b0, write_read_mask, CE_final0);
word_lines128 blk_line1 (ADDR[11:5], DATA_BUF, 1'b0, write_read_mask, CE_final1);
word_lines128 blk_line2 (ADDR[11:5], DATA_BUF, 1'b0, write_read_mask, CE_final2);
word_lines128 blk_line3 (ADDR[11:5], DATA_BUF, 1'b0, write_read_mask, CE_final3);
word_lines128 blk_line4 (ADDR[11:5], DATA_BUF, 1'b0, write_read_mask, CE_final4);
word_lines128 blk_line5 (ADDR[11:5], DATA_BUF, 1'b0, write_read_mask, CE_final5);
word_lines128 blk_line6 (ADDR[11:5], DATA_BUF, 1'b0, write_read_mask, CE_final6);
word_lines128 blk_line7 (ADDR[11:5], DATA_BUF, 1'b0, write_read_mask, CE_final7);



endmodule

module word_lines128 (
    input [6:0] A,
    input [255:0] DIO,
    input  OE,
    input [31:0] WR, 
    input [31:0] CE
);

sram128x8$ sram0 (A, DIO[7:0], OE, WR[0], CE[0]);
sram128x8$ sram1 (A, DIO[15:8], OE, WR[1], CE[1]);
sram128x8$ sram2 (A, DIO[23:16], OE, WR[2], CE[2]);
sram128x8$ sram3 (A, DIO[31:24], OE, WR[3], CE[3]);
sram128x8$ sram4 (A, DIO[39:32], OE, WR[4], CE[4]);
sram128x8$ sram5 (A, DIO[47:40], OE, WR[5], CE[5]);
sram128x8$ sram6 (A, DIO[55:48], OE, WR[6], CE[6]);
sram128x8$ sram7 (A, DIO[63:56], OE, WR[7], CE[7]);
sram128x8$ sram8 (A, DIO[71:64], OE, WR[8], CE[8]);
sram128x8$ sram9 (A, DIO[79:72], OE, WR[9], CE[9]);
sram128x8$ sram10 (A, DIO[87:80], OE, WR[10], CE[10]);
sram128x8$ sram11 (A, DIO[95:88], OE, WR[11], CE[11]);
sram128x8$ sram12 (A, DIO[103:96], OE, WR[12], CE[12]);
sram128x8$ sram13 (A, DIO[111:104], OE, WR[13], CE[13]);
sram128x8$ sram14 (A, DIO[119:112], OE, WR[14], CE[14]);
sram128x8$ sram15 (A, DIO[127:120], OE, WR[15], CE[15]);
sram128x8$ sram16 (A, DIO[135:128], OE, WR[16], CE[16]);
sram128x8$ sram17 (A, DIO[143:136], OE, WR[17], CE[17]);
sram128x8$ sram18 (A, DIO[151:144], OE, WR[18], CE[18]);
sram128x8$ sram19 (A, DIO[159:152], OE, WR[19], CE[19]);
sram128x8$ sram20 (A, DIO[167:160], OE, WR[20], CE[20]);
sram128x8$ sram21 (A, DIO[175:168], OE, WR[21], CE[21]);
sram128x8$ sram22 (A, DIO[183:176], OE, WR[22], CE[22]);
sram128x8$ sram23 (A, DIO[191:184], OE, WR[23], CE[23]);
sram128x8$ sram24 (A, DIO[199:192], OE, WR[24], CE[24]);
sram128x8$ sram25 (A, DIO[207:200], OE, WR[25], CE[25]);
sram128x8$ sram26 (A, DIO[215:208], OE, WR[26], CE[26]);
sram128x8$ sram27 (A, DIO[223:216], OE, WR[27], CE[27]);
sram128x8$ sram28 (A, DIO[231:224], OE, WR[28], CE[28]);
sram128x8$ sram29 (A, DIO[239:232], OE, WR[29], CE[29]);
sram128x8$ sram30 (A, DIO[247:240], OE, WR[30], CE[30]);
sram128x8$ sram31 (A, DIO[255:248], OE, WR[31], CE[31]);

endmodule
