module adder32_props (
    input clk, reset, 
    input [31:0] a,b,
    input [31:0] carry,
    input [31:0] sum
);

logic [32:0] temp;
assign temp = a+b;
logic [1:0] temp1 = a[0] + b[0];
logic [2:0] temp2 = a[1:0] + b[1:0];
logic [3:0] temp3 = a[2:0] + b[2:0];
logic [4:0] temp4 = a[3:0] + b[3:0];
logic [5:0] temp5 = a[4:0] + b[4:0];
logic [6:0] temp6 = a[5:0] + b[5:0];
logic [7:0] temp7 = a[6:0] + b[6:0];
logic [8:0] temp8 = a[7:0] + b[7:0];
logic [9:0] temp9 = a[8:0] + b[8:0];
logic [10:0] temp10 = a[9:0] + b[9:0];
logic [11:0] temp11 = a[10:0] + b[10:0];
logic [12:0] temp12 = a[11:0] + b[11:0];
logic [13:0] temp13 = a[12:0] + b[12:0];
logic [14:0] temp14 = a[13:0] + b[13:0];
logic [15:0] temp15 = a[14:0] + b[14:0];
logic [16:0] temp16 = a[15:0] + b[15:0];
logic [17:0] temp17 = a[16:0] + b[16:0];
logic [18:0] temp18 = a[17:0] + b[17:0];
logic [19:0] temp19 = a[18:0] + b[18:0];
logic [20:0] temp20 = a[19:0] + b[19:0];
logic [21:0] temp21 = a[20:0] + b[20:0];
logic [22:0] temp22 = a[21:0] + b[21:0];
logic [23:0] temp23 = a[22:0] + b[22:0];
logic [24:0] temp24 = a[23:0] + b[23:0];
logic [25:0] temp25 = a[24:0] + b[24:0];
logic [26:0] temp26 = a[25:0] + b[25:0];
logic [27:0] temp27 = a[26:0] + b[26:0];
logic [28:0] temp28 = a[27:0] + b[27:0];
logic [29:0] temp29 = a[28:0] + b[28:0];
logic [30:0] temp30 = a[29:0] + b[29:0];
logic [31:0] temp31 = a[30:0] + b[30:0];

assert property (@(posedge clk) sum == temp[31:0]);
assert property (@(posedge clk) carry[31] == temp[32]);
assert property (@(posedge clk) carry[0] == temp1[1]);
assert property (@(posedge clk) carry[1] == temp2[2]);
assert property (@(posedge clk) carry[2] == temp3[3]);
assert property (@(posedge clk) carry[3] == temp4[4]);
assert property (@(posedge clk) carry[4] == temp5[5]);
assert property (@(posedge clk) carry[5] == temp6[6]);
assert property (@(posedge clk) carry[6] == temp7[7]);
assert property (@(posedge clk) carry[7] == temp8[8]);
assert property (@(posedge clk) carry[8] == temp9[9]);
assert property (@(posedge clk) carry[9] == temp10[10]);
assert property (@(posedge clk) carry[10] == temp11[11]);
assert property (@(posedge clk) carry[11] == temp12[12]);
assert property (@(posedge clk) carry[12] == temp13[13]);
assert property (@(posedge clk) carry[13] == temp14[14]);
assert property (@(posedge clk) carry[14] == temp15[15]);
assert property (@(posedge clk) carry[15] == temp16[16]);
assert property (@(posedge clk) carry[16] == temp17[17]);
assert property (@(posedge clk) carry[17] == temp18[18]);
assert property (@(posedge clk) carry[18] == temp19[19]);
assert property (@(posedge clk) carry[19] == temp20[20]);
assert property (@(posedge clk) carry[20] == temp21[21]);
assert property (@(posedge clk) carry[21] == temp22[22]);
assert property (@(posedge clk) carry[22] == temp23[23]);
assert property (@(posedge clk) carry[23] == temp24[24]);
assert property (@(posedge clk) carry[24] == temp25[25]);
assert property (@(posedge clk) carry[25] == temp26[26]);
assert property (@(posedge clk) carry[26] == temp27[27]);
assert property (@(posedge clk) carry[27] == temp28[28]);
assert property (@(posedge clk) carry[28] == temp29[29]);
assert property (@(posedge clk) carry[29] == temp30[30]);
assert property (@(posedge clk) carry[30] == temp31[31]);

endmodule

module adder32_cry_props (
    input clk, reset, 
    input [31:0] a,b,
    input [31:0] carry_out,
    input [31:0] sum,
    input carry_in
);

logic [32:0] temp;
assign temp = a+b+carry_in;
logic [1:0] temp1 = a[0] + b[0]+ carry_in;
logic [2:0] temp2 = a[1:0] + b[1:0]+ carry_in;
logic [3:0] temp3 = a[2:0] + b[2:0]+ carry_in;
logic [4:0] temp4 = a[3:0] + b[3:0]+ carry_in;
logic [5:0] temp5 = a[4:0] + b[4:0]+ carry_in;
logic [6:0] temp6 = a[5:0] + b[5:0]+ carry_in;
logic [7:0] temp7 = a[6:0] + b[6:0]+ carry_in;
logic [8:0] temp8 = a[7:0] + b[7:0]+ carry_in;
logic [9:0] temp9 = a[8:0] + b[8:0]+ carry_in;
logic [10:0] temp10 = a[9:0] + b[9:0]+ carry_in;
logic [11:0] temp11 = a[10:0] + b[10:0]+ carry_in;
logic [12:0] temp12 = a[11:0] + b[11:0]+ carry_in;
logic [13:0] temp13 = a[12:0] + b[12:0]+ carry_in;
logic [14:0] temp14 = a[13:0] + b[13:0]+ carry_in;
logic [15:0] temp15 = a[14:0] + b[14:0]+ carry_in;
logic [16:0] temp16 = a[15:0] + b[15:0]+ carry_in;
logic [17:0] temp17 = a[16:0] + b[16:0]+ carry_in;
logic [18:0] temp18 = a[17:0] + b[17:0]+ carry_in;
logic [19:0] temp19 = a[18:0] + b[18:0]+ carry_in;
logic [20:0] temp20 = a[19:0] + b[19:0]+ carry_in;
logic [21:0] temp21 = a[20:0] + b[20:0]+ carry_in;
logic [22:0] temp22 = a[21:0] + b[21:0]+ carry_in;
logic [23:0] temp23 = a[22:0] + b[22:0]+ carry_in;
logic [24:0] temp24 = a[23:0] + b[23:0]+ carry_in;
logic [25:0] temp25 = a[24:0] + b[24:0]+ carry_in;
logic [26:0] temp26 = a[25:0] + b[25:0]+ carry_in;
logic [27:0] temp27 = a[26:0] + b[26:0]+ carry_in;
logic [28:0] temp28 = a[27:0] + b[27:0]+ carry_in;
logic [29:0] temp29 = a[28:0] + b[28:0]+ carry_in;
logic [30:0] temp30 = a[29:0] + b[29:0]+ carry_in;
logic [31:0] temp31 = a[30:0] + b[30:0]+ carry_in;

assert property (@(posedge clk) sum == temp[31:0]);
assert property (@(posedge clk) carry_out[31] == temp[32]);
assert property (@(posedge clk) carry_out[0] == temp1[1]);
assert property (@(posedge clk) carry_out[1] == temp2[2]);
assert property (@(posedge clk) carry_out[2] == temp3[3]);
assert property (@(posedge clk) carry_out[3] == temp4[4]);
assert property (@(posedge clk) carry_out[4] == temp5[5]);
assert property (@(posedge clk) carry_out[5] == temp6[6]);
assert property (@(posedge clk) carry_out[6] == temp7[7]);
assert property (@(posedge clk) carry_out[7] == temp8[8]);
assert property (@(posedge clk) carry_out[8] == temp9[9]);
assert property (@(posedge clk) carry_out[9] == temp10[10]);
assert property (@(posedge clk) carry_out[10] == temp11[11]);
assert property (@(posedge clk) carry_out[11] == temp12[12]);
assert property (@(posedge clk) carry_out[12] == temp13[13]);
assert property (@(posedge clk) carry_out[13] == temp14[14]);
assert property (@(posedge clk) carry_out[14] == temp15[15]);
assert property (@(posedge clk) carry_out[15] == temp16[16]);
assert property (@(posedge clk) carry_out[16] == temp17[17]);
assert property (@(posedge clk) carry_out[17] == temp18[18]);
assert property (@(posedge clk) carry_out[18] == temp19[19]);
assert property (@(posedge clk) carry_out[19] == temp20[20]);
assert property (@(posedge clk) carry_out[20] == temp21[21]);
assert property (@(posedge clk) carry_out[21] == temp22[22]);
assert property (@(posedge clk) carry_out[22] == temp23[23]);
assert property (@(posedge clk) carry_out[23] == temp24[24]);
assert property (@(posedge clk) carry_out[24] == temp25[25]);
assert property (@(posedge clk) carry_out[25] == temp26[26]);
assert property (@(posedge clk) carry_out[26] == temp27[27]);
assert property (@(posedge clk) carry_out[27] == temp28[28]);
assert property (@(posedge clk) carry_out[28] == temp29[29]);
assert property (@(posedge clk) carry_out[29] == temp30[30]);
assert property (@(posedge clk) carry_out[30] == temp31[31]);

endmodule


module alu32_props (
    input clk, reset,
    input [31:0] alu_out,
	input [31:0] flags,
	input [31:0] a, b,
	input [2:0] op
);

assign OF = flags[11];
assign DF = flags[10];
assign SF = flags[7];
assign ZF = flags[6];
assign AF = flags[4];
assign PF = flags[2];
assign CF = flags[0];

assume property (@(posedge clk) (op==3) |-> a[31:8] == 24'b0);
assume property (@(posedge clk) (op==3) |-> AF == 0);

function reg ZF_flag (reg [31:0] alu_out);
    if(alu_out==32'b0)
        return 1;
    else
        return 0;
    ZF_flag = 1;
endfunction

function reg PF_flag (reg [31:0] alu_out);
    if(^~alu_out[7:0])
        return 1;
    else
        return 0;
    PF_flag = 1;
endfunction

function reg OF_flag (reg [31:0] alu_out);
    if((a[31] == b[31]) && (a[31] != alu_out[31]))
        return 1;
    else
        return 0;
    OF_flag = 1;
endfunction

logic [31:0] not_b = ~b;
logic [31:0] not_a = ~a;
logic [32:0] temp1 = a+b;
logic [32:0] temp3 = {1'b0, not_a[31:0]} + {1'b0, b[31:0]} + {32'b0,1};
logic [4:0] temp2 = a[3:0] + b[3:0];
logic [4:0] temp4 = {1'b0, not_a[3:0]} + {1'b0, b[3:0]} + {32'b0, 1};
logic [31:0] old_a = a;
logic old_CF = CF;

function reg[9:0] DAA (reg [31:0]a, reg [31:0] flags);
    if(((a & 8'h0F) > 9) | (flags[4] == 1)) begin
        a = a+6;
        flags[0] = flags[0] | a[8];
        flags[4] = 1;
    end else
        flags[4] = 0;
    
    if ((old_a > 8'h99) || (old_CF == 1)) begin
        a = a+8'h60;
        flags[0] = 1;
    end else 
        flags[0] = 0;
    DAA = {flags[0], flags[4], a[7:0]};
endfunction

//assert property (@(posedge clk)
//    if(op==0) (alu_out == a+b)
//    else if(op==1) (alu_out == a | b)
//    else if(op==2) (alu_out == ~a) 
//);

logic [9:0] DAA_result = DAA(a, flags);

assert property (@(posedge clk) (op==0) |-> alu_out == a+b);
assert property (@(posedge clk) (op==1) |-> alu_out == (a | b));
assert property (@(posedge clk) (op==2) |-> alu_out == ~a);
assert property (@(posedge clk) (op==3) |-> (alu_out[7:0] == DAA_result[7:0]) && (CF==DAA_result[9]) && (AF==DAA_result[8]));
assert property (@(posedge clk) (op==4) |-> alu_out == (a & b));
assert property (@(posedge clk) (op==5) |-> DF==0);
assert property (@(posedge clk) (op==6) |-> alu_out == b-a);
assert property (@(posedge clk) (op==7) |-> DF==1);

// Flags changed
assert property (@(posedge clk) 
    (op==0) |-> (CF==temp1[32]) && (ZF==ZF_flag(alu_out)) && (PF==PF_flag(alu_out)) 
    && (SF==alu_out[31]) && (OF==OF_flag(alu_out)) && (AF==temp2[4])
);

assert property (@(posedge clk) 
    (op==1) |-> (OF==0) && (CF==0) && (ZF==ZF_flag(alu_out)) && (PF==PF_flag(alu_out)) && (SF==alu_out[31])
);

assert property (@(posedge clk) 
    (op==4) |-> (OF==0) && (CF==0) && (ZF==ZF_flag(alu_out)) && (PF==PF_flag(alu_out)) && (SF==alu_out[31])
);

assert property (@(posedge clk) 
    (op==6) |-> (CF==temp3[32]) && (ZF==ZF_flag(alu_out)) && (PF==PF_flag(alu_out)) 
    && (SF==alu_out[31]) && (OF==OF_flag(alu_out)) && (AF==temp4[4])
);

endmodule


//bind execute adder32_props wrp_adder32 (
//    .clk(CLK),
//    .reset(RST),
//    .a(u_adder32.a),
//    .b(u_adder32.b),
//    .carry(u_adder32.carry),
//    .sum(u_adder32.sum)
//);


//bind execute adder32_cry_props wrp_adder32_cry (
//    .clk(CLK),
//    .reset(RST),
//    .a(add_sz.a),
//    .b(add_sz.b),
//    .carry_out(add_sz.carry_out),
//    .sum(add_sz.sum),
//    .carry_in(add_sz.carry_in)
//);


bind execute alu32_props wrp_alu32 (
    .clk(CLK),
    .reset(RST),
    .a(u_alu32.a),
    .b(u_alu32.b),
    .flags(u_alu32.flags),
    .alu_out(u_alu32.alu_out),
    .op(u_alu32.op)
);

bind execute execute_props wrp_alu32 (
    .clk(CLK),
    .reset(RST),
    .a(u_alu32.a),
    .b(u_alu32.b),
    .flags(u_alu32.flags),
    .alu_out(u_alu32.alu_out),
    .op(u_alu32.op)
);
