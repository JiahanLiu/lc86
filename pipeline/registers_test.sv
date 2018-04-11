module regfile_gpr_props (
    input clk,
    input [31:0] result1, result2, result3,
    input [2:0] SR1, SR2, SR3, SR4,
    input [1:0]	RE1, RE2, RE3, RE4,
    input [2:0] DR1, DR2, DR3,
    input write_DR1, write_DR2, write_DR3,
    input [1:0] WE1, WE2, WE3,
    input [31:0] regA, regB, regC, regD
);

assume property (@(posedge clk) !(DR1 & DR2));
assume property (@(posedge clk) !(DR1 & DR3));
assume property (@(posedge clk) !(DR2 & DR3));

assume property (@(posedge clk) !(SR1 & SR2));
assume property (@(posedge clk) !(SR1 & SR3));
assume property (@(posedge clk) !(SR1 & SR4));
assume property (@(posedge clk) !(SR2 & SR3));
assume property (@(posedge clk) !(SR2 & SR4));
assume property (@(posedge clk) !(SR3 & SR4));

assume property (@(posedge clk) write_DR1 |-> !$isunknown(result1) && $stable(result1));
assume property (@(posedge clk) write_DR2 |-> !$isunknown(result2) && $stable(result2));
assume property (@(posedge clk) write_DR3 |-> !$isunknown(result3) && $stable(result3));

assert property (@(posedge clk) RE1==0 |-> regA[31:8]==24'b0); 
assert property (@(posedge clk) RE1==1 |-> regA[31:8]==24'b0); 
assert property (@(posedge clk) RE1==2 |-> regA[31:16]==24'b0); 

assert property (@(posedge clk) RE2==0 |-> regB[31:8]==24'b0); 
assert property (@(posedge clk) RE2==1 |-> regB[31:8]==24'b0); 
assert property (@(posedge clk) RE2==2 |-> regB[31:16]==24'b0); 

assert property (@(posedge clk) RE3==0 |-> regC[31:8]==24'b0); 
assert property (@(posedge clk) RE3==1 |-> regC[31:8]==24'b0); 
assert property (@(posedge clk) RE3==2 |-> regC[31:16]==24'b0); 

assert property (@(posedge clk) RE4==0 |-> regD[31:8]==24'b0); 
assert property (@(posedge clk) RE4==1 |-> regD[31:8]==24'b0); 
assert property (@(posedge clk) RE4==2 |-> regD[31:16]==24'b0); 





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
logic [32:0] temp3 = {1'b0, not_a[31:0]} + {1'b0, b[31:0]} + {32'b0, 1'b1};
logic [4:0] temp2 = a[3:0] + b[3:0];
logic [4:0] temp4 = {1'b0, not_a[3:0]} + {1'b0, b[3:0]} + {32'b0, 1'b1};
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


bind register_file regfile_gpr_props wrp_regfile_gpr (
    .clk(CLK),
    .result1(GPR_DIN0),
    .result2(GPR_DIN1),
    .result3(GPR_DIN2),
    .SR1(GPRID0),
    .SR2(GPRID1),
    .SR3(GPRID2),
    .SR4(GPRID3),
    .RE1(GPR_RE0),
    .RE2(GPR_RE1),
    .RE3(GPR_RE2),
    .RE4(GPR_RE3),
    .DR1(WRGPR0),
    .DR2(WRGPR1),
    .DR3(WRGPR2),
    .write_DR1(WE0),
    .write_DR2(WE1),
    .write_DR3(WE2),
    .WE1(GPRWE0),
    .WE2(GPRWE1),
    .WE3(GPRWE2),
    .regA(GPRDOUT0),
    .regB(GPRDOUT1),
    .regC(GPRDOUT2),
    .regD(GPRDOUT3)
);
