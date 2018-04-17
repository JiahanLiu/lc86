module seg_lmt_chk_props (
    input clk, reset, 
    input V, MEM_RD, MEM_WR,
    input [2:0] SEG1_ID,
    input [1:0] DATA_SIZE,
    input [31:0] ADD_BASE_DISP, MUX_SIB_SI, 
    input EXC
);

//assert property (@(posedge clk) 

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
logic [32:0] temp1 = a+b;
logic [32:0] temp3 = {1'b0, a[31:0]} + {1'b0, not_b[31:0]} + {32'b0,1};
logic [4:0] temp2 = a[3:0] + b[3:0];
logic [4:0] temp4 = {1'b0, a[3:0]} + {1'b0, not_b[3:0]} + {32'b0, 1};
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


logic [9:0] DAA_result = DAA(a, flags);

assert property (@(posedge clk) (op==0) |-> alu_out == a+b);
assert property (@(posedge clk) (op==1) |-> alu_out == (a | b));
assert property (@(posedge clk) (op==2) |-> alu_out == ~a);
assert property (@(posedge clk) (op==3) |-> (alu_out[7:0] == DAA_result[7:0]) && (CF==DAA_result[9]) && (AF==DAA_result[8]));
assert property (@(posedge clk) (op==4) |-> alu_out == (a & b));
assert property (@(posedge clk) (op==5) |-> DF==0);
assert property (@(posedge clk) (op==6) |-> alu_out == a-b);
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


//bind execute alu32_props wrp_alu32 (
//    .clk(CLK),
//    .reset(RST),
//    .a(u_alu32.a),
//    .b(u_alu32.b),
//    .flags(u_alu32.flags),
//    .alu_out(u_alu32.alu_out),
//    .op(u_alu32.op)
//);

bind address_generation seg_lmt_chk_props wrp_seg_lmt_chk (
    .clk(CLK),
    .reset(RST),
    .V(u_seg_limit_check.V),
    .MEM_RD(u_seg_limit_check.MEM_RD),
    .MEM_WR(u_seg_limit_check.MEM_WR),
    .SEG1_ID(u_seg_limit_check.SEG1_ID),
    .DATA_SIZE(u_seg_limit_check.DATA_SIZE),
    .ADD_BASE_DISP(u_seg_limit_check.ADD_BASE_DISP),
    .MUX_SIB_SI(u_seg_limit_check.MUX_SIB_SI),
    .EXC(u_seg_limit_check.EXC)
);
