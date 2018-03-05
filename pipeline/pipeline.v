module TOP;
//this module is used to debug the basic functionality of the simulator
//the clk cycle used to drive the entire system
reg clk, clr, pre;
integer     clk_cycle = 5;
always  #(clk_cycle)  clk = ~clk;
SIMULATOR bob(clk, clr, pre);
initial
     begin
	clk = 0;
	clr = 1;
	pre = 1;
	# clk_cycle
	clr = 0;
	# (clk_cycle -2)
	clr = 1;
	# (clk_cycle - 3)
	# (clk_cycle * 2);
     end 

   
   
initial #(29 * clk_cycle) $finish;
initial
begin
	$vcdplusfile("lab_four.dump.vpd");
	$vcdpluson(0, TOP);
end
endmodule

module PIPELINE(CLK, CLR, PRE);
//inputs to this simulator
input CLK, CLR, PRE;
assign EN = 1;//placeholder until stalls are working correctly


//*******REGISTER FILE*******//
//register file module to be used by the system
//REG_FILE(RESULT, REG, RM_REG, RE1, RE2, DEST, WE, CLOCK, REG_A, REG_B);
wire [31:0] EAX_IN, EAX_OUT, EAX_BAR_OUT, ECX_IN, ECX_OUT, ECX_BAR_OUT;
reg32e$ EAX(CLK, EAX_IN, EAX_OUT, EAX_BAR_OUT, CLR, PRE, EAX_EN);
reg32e$ ECX(CLK, ECX_IN, ECX_OUT, ECX_BAR_OUT, CLR, PRE, ECX_EN);

//*******CACHE FILES*******//
//Cache file systems to be used by the system


//*******FETCH STAGE*******//
// FETCH MODULE GOES HERE;

//Latches between fetch and decode
wire [127:0] IR_IN, IR_OUT, IR_BAR_OUT, DE_V_OUT_T, DE_V_OUT_T_BAR;
reg32e$ IR_3(CLK, IR_IN[127:96], IR_OUT[127:96], IR_BAR_OUT[127:96], CLR, PRE, EN);
reg32e$ IR_2(CLK, IR_IN[95:64], IR_OUT[95:64], IR_BAR_OUT[95:64], CLR, PRE, EN);
reg32e$ IR_1(CLK, IR_IN[63:32], IR_OUT[63:32], IR_BAR_OUT[63:32], CLR, PRE, EN);
reg32e$ IR_0(CLK, IR_IN[31:0], IR_OUT[31:0], IR_BAR_OUT[31:0], CLR, PRE, EN);
reg32e$ DE_V(CLK, {{31{1'b0}},DE_V_IN}, DE_V_OUT_T, DE_V_OUT_T_BAR, CLR, PRE, EN);
assign DE_V_OUT = DE_V_OUT_T[0];


//*******DECODE STAGE*******//
// DECODE MODULE GOES HERE;

//Latches between decode and address generation
wire [2:0] AG_SR, AG_DR, AG_BASE, AG_INDEX, AG_MM_SR, AG_MM_DR, AG_SEG_SR, AG_SEG_DR;
wire [1:0] AG_SCALE, AG_DATA_SIZE;
assign AG_REGS_IN = {4'b0000, AG_SR, AG_DR, AG_BASE, AG_INDEX, AG_MM_SR, AG_MM_DR, AG_SEG_DR, AG_SEG_DR, AG_SCALE, AG_DATA_SIZE};
wire [31:0] AG_REGS_OUT, AG_REGS_OUT_BAR;
reg32e$ AG_REGS(CLK, AG_REGS_IN, AG_REGS_OUT, AG_REGS_OUT, CLR, PRE, EN);
wire [31:0] AG_IMM_IN, AG_IMM_OUT, AG_IMM_OUT_BAR, AG_DISP_IN, AG_DISP_OUT, AG_DISP_OUT_BAR;
reg32e$ AG_IMM(CLK, AG_IMM_IN, AG_IMM_OUT, AG_IMM_OUT_BAR, CLR, PRE, EN);
reg32e$ AG_DISP(CLK, AG_DISP_IN, AG_DISP_OUT, AG_DISP_OUT_BAR, CLR, PRE, EN);





//*******ADDRESS GENERATION STAGE*******//
// ADDRESS GENERATION MODULE GOES HERE;

//register between AG and ME
wire [31:0] A_BAR_OUT, B_BAR_OUT, A_OUT, B_OUT;
reg32e$ A(CLK, A_IN, A_OUT, A_BAR_OUT, CLR, PRE, EN);
reg32e$ B(CLK, B_IN, B_OUT, B_BAR_OUT, CLR, PRE, EN);
wire [31:0] D_REG_DEST, D_ALUK, D_V_COM, D_1, D_2, D_3;
reg32e$ REG_DEST_COM(CLK, {{31{1'b0}},REG_DEST_COM_IN}, D_REG_DEST, D_3, CLR, PRE, EN);
reg32e$ ALUK_COM(CLK, {{31{1'b0}},ALUK_COM_IN}, D_ALUK, D_1, CLR, PRE, EN);
reg32e$ V_COM(CLK, {{31{1'b0}},V_COM_IN}, D_V_COM, D_2, CLR, PRE, EN);
assign REG_DEST_COM_OUT = D_REG_DEST[0];
assign ALUK_COM_OUT = D_ALUK[0];
assign V_COM_OUT = D_V_COM[0];

//*******MEMORY STAGE*******//
// MEMORY MODULE GOES HERE;

//register between ME and EX



//*******EXECUTE STAGE*******//
// EXECUTE MODULE GOES HERE;

//register between EX and WB



//*******WRITE BACK STAGE*******//
// WRITE BACK MODULE GOES HERE;


endmodule