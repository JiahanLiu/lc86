// I have kept the control store as 32 bits for now
// Need to divide the decode in 2 pipeline stages

module decode (
    input clk, set, reset,
    input [127:0] IR,
    input [31:0] EIP,
    input [15:0] CS,
    input interrupt_addr, exception_addr,

    output [31:0] EIP_OUT,
    output [15:0] CS_OUT,
    output [3:0] instr_length_updt
    output [31:0] control_store,
    output [2:0] DR, SR, base, index,
    output [2:0] MM_DR, MM_SR,
    output [2:0] seg_SR, seg_DR,
    output [1:0] data_size, 
    output [31:0] imm, disp,

    output operation, MM_operation,
    output type_A, MM_type_A,
    output type_B, MM_type_B
);

endmodule
