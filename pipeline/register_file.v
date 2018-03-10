// Size of the control signals to be defined - it will be a part of control
// store. WE, data_size, 

module register_file (
    input clk, set, reset,
    input [2:0] DR, SR, baseID, indexID,
    input [2:0] write_ID1, write_ID2, write_ID3,
    input [31:0] result1, result2, result3,
    input [2:0] write_control_signals,
    input [2:0] read_control_signals,

    output [31:0] regA, regB, base, index
);

endmodule
