// Size of the control signals to be defined - it will be a part of control
// store. WE, data_size, 

module segment_register_file (
    input clk, set, reset,
    input [2:0] seg_SR, seg_DR,
    input [2:0] write_ID1,
    input [31:0] result1,
    input [2:0] read_control_signals,
    input [2:0] write_control_signals,

    output [31:0] seg_addr, seg_src
);

endmodule
