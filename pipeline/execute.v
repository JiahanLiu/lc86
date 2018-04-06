// Control store width needs to be adjusted

module execute (
   input CLK, SET, RST, //not uesd SET/RST

   input EX_V,
   input [31:0] EX_NEIP,
   input [15:0] EX_NCS,
   input [63:0] EX_CONTROL_STORE,

   input [31:0] EX_A, EX_B,
   input [31:0] EX_COUNT, 

   input [31:0] EX_ADDRESS,

   input [2:0] EX_DR1, EX_DR2, EX_DR3,

   output WB_V,
   output [31:0] WB_NEIP, 
   output [15:0] WB_NCS,
   output [63:0] WB_CONTROL_STORE,

   output [31:0] WB_ALU32_RESULT,
   output [31:0] WB_FLAGS,
   output [31:0] WB_CMPS_POINTER,
   output [31:0] WB_COUNT, 

   output [2:0] WB_DR1, WB_DR2, WB_DR3
);
   
   //control store
   wire cs_is_cmps_first_uop_all; //0
   wire cs_is_cmps_second_uop_all; //1
   wire [1:0] de_datasize_all; //2-3
   wire cs_is_first_of_repne; //4
   wire de_dr1_write_wb; //5
   wire de_dr2_write_wb; //6
   wire de_dr3_write_wb; //7
   wire [6:0] de_flags_affected_wb; //8-14
   wire [2:0] de_aluk_ex; //15-17

   //internal wires
   wire [31:0] a, b;
   wire [31:0] cmps_first_mem;


   undo_control_store u_undo_control_store(
       cs_is_cmps_first_uop_all, //0
       cs_is_cmps_second_uop_all, //1
       de_datasize_all, //2-3
       cs_is_first_of_repne, //4
       de_dr1_write_wb, //5
       de_dr2_write_wb, //6
       de_dr3_write_wb, //7
       de_flags_affected_wb, //8-14
       de_aluk_ex, //15-17
      EX_CONTROL_STORE
   );

   //Operand_Select_EX
   assign a = EX_A;
   mux32_2way u_select_b(b, EX_B, cmps_first_mem, cs_is_cmps_second_uop_all); 
   
   //String_Support
   reg32e$ u_cmps_temp_mem (CLK, EX_A, cmps_first_mem, , 1'b1, 1'b1, cs_is_cmps_first_uop_all);
   assign WB_CMPS_POINTER = EX_B; 
   assign WB_COUNT = EX_COUNT; 

   //ALU32
   alu32 u_alu32(WB_ALU32_RESULT, WB_FLAGS, a, b, de_aluk_ex);

endmodule
