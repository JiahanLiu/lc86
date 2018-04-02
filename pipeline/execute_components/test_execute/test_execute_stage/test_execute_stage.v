`define half_cycle 50
`define error_time 1.0
`define runtime #2000

module TOP;
   //input control signals
   reg cs_is_cmps_first_uop_all; //0
   reg cs_is_cmps_second_uop_all; //1
   reg [1:0] de_datasize_all; //2-3
   reg cs_is_first_of_repne; //4
   reg de_dr1_write_wb; //5
   reg de_dr2_write_wb; //6
   reg de_dr3_write_wb; //7
   reg [6:0] de_flags_affected_wb; //8-14
   reg [2:0] de_aluk_ex; //15-17
   //inputs latches
   reg CLK, SET, RST;
   
   reg EX_V; 
   reg [31:0] EX_NEIP;
   reg [15:0] EX_NCS;
   wire [63:0] EX_CONTROL_STORE;

   reg [31:0] EX_A, EX_B;
   reg [31:0] EX_COUNT;

   reg [31:0] EX_ADDRESS;

   reg [2:0] EX_DR1, EX_DR2, EX_DR3;

   //outputs
   wire WB_V;
   wire [31:0] WB_NEIP;
   wire [15:0] WB_NCS;
   wire [63:0] WB_CONTROL_STORE;

   wire [31:0] WB_ALU32_RESULT;
   wire [31:0] WB_FLAGS;
   wire [31:0] WB_CMPS_POINTER;
   wire [31:0] WB_COUNT;

   wire [2:0] WB_DR1, WB_DR2, WB_DR3;

   //simulation result error
   reg error;
   reg error_free;

   make_control_store_line u_make(
   EX_CONTROL_STORE,
    cs_is_cmps_first_uop_all, //0
    cs_is_cmps_second_uop_all, //1
    de_datasize_all, //2-3
    cs_is_first_of_repne, //4
    de_dr1_write_wb, //5
    de_dr2_write_wb, //6
    de_dr3_write_wb, //7
    de_flags_affected_wb, //8-14
    de_aluk_ex //15-17
   );

   initial
      begin
            CLK <= 1; 
            error_free = 1;
            error = 0;
            de_aluk_ex = 3'b000;
            cs_is_cmps_first_uop_all = 0;
            cs_is_cmps_second_uop_all = 0;
            EX_A = 32'hffff_ffff;
            EX_B = 32'h0000_0000;
         #`half_cycle //1
            CLK <= 0; 
            if(WB_ALU32_RESULT != (EX_A + EX_B)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`half_cycle //1
         #`error_time //2

            error = 0;
            EX_A = 32'ha47ba47b;
            EX_B = 32'h5c915c91;
         #`half_cycle //1 //3
            CLK <= 1; 
            if(WB_ALU32_RESULT != (EX_A + EX_B)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`half_cycle //1
            CLK <= 0;
         #`error_time //4

            error = 0;
            EX_A = 32'hbcdabcda;
            EX_B = 32'h79867986;
         #`half_cycle //1
            CLK <= 1;
            if(WB_ALU32_RESULT != (EX_A + EX_B)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`half_cycle //1
            CLK <= 0;   
         #`error_time //6

            error = 0;
            EX_A = 32'h96579657;
            EX_B = 32'h34563456;
         #`half_cycle //1
            CLK <= 1;
            if(WB_ALU32_RESULT != (EX_A + EX_B)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`half_cycle //1
            CLK <= 0;
         if(error_free == 1)
            $display("\n*** WOOT! TEST PASS! ***\n");      
      end
    
   initial `runtime $finish;
   
   // Dump all waveforms to d_latch.dump.vpd
   initial
      begin
	 //$dumpfile ("d_latch.dump");
	 //$dumpvars (0, TOP);
	 $vcdplusfile("test_execute_stage.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin
   
   always @(*)
      if(error == 1)
      $strobe ("time: %0d found error at: a = %x, b = %x, recieved out = %x, correct out = %x", 
          $time, EX_A, EX_B, WB_ALU32_RESULT, (EX_A + EX_B));
      else
      $strobe ("correct: time: %0d: a = %x, b = %x, out = %x", 
          $time, EX_A, EX_B, WB_ALU32_RESULT);

   execute u_execute(
   CLK, SET, RST, //not uesd SET/RST

   EX_V,
   EX_NEIP,
   EX_NCS,
   EX_CONTROL_STORE,

   EX_A, EX_B,
   EX_COUNT, 

   EX_ADDRESS,

   EX_DR1, EX_DR2, EX_DR3,

   WB_V,
   WB_NEIP, 
   WB_NCS,
   WB_CONTROL_STORE,

   WB_ALU32_RESULT,
   WB_FLAGS,
   WB_CMPS_POINTER,
   WB_COUNT, 

   WB_DR1, WB_DR2, WB_DR3
);

endmodule
