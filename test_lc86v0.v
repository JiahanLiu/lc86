`define cycle 100
`define error_time 1.0
`define runtime #2000

module TOP;
   reg [31:0] EAX, ECX; 
   //GA Latches
   reg [31:0] GA_drid, GA_srid, GA_imm;

   //SO Latches
   reg [31:0] SO_drid, SO_srid, SO_imm;

   //E Latches
   reg [31:0] E_drid, E_srid, E_imm;

   //WB Latches
   reg [31:0] WB_drid, WB_srid, WB_imm;


   wire [31:0] out;
   wire [3:0] flags;

   reg error;
   reg error_free;

   initial
      begin
            error_free = 1;
            error = 0;
            op = 3'b000;
            a = 32'hffffffff;
            b = 32'h00000000;
         #`cycle //1
            if(out != (a + b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //2
            error = 0;
            a = 32'ha47ba47b;
            b = 32'h5c915c91;
         #`cycle //3
            if(out != (a + b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //4
            error = 0;
            a = 32'hbcdabcda;
            b = 32'h79867986;
         #`cycle //5
            if(out != (a + b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6
            error = 0;
            a = 32'h96579657;
            b = 32'h34563456;
         #`cycle //7
            if(out != (a + b)) 
            begin
               error_free = 0;
               error = 1;
            end
         if(error_free == 1)
            $display("\n*** WOOT! TEST PASS! ***\n");      
      end
    
   initial `runtime $finish;
   
   // Dump all waveforms to d_latch.dump.vpd
   initial
      begin
	 //$dumpfile ("d_latch.dump");
	 //$dumpvars (0, TOP);
	 $vcdplusfile("alu.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin
   
   always @(*)
      if(error == 1)
      $strobe ("time: %0d found error at: a = %x, b = %x, recieved out = %x, correct out = %x", 
          $time, a, b, out, (a + b));
      else
      $strobe ("correct: time: %0d: a = %x, b = %x, out = %x", 
          $time, a, b, out);

    alu alu_test (out, flags, a, b, op);

   
endmodule
