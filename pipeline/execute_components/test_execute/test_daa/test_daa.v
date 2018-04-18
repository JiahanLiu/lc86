`define cycle 100
`define error_time 1.0
`define runtime #2000

module TOP;
   //ALU inputs
   reg [31:0] a, b;
   reg [2:0] op;
   reg CF_dataforwarded;
   reg AF_dataforwarded;

   wire [31:0] out;
   wire [31:0] flags;

   reg error;
   reg error_free;

   initial
      begin
            CF_dataforwarded = 0; 
            AF_dataforwarded = 0; 
            error_free = 1;
            error = 0;
            op = 3'b011;
            a = 32'h0000_00AE;
            b = 32'h0000_0000;
         #`cycle //1
            if(out != 32'h0000_0014) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //2
            error = 0;
            a = 32'h0000_002E;
            b = 32'h0000_0000;
         #`cycle //3
            if(out != 32'h0000_0034) 
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
	 $vcdplusfile("daa.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin
   
   always @(*)
      if(error == 1)
      $strobe ("time: %0d found error at: a = %x, b = %x, recieved out = %x", 
          $time, a, b, out);
      else
      $strobe ("correct: time: %0d: a = %x, b = %x, out = %x", 
          $time, a, b, out);

    alu32 u_alu_test (out, flags, a, b, op, CF_dataforwarded, AF_dataforwarded);

endmodule
