`define cycle 100
`define error_time 1.0
`define runtime #2000

module TOP;
   //ALU inputs
   reg [31:0] a;

   wire [31:0] out;
   //wire [31:0] flags;
   wire carry_out;

   reg error;
   reg error_free;

   initial
      begin
            error_free = 1;
            error = 0;
            a = 32'hffff_ffff;
         #`cycle //1
            if(out != (a + 1)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //2
            error = 0;
            a = 32'ha47ba47b;
         #`cycle //3
            if(out != (a + 1)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //4
            error = 0;
            a = 32'hbcdabcda;
         #`cycle //5
            if(out != (a + 1)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6
            error = 0;
            a = 32'h96579657;
         #`cycle //7
            if(out != (a + 1)) 
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
	 $vcdplusfile("inc_by_1.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin
   
   always @(*)
      if(error == 1)
      $strobe ("time: %0d found error at: a = %x, recieved out = %x, correct out = %x", 
          $time, a, out, (a + 1));
      else
      $strobe ("correct: time: %0d: a = %x, out = %x", 
          $time, a, out);

    inc_by_1 u_inc_by_1 (out, carry_out, a);

endmodule
