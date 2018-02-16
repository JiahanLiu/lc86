`define cycle .35
`define error_time 1.0
`define runtime #2000

module TOP;
   //ALU inputs
   reg [31:0] a, b;

   wire [31:0] p;

   reg error;
   reg error_free;

   initial
      begin
            error_free = 1;
            error = 0;
            a = 32'hffffffff;
            b = 32'h00000000;
         #`cycle //1
            if(p != (a | b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //2
            error = 0;
            a = 32'ha47ba47b;
            b = 32'h5c915c91;
         #`cycle //3
            if(p != (a | b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //4
            error = 0;
            a = 32'hbcdabcda;
            b = 32'h79867986;
         #`cycle //5
            if(p != (a | b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6
            error = 0;
            a = 32'h96579657;
            b = 32'h34563456;
         #`cycle //7
            if(p != (a | b)) 
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
	 $vcdplusfile("propagate32.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin
   
   always @(error)
      if(error == 1)
      $strobe ("time: %0d found error at: a = %x, b = %x, propagate1 = %x, correct propagate1 = %x", 
          $time, a, b, p, (a | b));

   propagate32 propagate32_test(p, a, b);

   
endmodule
