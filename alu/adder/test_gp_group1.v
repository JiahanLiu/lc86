`define cycle 0.35
`define error_time 1.0
`define runtime #20

module TOP;
   //ALU inputs
   reg a, b;

   wire p;

   reg error;
   reg error_free;

   initial
      begin
            error_free = 1;
            error = 0;
            a = 0;
            b = 0;
         #`cycle //1
            if(p != (a | b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //2
            error = 0;
            a = 1;
            b = 0;
         #`cycle //3
            if(p != (a | b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //4
            error = 0;
            a = 0;
            b = 1;
         #`cycle //5
            if(p != (a | b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6
            error = 0;
            a = 1;
            b = 1;
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
	 $vcdplusfile("propagate1.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin
   
   always @(error)
      if(error == 1)
      $strobe ("error at: a = %x, b = %x, propagate1 = %x", 
          a, b, p);

   sum1 propagate1(p, a, b);

   
endmodule
