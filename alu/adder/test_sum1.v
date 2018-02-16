`define cycle 1.0
`define error_time 1.0
`define runtime #20

module TOP;
   //ALU inputs
   reg a, b, c;

   wire sum1;

   reg error;
   reg error_free;

   initial
      begin
            error_free = 1;
            error = 0;
            a = 0;
            b = 0;
            c = 0;
         #`cycle //1
            if(sum1 != a^b^c) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //2
            error = 0;
            a = 1;
            b = 0;
            c = 0;
         #`cycle //3
            if(sum1 != a^b^c) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //4
            error = 0;
            a = 0;
            b = 1;
            c = 0;
         #`cycle //5
            if(sum1 != a^b^c) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6
            error = 0;
            a = 0;
            b = 0;
            c = 1;
         #`cycle //7
            if(sum1 != a^b^c) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //8
            error = 0;
            a = 1;
            b = 1;
            c = 0;
         #`cycle //9
            if(sum1 != a^b^c) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //10
            error = 0;
            a = 1;
            b = 0;
            c = 1;
         #`cycle //11
            if(sum1 != a^b^c) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //12
            error = 0;
            a = 0;
            b = 1;
            c = 1;
         #`cycle //13
            if(sum1 != a^b^c) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //14
            error = 0;
            a = 1;
            b = 1;
            c = 1;
         #`cycle //15
            if(sum1 != a^b^c) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //16
         if(error_free == 1)
            $display("\n*** WOOT! TEST PASS! ***\n");      
      end
    
   initial `runtime $finish;
   
   // Dump all waveforms to d_latch.dump.vpd
   initial
      begin
	 //$dumpfile ("d_latch.dump");
	 //$dumpvars (0, TOP);
	 $vcdplusfile("sum1.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin
   
   always @(error)
      if(error == 1)
      $strobe ("error at: a = %x, b = %x, c = %x, sum = %x", 
          a, b, c, sum1);

   sum1 sum1_test(sum1, a, b, c);

   
endmodule
