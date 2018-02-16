`define cycle 0.75
`define error_time 1.0
`define runtime #2000

module TOP;
   //ALU inputs
   reg g_in_high, p_in_high, g_in_low, p_in_low;

   wire g_out, p_out;

   reg error;
   reg error_free;

   initial
      begin
            error_free = 1;
            error = 0;
            g_in_high = 0;
            p_in_high = 0;
            g_in_low = 0;
            p_in_low = 0;
         #`cycle //1
            if(p_out != (p_in_high & p_in_low) || g_out != ((p_in_high & g_in_low) | g_in_high)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //2
            error = 0;
            g_in_high = 1;
            p_in_high = 0;
            g_in_low = 0;
            p_in_low = 0;
         #`cycle //3
            if(p_out != (p_in_high & p_in_low) || g_out != ((p_in_high & g_in_low) | g_in_high)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //4
            error = 0;
            g_in_high = 0;
            p_in_high = 1;
            g_in_low = 0;
            p_in_low = 0;
         #`cycle //5
            if(p_out != (p_in_high & p_in_low) || g_out != ((p_in_high & g_in_low) | g_in_high)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6
            error = 0;
            g_in_high = 0;
            p_in_high = 1;
            g_in_low = 1;
            p_in_low = 1;
         #`cycle //7
            if(p_out != (p_in_high & p_in_low) || g_out != ((p_in_high & g_in_low) | g_in_high)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //8
            error = 0;
            g_in_high = 0;
            p_in_high = 1;
            g_in_low = 1;
            p_in_low = 0;
         #`cycle //9
            if(p_out != (p_in_high & p_in_low) || g_out != ((p_in_high & g_in_low) | g_in_high)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //10
            error = 0;
            g_in_high = 0;
            p_in_high = 0;
            g_in_low = 1;
            p_in_low = 1;
         #`cycle //11
            if(p_out != (p_in_high & p_in_low) || g_out != ((p_in_high & g_in_low) | g_in_high)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //12
            error = 0;
            g_in_high = 0;
            p_in_high = 1;
            g_in_low = 0;
            p_in_low = 0;
         #`cycle //13
            if(p_out != (p_in_high & p_in_low) || g_out != ((p_in_high & g_in_low) | g_in_high)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //14
            error = 0;
            g_in_high = 1;
            p_in_high = 0;
            g_in_low = 1;
            p_in_low = 1;
         #`cycle //15
            if(p_out != (p_in_high & p_in_low) || g_out != ((p_in_high & g_in_low) | g_in_high)) 
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
    $vcdplusfile("gp_group1.dump.vpd");
    $vcdpluson(0, TOP); 
      end // initial begin
   
   always @(error)
      if(error == 1)
      $strobe ("time: %0d found error at: p_in_low = %x, g_in_low = %x, p_in_high = %x, g_in_high = %x, p_out = %x, g_out = %x", 
          $time, p_in_low, g_in_low, p_in_high, g_in_high, p_out, g_out);

   gp_group1 test_gp_group1(g_out, p_out, g_in_high, p_in_high, g_in_low, p_in_low);

   
endmodule
