`define cycle 100
`define error_time 1.0
`define runtime #2000
`define half_cycle 50

module TOP;
   //mux test inputs
   reg [31:0] d;

   reg clk, clr, pre;
   reg [2:0] s;

   wire [31:0] q, qbar;

   reg error;
   reg error_free;

   initial
      begin
            error_free <= 1;
            error <= 0;
            pre <= 1;
            clr <= 0; 
            d <= 0;
            q <= 0;
         #`cycle //1
            if(q != 32'h00000000 || qbar != 32'hffffffff) 
            begin
               error_free = 0;
               error = 1;
            end
            error <= 0;
            d <= 32'habcd1234; 
         #`cycle //3
            if(out != 32'hffffffff) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //4

            error = 0;
            s = 3'b010;
         #`cycle //5
            if(out != 32'ha47ba47b) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6

            error = 0;
            s = 3'b011;
         #`cycle //7
            if(out != 32'h5c915c91) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6

            error = 0;
            s = 3'b100;
         #`cycle //7
            if(out != 32'hbcdabcda) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6

            error = 0;
            s = 3'b101;
         #`cycle //7
            if(out != 32'h96579657) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6

            error = 0;
            s = 3'b110;
         #`cycle //7
            if(out != 32'h34563456) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6
            error = 0;
            s = 3'b111;
         #`cycle //7
            if(out != 32'h09090909) 
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
	 $vcdplusfile("adder.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin
   
   always @(*)
      if(error == 1)
      $strobe ("time: %0d found error at: d = %x, q = %x", 
         $time, a, b, s, out);
      else
      $strobe ("correct: time: %0d: selection = %x, out = %x", 
         $time, s, out);

   always begin
      #`half_cycle clk = ~clk;    
   end

    dff32 dff32_test(clk, d, q, qbar, clr, pre);

   
endmodule
