`define cycle 100
`define error_time 1.0
`define runtime #2000

module TOP;
   //mux test inputs
   reg [31:0] a, b, c, d, e, f, g, h;

   reg [2:0] s;

   wire [31:0] out;

   reg error;
   reg error_free;

   initial
      begin
            error_free = 1;
            error = 0;
            a = 32'h00000000;
            b = 32'hffffffff;
            c = 32'ha47ba47b;
            d = 32'h5c915c91;
            e = 32'hbcdabcda;
            f = 32'h96579657;
            g = 32'h34563456;
            h = 32'h09090909;
            s = 3'b000;
         #`cycle //1
            if(out != 32'h00000000) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //2

            error = 0;
            s = 3'b001;
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
      $strobe ("time: %0d found error at: a = %x, b = %x, selection = %x, out = %x", 
         $time, a, b, s, out);
      else
      $strobe ("correct: time: %0d: selection = %x, out = %x", 
         $time, s, out);

    mux32_8way mux_test(out, a, b, c, d, e, f, g, h, s[0], s[1], s[2]);

   
endmodule
