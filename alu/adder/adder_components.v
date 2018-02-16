//-----------------------------------------------------

// 1-bit Adder

//-----------------------------------------------------
// Functionality:
// Combinational Delay: 1.0ns
//

module sum1 (sum, a, b, c);
	output sum;
	input a, b, c;

	wire a_not, b_not, c_not;
	wire a_asserted, b_asserted, c_asserted, all_asserted;

	inv1$ not_a (a_not, a);
	inv1$ not_b (b_not, b);
	inv1$ not_c (c_not, c);

	and3$ and_a_asserted (a_asserted, a, b_not, c_not);
	and3$ and_b_asserted (b_asserted, a_not, b, c_not);
	and3$ and_c_asserted (c_asserted, a_not, b_not, c);
	and3$ and_all_asserted (all_asserted, a, b, c);
	or4$ or_asserted (sum, a_asserted, b_asserted, c_asserted, all_asserted);

endmodule // sum1

//-----------------------------------------------------

// 1-bit Propgate

//-----------------------------------------------------
// Functionality: Can a carry possibily propgate?
// Combinational Delay: 0.35ns
//

module propagate1 (p, a, b);
	output p;
	input a. b;

	or2$ or_to_p (p, a, b);

endmodule // propagate1

//-----------------------------------------------------

// 1-bit Generate

//-----------------------------------------------------
// Functionality: Generate 
// Combinational Delay: 0.35ns
//

module generate1 (g, a, b);
	output g;
	input a, b;

	and2$ and_to_g (g, a, b);

endmodule // generate1

//-----------------------------------------------------

// 1-bit gp_group1

//-----------------------------------------------------
// Functionality: Kogge-Stone Component 
// Combinational Delay: 0.7ns?
//

module gp_group1 (g_out, p_out, g_in_high, p_in_high, g_in_low, p_in_low);
	output g_out, p_out;
	input g_in_high, p_in_high, g_in_low, p_in_low;

	wire prev_generate;

	and2$ and_to_propagate (p_out, p_in_low, p_in_high);
	and2$ and_prev_generate (prev_generate, g_in_low, p_in_high);
	and2$ or_to_generate (g_out, prev_generate, g_in_high);

endmodule // gp_group1






