module func_width_scope_top(inp, out1, out2);
	input wire signed inp;

	localparam WIDTH_A = 5;
  
	generate
		if (1) begin : blk
			localparam WIDTH_A = 6;
			function automatic [WIDTH_A-1:0] func2;
				input reg [WIDTH_A-1:0] inp;
				func2 = ~inp;
			endfunction
			wire [func2(0)-1:0] yc;
                  
		end
	endgenerate

endmodule
