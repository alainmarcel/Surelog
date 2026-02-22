module gen_test5(input_bits, out);

parameter WIDTH = 256;
parameter CHUNK = 4;

input [WIDTH-1:0] input_bits;
output out;

genvar step, i, j;
generate
	for (step = 1; step <= WIDTH; step = step * CHUNK) begin : steps
		localparam PREV = step / CHUNK;
		localparam DIM = WIDTH / step;
		for (i = 0; i < DIM; i = i + 1) begin : outer
			localparam LAST_START = i * CHUNK;
			for (j = 0; j < CHUNK; j = j + 1) begin : inner
				wire temp;
				if (step == 1)
					assign temp = input_bits[i];
				else if (j == 0)
					assign temp = steps[PREV].outer[LAST_START].val;
				else
					assign temp
						= steps[step].outer[i].inner[j-1].temp
						& steps[PREV].outer[LAST_START + j].val;
			end
			wire val;
			assign val = steps[step].outer[i].inner[CHUNK - 1].temp;
		end
	end
endgenerate
assign out = steps[WIDTH].outer[0].val;
endmodule

