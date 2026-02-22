// Test parenthesized type variable declaration: (type) varname;
module enum_paren_type(input clk, input rst);

  typedef enum logic [1:0] {
    ts0, ts1, ts2, ts3
  } states_t;

  states_t state;
  (states_t) state1;
  states_t enum_const = ts1;

  always @(posedge clk) begin
    if (rst) begin
      state <= ts0;
    end else begin
      if (state == ts0)
        state <= ts1;
      else if (state == ts1)
        state <= ts2;
      else if (state == ts2)
        state <= ts0;
    end
  end

endmodule
