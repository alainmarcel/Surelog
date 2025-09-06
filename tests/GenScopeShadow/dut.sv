`default_nettype none

module gate(out);
    wire [3:0] x;
    for (genvar x = 0; x < 2; x++) begin : blk
        localparam w = x;
        if (x == 0) begin : sub
            wire [w:0] x;
        end
    end
    //assign x = 2;
    assign blk[0].sub.x = '1;
    //output wire [9:0] out;
    //assign out = {1'bx, x, blk[0].sub.x};
endmodule

