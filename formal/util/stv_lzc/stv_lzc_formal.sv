module stv_lzc_formal #(
  parameter  int WIDTH    = 8,
  localparam int CNTWIDTH = $clog2(WIDTH+1)
) ();

  (* anyconst *) logic [WIDTH-1:0] din;
  logic [CNTWIDTH-1:0] count;

  stv_lzc #(
    .WIDTH(WIDTH)
  ) dut (
    .din(din),
    .count(count)
  );

  function automatic logic [CNTWIDTH-1:0] ref_lzc(
    input logic [WIDTH-1:0] value
  );
    logic found_one;
    begin
      ref_lzc = CNTWIDTH'(WIDTH);
      found_one = 1'b0;
      for (int i = WIDTH-1; i >= 0; i--) begin
        if (!found_one && value[i]) begin
          ref_lzc = CNTWIDTH'(WIDTH-1-i);
          found_one = 1'b1;
        end
      end
    end
  endfunction

  always_comb begin
    assert (WIDTH >= 1);
    assert (count == ref_lzc(din));
  end

endmodule : stv_lzc_formal
