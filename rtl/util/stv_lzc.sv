//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Leading zero counter
//
// This module counts leading zeros. A zero input returns WIDTH. The
// implementation intentionally favors broad open-source tool compatibility over
// a more complex tree structure.
//////////////////////////////////////////////////////////////////////////////

module stv_lzc #(
  parameter  int WIDTH    = 2,
  localparam int CNTWIDTH = $clog2(WIDTH+1)
) (
  input  logic [WIDTH-1:0]    din,
  output logic [CNTWIDTH-1:0] count
);

  logic found_one;

  always_comb begin
    count = CNTWIDTH'(WIDTH);
    found_one = 1'b0;

    for (int i = WIDTH-1; i >= 0; i--) begin
      if (!found_one && din[i]) begin
        count = CNTWIDTH'(WIDTH-1-i);
        found_one = 1'b1;
      end
    end
  end

//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifndef SYNTHESIS
  initial begin
    assert (WIDTH >= 1) else $fatal(1, "LZC data width must be at least 1.");
  end
`endif // SYNTHESIS
// pragma translate_on

endmodule : stv_lzc
