//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Priority Arbiter
//
//////////////////////////////////////////////////////////////////////////////

module stv_priority_arbiter #(
  // number of inputs
  parameter int INPUTS = 8
) (
  input  logic [INPUTS-1:0] req,
  output logic [INPUTS-1:0] gnt
);

  logic [INPUTS-1:0] mask;

  always_comb begin
    mask = '0;
    for (int i = 0; i < INPUTS; i++) begin
      for (int j = 0; j < i; j++) begin
        mask[i] |= req[j];
      end
    end
    for (int i = 0; i < INPUTS; i++)
      gnt[i] = req[i] & ~mask[i];
  end

//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifdef STV_ASSERT_ON

  initial begin
    assert (INPUTS > 0) else $fatal(1, "Priority arbiter needs at least 1 input.");
  end

`endif // STV_ASSERT_ON
// pragma translate_on

endmodule : stv_priority_arbiter
