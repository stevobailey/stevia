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

  // use unpacked array and for loops to avoid verilator complaints
  logic mask [INPUTS];

  always_comb begin
    mask[0] = 1'b0;
    for (int i = 1; i < INPUTS; i++)
      mask[i] = mask[i-1] | req[i-1];
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
