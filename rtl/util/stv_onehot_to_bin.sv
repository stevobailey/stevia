////////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// One-hot to unsigned binary integer converter
//
////////////////////////////////////////////////////////////////////////////////

module stv_onehot_to_bin #(
  parameter  int ONEHOT_WIDTH = 1,
  localparam int BIN_WIDTH    = (ONEHOT_WIDTH == 1) ? 1 : $clog2(ONEHOT_WIDTH)
) (
  input  logic [ONEHOT_WIDTH-1:0] onehot,
  output logic [BIN_WIDTH-1:0]    bin
);

  logic [BIN_WIDTH-1:0][ONEHOT_WIDTH-1:0] mask;

  always_comb begin
    for (int i = 0; i < BIN_WIDTH; i++) begin
      for (int j = 0; j < ONEHOT_WIDTH; j++) begin
        mask[i][j] = j[i];
      end
      bin[i] = |(mask[i] & onehot);
    end
  end

//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifdef ASSERT_ON

  initial begin
    assume (ONEHOT_WIDTH > 0) else $fatal(1, "ONEHOT width must be greater than 0");
  end

  onehot_is_onehot: assume property ($onehot0(onehot))
    else $warning(1, "Onehot signal is not onehot!"); 

`endif // ASSERT_ON
// pragma translate_on

endmodule : stv_onehot_to_bin
