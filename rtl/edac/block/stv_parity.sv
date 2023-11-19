//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Parity Generator and Checker
//
// Generates and checks parity bit against the data.
//////////////////////////////////////////////////////////////////////////////

module stv_parity #(
  // input data width
  parameter int WIDTH = 8
) (
  // if 1, generate even parity, otherwise generate odd parity
  input  logic             even,
  // input data
  input  logic [WIDTH-1:0] data_in,
  // input parity to check
  input  logic             parity_in,
  // output calculated parity
  output logic             parity_out,
  // output parity good signal, high if parity check passes, otherwise low
  output logic             parity_good
);

  always_comb begin
    parity_out = even ^ (^data_in);
    parity_good = parity_in == parity_out;
  end

endmodule : stv_parity
