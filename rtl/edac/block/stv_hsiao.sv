//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Hsiao Code Generator and Checker
//
// Calculates Hsiao code for an input. The Hsiao code is an optimal minimum
// odd-weight-column SECDED that reduces hardware overhead compared to the
// extended Hamming code.
//////////////////////////////////////////////////////////////////////////////

`include "stv_edac_functions.svh"

module stv_hsiao #(
  // input data type
  parameter type DTYPE  = logic[3:0],
  // parity length
  parameter int  PWIDTH = 4
) (
  // input data (message)
  input  DTYPE              data_in,
  // generated parity bits
  output logic [PWIDTH-1:0] parity_out
);

//////////////////////////////////////////////////////////////////////////////
// Local parameters
//////////////////////////////////////////////////////////////////////////////

  // input data width
  localparam int DWIDTH = $bits(DTYPE);


//////////////////////////////////////////////////////////////////////////////
// Logic
//////////////////////////////////////////////////////////////////////////////

  logic [DWIDTH-1:0] message;

  // convert to logic
  always_comb begin
    message = data_in;
  end

  // calculate parity
  always_comb begin
    for (int p = 0; p < PWIDTH; p++) begin
      parity_out[p] = 0;
      for (int m = 0; m < DWIDTH; m++) begin
        parity_out[p] ^= (message[m] & stv_hsiao(DWIDTH, PWIDTH, m, p));
      end
    end
  end


//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifndef SYNTHESIS
  initial begin
    assert (PWIDTH >= 1 + $clog2(DWIDTH+PWIDTH))
      else $fatal(1, "Not enough parity bits for Hsiao generator.");
  end
`endif // SYNTHESIS
// pragma translate_on

endmodule : stv_hsiao

