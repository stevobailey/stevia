//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// AES SubBytes step
//
//////////////////////////////////////////////////////////////////////////////

module stv_aes_subbytes #(
  // bytes to process in one cycle
  parameter int BYTES = 4
) (
  input  logic [7:0] data_in [BYTES],
  input  logic       inverse,
  output logic [7:0] data_out [BYTES]
);

  for (genvar i = 0; i < BYTES; i++) begin: g_sbox
    stv_aes_sbox u_sbox (
      .data_in  (data_in[i] ),
      .inverse  (inverse    ),
      .data_out (data_out[i])
    );
  end

endmodule : stv_aes_subbytes

