//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// AES MixColumns step
//
// Note that the inputs are column-major, so data_in[0] is row 0 column 0,
// data_in[1] is row 1 column 0, etc. It includes a bypass signal, which just
// passes the input through with no changes. This is useful for the final
// rounds where MixColumns is not used.
//////////////////////////////////////////////////////////////////////////////

module stv_aes_mixcolumns (
  input  logic [7:0] data_in [16],
  input  logic       inverse,
  input  logic       bypass,
  output logic [7:0] data_out [16]
);

  logic [7:0] mixcolumns_out [16];

  for (genvar i = 0; i < 4; i++) begin: g_mixcol
    stv_aes_mixcolumn u_mixcolumn (
      .data_in  (data_in[i*4:i*4+3]       ),
      .inverse  (inverse                  ),
      .data_out (mixcolumns_out[i*4:i*4+3])
    );
  end

  always_comb begin
    for (int i = 0; i < 16; i++) begin
      data_out[i] = bypass ? data_in[i] : mixcolumns_out[i];
    end
  end

endmodule : stv_aes_mixcolumns

