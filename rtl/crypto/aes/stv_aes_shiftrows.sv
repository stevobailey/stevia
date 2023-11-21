//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// AES ShiftRows step
//
// Note that the inputs are column-major, so data_in[0] is row 0 column 0,
// data_in[1] is row 1 column 0, etc.
//////////////////////////////////////////////////////////////////////////////

module stv_aes_shiftrows (
  input  logic [7:0] data_in [16],
  input  logic       inverse,
  output logic [7:0] data_out [16]
);

  always_comb begin
    // row 0
    data_out[0] = data_in[0];
    data_out[4] = data_in[4];
    data_out[8] = data_in[8];
    data_out[12] = data_in[12];

    // row 1
    data_out[1] = inverse ? data_in[13] : data_in[5];
    data_out[5] = inverse ? data_in[1] : data_in[9];
    data_out[9] = inverse ? data_in[5] : data_in[13];
    data_out[13] = inverse ? data_in[9] : data_in[1];

    // row 2
    data_out[2] = data_in[10];
    data_out[6] = data_in[14];
    data_out[10] = data_in[2];
    data_out[14] = data_in[6];

    // row 3
    data_out[3] = inverse ? data_in[7] : data_in[15];
    data_out[7] = inverse ? data_in[11] : data_in[3];
    data_out[11] = inverse ? data_in[15] : data_in[7];
    data_out[15] = inverse ? data_in[3] : data_in[11];
  end

endmodule : stv_aes_shiftrows

