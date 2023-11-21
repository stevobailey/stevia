//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// AES AddRoundKey step
//
//////////////////////////////////////////////////////////////////////////////

module stv_aes_addroundkey (
  input  logic [7:0] data_in [16],
  input  logic [7:0] key_in [16],
  output logic [7:0] data_out [16]
);

  always_comb begin
    for (int i = 0; i < 16; i++) begin
      data_out[i] = data_in[i] ^ key_in[i];
    end
  end

endmodule : stv_aes_addroundkey

