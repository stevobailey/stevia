//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// AES data generator
//
// This module combines all compute blocks with control logic to process each
// AES round and output an encrypted or decrypted block. It does not generate
// round keys. It is designed to be combined with a round key generator or a
// round key look-up table. It works with any key length.
//
//       inverse
//  data   |
//   |     |
//   V     V
// -----------       ----------
// |         |       |        |
// |   AES   | round |  AES   |
// | Datagen | <---> | Keygen |
// |         |  key  |        |
// |         |       |        |
// -----------       ----------
//     |
//     V
//    data
//
// Round counts from 0 to N (encryption) or N to 0 (decryption). The first
// round (0 or N) is always the initial AddRoundKey, and subsequent rounds
// count up or down. So AES128 starts with round = 0 (encryption) and counts
// to round = 10. For decryption, AES128 starts with round = 10 and counts to
// round = 0.
//////////////////////////////////////////////////////////////////////////////

import stv_aes_pkg::*;

module stv_aes_datagen (
  input  logic            clk,
  input  logic            arst_n,

  // control signals
  // these are latched when data_valid_in and data_ready_out are both high
  input  stv_aes_keylen_t keylen,
  input  logic            inverse,

  // status signals
  output logic            busy,
  output logic [3:0]      round,

  // data input interface
  input  logic [7:0]      data_in [16],
  input  logic            data_valid_in,
  output logic            data_ready_out,

  // key interface
  input  logic [7:0]      key_in [16],
  input  logic            key_valid_in,
  output logic            key_ready_out,

  // data output interface
  output logic [7:0]      data_out [16],
  output logic            data_valid_out,
  input  logic            data_ready_in
);


//////////////////////////////////////////////////////////////////////////////
// Declarations
//////////////////////////////////////////////////////////////////////////////

  // local signals
  logic            fire_in;  // valid & ready
  logic            fire_out; // valid & ready
  logic            fire_key; // valid & ready
  logic            first_round, last_round;

  // submodule signals
  logic [7:0]      subbytes_out [16];
  logic [7:0]      shiftrows_out [16];
  logic [7:0]      mixcolumns_out [16];
  logic [7:0]      addroundkey_in [16];
  logic [7:0]      addroundkey_out [16];

  // registers and register updates
  logic            busy_next;
  logic            done, done_next;
  stv_aes_keylen_t keylen_reg, keylen_reg_next;
  logic [3:0]      round_next;
  logic            inverse_reg, inverse_reg_next;
  logic [7:0]      data [16];
  logic [7:0]      data_next [16];


//////////////////////////////////////////////////////////////////////////////
// Submodules
//////////////////////////////////////////////////////////////////////////////

  stv_aes_subbytes #(
    .BYTES    (16          )
  ) u_subbytes (
    .data_in  (data        ),
    .inverse  (inverse_reg ),
    .data_out (subbytes_out)
  );

  stv_aes_shiftrows u_shiftrows (
    .data_in  (subbytes_out ),
    .inverse  (inverse_reg  ),
    .data_out (shiftrows_out)
  );

  stv_aes_mixcolumns u_mixcolumns (
    .data_in  (shiftrows_out ),
    .inverse  (inverse_reg   ),
    .bypass   (last_round    ),
    .data_out (mixcolumns_out)
  );

  stv_aes_addroundkey u_addroundkey (
    .data_in  (addroundkey_in ),
    .key_in   (key_in         ),
    .data_out (addroundkey_out)
  );


//////////////////////////////////////////////////////////////////////////////
// Control logic
//////////////////////////////////////////////////////////////////////////////

  // local signals
  always_comb begin
    fire_in  = data_valid_in  && data_ready_out;
    fire_out = data_valid_out && data_ready_in;
    fire_key = key_valid_in   && key_ready_out;
    case (keylen_reg)
      AES128:  last_round = inverse_reg ? (round == 0) : (round == 4'd10);
      AES192:  last_round = inverse_reg ? (round == 0) : (round == 4'd12);
      AES256:  last_round = inverse_reg ? (round == 0) : (round == 4'd14);
      default: last_round = 0;
    endcase
    case (keylen_reg)
      AES128:  first_round = inverse_reg ? (round == 4'd10) : (round == 0);
      AES192:  first_round = inverse_reg ? (round == 4'd12) : (round == 0);
      AES256:  first_round = inverse_reg ? (round == 4'd14) : (round == 0);
      default: first_round = 0;
    endcase
  end

  // submodule signals
  always_comb begin
    for (int i = 0; i < 16; i++)
      addroundkey_in[i] = first_round ? data[i] : mixcolumns_out[i];
  end

  // busy
  always_comb begin
    if (fire_in)
      busy_next = 1;
    else if (fire_out)
      busy_next = 0;
    else
      busy_next = busy;
  end

  // done
  always_comb begin
    if (fire_key && last_round)
      done_next = 1;
    else if (fire_out)
      done_next = 0;
    else
      done_next = done;
  end

  // keylen
  always_comb begin
    if (fire_in)
      keylen_reg_next = keylen;
    else
      keylen_reg_next = keylen_reg;
  end

  // round
  always_comb begin
    if (fire_in) begin
      if (inverse) begin
        case (keylen)
          AES128:  round_next = 4'd10;
          AES192:  round_next = 4'd12;
          AES256:  round_next = 4'd14;
          default: round_next = 0;
        endcase
      end else
        round_next = 0;
    end else if (fire_key && !last_round)
      round_next = inverse_reg ? (round - 1) : (round + 1);
    else
      round_next = round;
  end

  // inverse
  always_comb begin
    if (fire_in)
      inverse_reg_next = inverse;
    else
      inverse_reg_next = inverse_reg;
  end

  // data
  always_comb begin
    data_next = data;
    if (fire_in)
      for (int i = 0; i < 16; i++)
        data_next[i] = data_in[i];
    else if (fire_key)
      for (int i = 0; i < 16; i++)
        data_next[i] = addroundkey_out[i];
  end


//////////////////////////////////////////////////////////////////////////////
// IO
//////////////////////////////////////////////////////////////////////////////

  always_comb begin
    data_ready_out = !busy;
    key_ready_out  = busy && !done;
    data_valid_out = done;
    for (int i = 0; i < 16; i++)
      data_out[i] = data[i];
  end


//////////////////////////////////////////////////////////////////////////////
// Registers
//////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      busy <= '0;
      done <= '0;
    end else begin
      busy <= busy_next;
      done <= done_next;
    end
  end

  always_ff @(posedge clk) begin
    keylen_reg  <= keylen_reg_next;
    round       <= round_next;
    inverse_reg <= inverse_reg_next;
    for (int i = 0; i < 16; i++)
      data[i] <= data_next[i];
  end

endmodule : stv_aes_datagen

