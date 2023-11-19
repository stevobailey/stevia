//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Hamming Code Generator and Checker
//
// Both generates and checks a Hamming code for a message. The input is
// zero-padded until the message length is sufficiently large for the parity
// length. This Hamming code can detect and correct 1 bit errors.
//////////////////////////////////////////////////////////////////////////////

`include "stv_functions.svh"

module stv_hamming #(
  // input data width
  parameter int WIDTH  = 4,
  // parity length
  parameter int PWIDTH = 3
) (
  // input data (message)
  input  logic [WIDTH-1:0]  data_in,
  // input parity bits
  input  logic [PWIDTH-1:0] parity_in,
  // output data (message, corrected)
  output logic [WIDTH-1:0]  data_out,
  // output parity bits
  output logic [PWIDTH-1:0] parity_out,
  // error position indicator (0 = no error)
  output logic [PWIDTH-1:0] syndrome
);

//////////////////////////////////////////////////////////////////////////////
// Local parameters
//////////////////////////////////////////////////////////////////////////////

  // full data width supported by the algorithm
  localparam int FULLWIDTH = (1 << PWIDTH) - PWIDTH - 1;
  // bits to pad the data width
  localparam int PADWIDTH = FULLWIDTH - WIDTH;


//////////////////////////////////////////////////////////////////////////////
// Logic
//////////////////////////////////////////////////////////////////////////////

  logic [FULLWIDTH-1:0]      message;
  logic [FULLWIDTH+PWIDTH:0] codeword; // 1-indexed, lsb=0

  // zero pad message
  always_comb begin
    message = data_in;
  end

  // calculate parity
  int m;
  always_comb begin
    for (int p = 0; p < PWIDTH; p++) begin
      parity_out[p] = 1;
      m = 0;
      for (int c = 1; c <= FULLWIDTH+PWIDTH; c++) begin
        if (!stv_onehot(c)) begin
          if (|(c & (1<<p)))
            parity_out[p] ^= message[m];
          m += 1;
        end
      end
    end
  end

  // calculate syndrome
  always_comb begin
    syndrome = parity_in ^ parity_out;
  end

  // construct and correct codeword
  int m2;
  always_comb begin
    m2 = 0;
    codeword[0] = 0;
    for (int c = 1; c <= FULLWIDTH+PWIDTH; c++) begin
      if (stv_onehot(c)) begin
        codeword[c] = 0;
      end else begin
        codeword[c] = message[m2];
        m2 += 1;
      end
    end
    codeword[syndrome] ^= 1;
  end

  // reconstruct message
  // verilator lint_off LATCH
  int m3;
  always_comb begin
    m3 = 0;
    for (int c = 1; c <= FULLWIDTH+PWIDTH; c++) begin
      if (!stv_onehot(c)) begin
        data_out[m3] = codeword[c];
        m3 += 1;
      end
    end
  end
  // verilator lint_on LATCH


//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifndef SYNTHESIS
  initial begin
    assert (PADWIDTH >= 0) else $fatal(1, "Not enough parity bits for Hamming generator+checker.");
  end
`endif // SYNTHESIS
// pragma translate_on

endmodule : stv_hamming

