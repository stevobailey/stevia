//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Leading zero counter
//
// This module counts leading zeros. It uses the "high speed" counter from:
// https://electronics.stackexchange.com/questions/196914/
// verilog-synthesize-high-speed-leading-zero-count
//
// First, encode bits 2 by 2 :
//
//     00 => 10 : 2 leading zeros
//     01 => 01 : 1 leading zero
//     10 => 00 : 0 leading zero
//     11 => 00 : 0 leading zero
//
// Then, assemble as pairs.
//
//     If both sides start with 1xxx, the result is 10...0
//     If the left side start with 0 the result is 0[left]
//     If the left side starts with 1, the result is 01[right(msb-1:0)]
//
// When the input is not a power-of-2, it one-pads the LSBs until it hits the
// next power-of-2. It alternates the polarity of stages in the tree, which
// produced slightly better synthesized results in a 64-bit test case.
//////////////////////////////////////////////////////////////////////////////

module stv_lzc #(
  parameter  int WIDTH    = 2,
  localparam int CNTWIDTH = $clog2(WIDTH+1)
) (
  input  logic [WIDTH-1:0]    din,
  output logic [CNTWIDTH-1:0] count
);

  // adjust parameters for small values
  localparam int WIDTH_MIN2 = (WIDTH == 1) ? 2 : WIDTH;
  localparam int WIDTH_POW2 = 1 << $clog2(WIDTH_MIN2);
  localparam int PADWIDTH = WIDTH_POW2 - WIDTH;
  localparam int DEPTH = $clog2(WIDTH_POW2);

  logic [WIDTH_POW2-1:0]                       in_tmp;
  // nodes in the tree are organized as row, group, value
  logic [DEPTH-1:0][WIDTH_POW2/2-1:0][DEPTH:0] nodes;

  always_comb begin
    // pad the input to the next power-of-2
    in_tmp = {din, {PADWIDTH{1'b1}}};

    // zero out all nodes; most are unused
    nodes = '0;

    // initial encoding
    for (int i = 0; i < WIDTH_POW2/2; i++) begin
      nodes[0][i][0] = (in_tmp[i*2 +: 2] == 2'b01) ^ !DEPTH[0];
      nodes[0][i][1] = (in_tmp[i*2 +: 2] == 2'b00) ^ !DEPTH[0];
    end

    // assemble the layers
    for (int row = 1; row < DEPTH; row++) begin
      // og is the output group number
      for (int og = 0; og < WIDTH_POW2/(1 << (row+1)); og++) begin
        // left group starts with 0
        if (!nodes[row-1][og*2+1][row] ^ !row[0] ^ !DEPTH[0]) begin
          // output = {1'b0, left[msb:0]}
          for (int j = 0; j < row+1; j++) begin
            nodes[row][og][j] = !nodes[row-1][og*2+1][j];
          end
          nodes[row][og][row+1] = row[0] ^ !DEPTH[0];
        // right group starts with 0
        end else if (!nodes[row-1][og*2][row] ^ !row[0] ^ !DEPTH[0]) begin
          // output = {2'b01, right[msb-1:0]}
          for (int j = 0; j < row; j++) begin
            nodes[row][og][j] = !nodes[row-1][og*2][j];
          end
          nodes[row][og][row] = !row[0] ^ !DEPTH[0];
          nodes[row][og][row+1] = row[0] ^ !DEPTH[0];
        // both groups start with 1
        end else begin
          // output = {1'b1, zeros[msb:0]}
          for (int j = 0; j < row+1; j++) begin
            nodes[row][og][j] = row[0] ^ !DEPTH[0];
          end
          nodes[row][og][row+1] = !row[0] ^ !DEPTH[0];
        end
      end
    end

    // output
    count = nodes[DEPTH-1][0][CNTWIDTH-1:0];
  end

//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifndef SYNTHESIS
  initial begin
    assert (WIDTH >= 1) else $fatal(1, "LZC data width must be at least 1.");
  end
`endif // SYNTHESIS
// pragma translate_on

endmodule : stv_lzc
