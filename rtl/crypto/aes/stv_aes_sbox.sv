//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// AES SBox, both forward and inverse
//
// Uses the combined forward/inverse implementation from Reyhani-Masoleh (see
// https://doi.org/10.1109/TC.2019.2922601). Note that the paper includes even
// more optimal implementations for forward-only and inverse-only versions.
// For simplicity, I just use the combined one. Tying the inverse input to a
// constant will still produce a nearly optimal implementation.
//////////////////////////////////////////////////////////////////////////////

module stv_aes_sbox #(
) (
  input  logic [7:0] data_in,
  input  logic       inverse,
  output logic [7:0] data_out
);

  // rename inputs
  wire g0 = data_in[0];
  wire g1 = data_in[1];
  wire g2 = data_in[2];
  wire g3 = data_in[3];
  wire g4 = data_in[4];
  wire g5 = data_in[5];
  wire g6 = data_in[6];
  wire g7 = data_in[7];

  // input mapping (Table 3, see Remark 1)
  wire ib0 = g0; // flipped
  wire ka1 = g7 ~^ g4;
  wire ka3 = g6 ^ g4;
  wire t0 = g7 ^ g2;
  wire t1 = g6 ^ g0;
  wire ib3 = t1 ~^ g5;
  wire kb0 = t0 ~^ g5; // flipped
  wire kb1 = ka1 ~^ g6;
  wire t2 = t1 ^ g3;
  wire ia0 = ib3 ^ g4;
  wire ia2 = ib3 ^ g7;
  wire ia3 = ib3 ^ g1;
  wire ka2 = t2 ^ g1;
  wire kb3 = ka3 ^ t2;
  wire ia1 = t0 ^ ia3;
  wire ib1 = kb1 ~^ ka2;
  wire ib2 = ka2 ~^ g2;
  wire kb2 = ia0 ^ g1;
  wire ka0 = kb2 ~^ g5;

  // input muxing (see Figure 2 and Remark 1)
  wire a0 = ~(inverse ? ka0 : ia0);
  wire a1 = ~(inverse ? ka1 : ia1);
  wire a2 = ~(inverse ? ka2 : ia2);
  wire a3 = ~(inverse ? ka3 : ia3);
  wire b0 =  (inverse ? kb0 : ib0);
  wire b1 = ~(inverse ? kb1 : ib1);
  wire b2 = ~(inverse ? kb2 : ib2);
  wire b3 = ~(inverse ? kb3 : ib3);

  // exp (Figure 3, also read Section 5.3)
  wire a01 = a0 ^ a1;
  wire a02 = a0 ^ a2;
  wire a13 = a1 ^ a3;
  wire a23 = a2 ^ a3;
  wire ap = a02 ^ a13;
  wire b01 = b0 ^ b1;
  wire b02 = b0 ^ b2;
  wire b13 = b1 ^ b3;
  wire b23 = b2 ^ b3;
  wire bp = b02 ^ b13;
  wire x0 = ~(a01 & b01);
  wire x1 = ~(a02 & b02);
  wire x2 = ~(a0 & b0);
  wire x3 = x0 ^ x1 ^ x2;
  wire x4 = ~(a13 | b13);
  wire d0 = x3 ^ x4;
  wire x5 = ~(a02 | b02);
  wire x6 = ~(a1 & b1);
  wire x7 = x0 ^ x5 ^ x6;
  wire x8 = ~(ap & bp);
  wire d1 = x7 ^ x8;
  wire x9 = ~(a2 | b2);
  wire x10 = ~(a13 & b13);
  wire x11 = ~(a23 & b23);
  wire x12 = x9 ^ x10 ^ x11;
  wire d2 = x12 ^ x1;
  wire x13 = ~(a3 & b3);
  wire x14 = ~(a23 | b23);
  wire x15 = x13 ^ x8 ^ x14;
  wire d3 = x15 ^ x1;

  // inv (Figure 4b)
  wire d2b = ~d2;
  wire d3b = ~d3;
  wire y0 = d0 ^ d1;
  wire y1 = ~y0;
  wire e0 = ~((d0 | d2b) & (d2b | d3b) & (y1 | d3b));
  wire y2 = ~(d1 | d3b);
  wire e1 = ~((y2 | d2b) & (y0 | d2 | d3b));
  wire d0b = ~d0;
  wire d1b = ~d1;
  wire y3 = d2 ^ d3;
  wire y4 = ~y3;
  wire e2 = ~((d2 | d0b) & (d0b | d1b) & (y4 | d1b));
  wire y5 = ~(d3 | d1b);
  wire e3 = ~((y5 | d0b) & (y3 | d0 | d1b));

  // output multipliers (Equations 38 and 39)
  wire e13 = e1 ^ e3;
  wire e02 = e0 ^ e2;
  wire w0p = (~(b1 & e0)) ^ (~(b01 & e1));
  wire w1p = (~(b0 & e1)) ^ (~(b01 & e0));
  wire w2p = (~(b3 & e2)) ^ (~(b23 & e3));
  wire w3p = (~(b2 & e3)) ^ (~(b23 & e2));
  wire w4p = (~(b13 & e13)) ^ (~(b02 & e02));
  wire w5p = (~(bp & e13)) ^ (~(b13 & e02));
  wire z0p = (~(a1 & e0)) ^ (~(a01 & e1));
  wire z1p = (~(a0 & e1)) ^ (~(a01 & e0));
  wire z2p = (~(a3 & e2)) ^ (~(a23 & e3));
  wire z3p = (~(a2 & e3)) ^ (~(a23 & e2));
  wire z4p = (~(a13 & e13)) ^ (~(a02 & e02));
  wire z5p = (~(ap & e13)) ^ (~(a13 & e02));
  wire w0 = w0p ^ w4p;
  wire w1 = w1p ^ w5p;
  wire w2 = w2p ^ w4p;
  wire w3 = w3p ^ w5p;
  wire z0 = z0p ^ z4p;
  wire z1 = z1p ^ z5p;
  wire z2 = z2p ^ z4p;
  wire z3 = z3p ^ z5p;

  // output mapping (Table 7 and see Remark 3)
  wire l0 = z0; // flipped
  wire j7 = w3 ~^ z1;
  wire j6 = w1 ^ z1;
  wire j5 = w0 ^ z2;
  wire l7 = w2 ~^ z3;
  wire l4 = w0 ~^ z3;
  wire l1 = w3 ~^ z3;
  wire j4 = j7 ^ w1;
  wire j1 = l7 ~^ w3;
  wire j0 = l7 ^ w0; // flipped
  wire tt0 = j7 ~^ z0;
  wire j2 = j5 ~^ tt0;
  wire l3 = j0 ^ tt0; // flipped
  wire l2 = j1 ~^ w1;
  wire tt1 = j4 ~^ z3;
  wire j3 = j0 ^ tt1; // flipped
  wire l6 = j5 ~^ tt1;
  wire l5 = j2 ^ w1;

  // output muxing (see Figure 2 and Remark 3)
  wire s0 =  (inverse ? l0 : j0);
  wire s1 = ~(inverse ? l1 : j1);
  wire s2 = ~(inverse ? l2 : j2);
  wire s3 = ~(inverse ? l3 : j3);
  wire s4 = ~(inverse ? l4 : j4);
  wire s5 = ~(inverse ? l5 : j5);
  wire s6 = ~(inverse ? l6 : j6);
  wire s7 = ~(inverse ? l7 : j7);

  // rename outputs
  assign data_out[0] = s0;
  assign data_out[1] = s1;
  assign data_out[2] = s2;
  assign data_out[3] = s3;
  assign data_out[4] = s4;
  assign data_out[5] = s5;
  assign data_out[6] = s6;
  assign data_out[7] = s7;

endmodule : stv_aes_sbox
