//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// One column of AES MixColumns step
//
// This module only does one column. It uses the small forward implementation
// from Maximov (https://eprint.iacr.org/2019/833.pdf). For the inverse, it
// preprocesses the input then reuses the forward logic. For more on the
// preprocessor, see https://eprint.iacr.org/2016/927.pdf.
//////////////////////////////////////////////////////////////////////////////

module stv_aes_mixcolumn (
  input  logic [7:0] data_in [4],
  input  logic       inverse,
  output logic [7:0] data_out [4]
);

  // inverse preprocessor
  wire [7:0] xx02 = data_in[0] ^ data_in[2];
  wire [7:0] xx13 = data_in[1] ^ data_in[3];
  wire [7:0] xxt02;
  wire xx02_67 = xx02[6] ^ xx02[7];
  assign xxt02[0] = xx02[6];
  assign xxt02[1] = xx02_67;
  assign xxt02[2] = xx02[0] ^ xx02[7];
  assign xxt02[3] = xx02[1] ^ xx02[6];
  assign xxt02[4] = xx02[2] ^ xx02_67;
  assign xxt02[5] = xx02[3] ^ xx02[7];
  assign xxt02[6] = xx02[4];
  assign xxt02[7] = xx02[5];
  wire [7:0] xxt13;
  wire xx13_67 = xx13[6] ^ xx13[7];
  assign xxt13[0] = xx13[6];
  assign xxt13[1] = xx13_67;
  assign xxt13[2] = xx13[0] ^ xx13[7];
  assign xxt13[3] = xx13[1] ^ xx13[6];
  assign xxt13[4] = xx13[2] ^ xx13_67;
  assign xxt13[5] = xx13[3] ^ xx13[7];
  assign xxt13[6] = xx13[4];
  assign xxt13[7] = xx13[5];
  wire [7:0] yy0 = xxt02 ^ data_in[0];
  wire [7:0] yy1 = xxt13 ^ data_in[1];
  wire [7:0] yy2 = xxt02 ^ data_in[2];
  wire [7:0] yy3 = xxt13 ^ data_in[3];

  // forward logic inputs
  wire x0 = inverse ? yy0[0] : data_in[0][0];
  wire x1 = inverse ? yy0[1] : data_in[0][1];
  wire x2 = inverse ? yy0[2] : data_in[0][2];
  wire x3 = inverse ? yy0[3] : data_in[0][3];
  wire x4 = inverse ? yy0[4] : data_in[0][4];
  wire x5 = inverse ? yy0[5] : data_in[0][5];
  wire x6 = inverse ? yy0[6] : data_in[0][6];
  wire x7 = inverse ? yy0[7] : data_in[0][7];
  wire x8 = inverse ? yy1[0] : data_in[1][0];
  wire x9 = inverse ? yy1[1] : data_in[1][1];
  wire x10 = inverse ? yy1[2] : data_in[1][2];
  wire x11 = inverse ? yy1[3] : data_in[1][3];
  wire x12 = inverse ? yy1[4] : data_in[1][4];
  wire x13 = inverse ? yy1[5] : data_in[1][5];
  wire x14 = inverse ? yy1[6] : data_in[1][6];
  wire x15 = inverse ? yy1[7] : data_in[1][7];
  wire x16 = inverse ? yy2[0] : data_in[2][0];
  wire x17 = inverse ? yy2[1] : data_in[2][1];
  wire x18 = inverse ? yy2[2] : data_in[2][2];
  wire x19 = inverse ? yy2[3] : data_in[2][3];
  wire x20 = inverse ? yy2[4] : data_in[2][4];
  wire x21 = inverse ? yy2[5] : data_in[2][5];
  wire x22 = inverse ? yy2[6] : data_in[2][6];
  wire x23 = inverse ? yy2[7] : data_in[2][7];
  wire x24 = inverse ? yy3[0] : data_in[3][0];
  wire x25 = inverse ? yy3[1] : data_in[3][1];
  wire x26 = inverse ? yy3[2] : data_in[3][2];
  wire x27 = inverse ? yy3[3] : data_in[3][3];
  wire x28 = inverse ? yy3[4] : data_in[3][4];
  wire x29 = inverse ? yy3[5] : data_in[3][5];
  wire x30 = inverse ? yy3[6] : data_in[3][6];
  wire x31 = inverse ? yy3[7] : data_in[3][7];

  wire t0 = x0 ^ x8;
  wire t1 = x16 ^ x24;
  wire t2 = x1 ^ x9;
  wire t3 = x17 ^ x25;
  wire t4 = x2 ^ x10;
  wire t5 = x18 ^ x26;
  wire t6 = x3 ^ x11;
  wire t7 = x19 ^ x27;
  wire t8 = x4 ^ x12;
  wire t9 = x20 ^ x28;
  wire t10 = x5 ^ x13;
  wire t11 = x21 ^ x29;
  wire t12 = x6 ^ x14;
  wire t13 = x22 ^ x30;
  wire t14 = x23 ^ x31;
  wire t15 = x7 ^ x15;
  wire t16 = x8 ^ t1;
  wire y0 = t15 ^ t16;
  wire t17 = x7 ^ x23;
  wire t18 = x24 ^ t0;
  wire y16 = t14 ^ t18;
  wire t19 = t1 ^ y16;
  wire y24 = t17 ^ t19;
  wire t20 = x27 ^ t14;
  wire t21 = t0 ^ y0;
  wire y8 = t17 ^ t21;
  wire t22 = t5 ^ t20;
  wire y19 = t6 ^ t22;
  wire t23 = x11 ^ t15;
  wire t24 = t7 ^ t23;
  wire y3 = t4 ^ t24;
  wire t25 = x2 ^ x18;
  wire t26 = t17 ^ t25;
  wire t27 = t9 ^ t23;
  wire t28 = t8 ^ t20;
  wire t29 = x10 ^ t2;
  wire y2 = t5 ^ t29;
  wire t30 = x26 ^ t3;
  wire y18 = t4 ^ t30;
  wire t31 = x9 ^ x25;
  wire t32 = t25 ^ t31;
  wire y10 = t30 ^ t32;
  wire y26 = t29 ^ t32;
  wire t33 = x1 ^ t18;
  wire t34 = x30 ^ t11;
  wire y22 = t12 ^ t34;
  wire t35 = x14 ^ t13;
  wire y6 = t10 ^ t35;
  wire t36 = x5 ^ x21;
  wire t37 = x30 ^ t17;
  wire t38 = x17 ^ t16;
  wire t39 = x13 ^ t8;
  wire y5 = t11 ^ t39;
  wire t40 = x12 ^ t36;
  wire t41 = x29 ^ t9;
  wire y21 = t10 ^ t41;
  wire t42 = x28 ^ t40;
  wire y13 = t41 ^ t42;
  wire y29 = t39 ^ t42;
  wire t43 = x15 ^ t12;
  wire y7 = t14 ^ t43;
  wire t44 = x14 ^ t37;
  wire y31 = t43 ^ t44;
  wire t45 = x31 ^ t13;
  wire y15 = t44 ^ t45;
  wire y23 = t15 ^ t45;
  wire t46 = t12 ^ t36;
  wire y14 = y6 ^ t46;
  wire t47 = t31 ^ t33;
  wire y17 = t19 ^ t47;
  wire t48 = t6 ^ y3;
  wire y11 = t26 ^ t48;
  wire t49 = t2 ^ t38;
  wire y25 = y24 ^ t49;
  wire t50 = t7 ^ y19;
  wire y27 = t26 ^ t50;
  wire t51 = x22 ^ t46;
  wire y30 = t11 ^ t51;
  wire t52 = x19 ^ t28;
  wire y20 = x28 ^ t52;
  wire t53 = x3 ^ t27;
  wire y4 = x12 ^ t53;
  wire t54 = t3 ^ t33;
  wire y9 = y8 ^ t54;
  wire t55 = t21 ^ t31;
  wire y1 = t38 ^ t55;
  wire t56 = x4 ^ t17;
  wire t57 = x19 ^ t56;
  wire y12 = t27 ^ t57;
  wire t58 = x3 ^ t28;
  wire t59 = t17 ^ t58;
  wire y28 = x20 ^ t59;

  // rename outputs
  assign data_out[0][0] = y0;
  assign data_out[0][1] = y1;
  assign data_out[0][2] = y2;
  assign data_out[0][3] = y3;
  assign data_out[0][4] = y4;
  assign data_out[0][5] = y5;
  assign data_out[0][6] = y6;
  assign data_out[0][7] = y7;
  assign data_out[1][0] = y8;
  assign data_out[1][1] = y9;
  assign data_out[1][2] = y10;
  assign data_out[1][3] = y11;
  assign data_out[1][4] = y12;
  assign data_out[1][5] = y13;
  assign data_out[1][6] = y14;
  assign data_out[1][7] = y15;
  assign data_out[2][0] = y16;
  assign data_out[2][1] = y17;
  assign data_out[2][2] = y18;
  assign data_out[2][3] = y19;
  assign data_out[2][4] = y20;
  assign data_out[2][5] = y21;
  assign data_out[2][6] = y22;
  assign data_out[2][7] = y23;
  assign data_out[3][0] = y24;
  assign data_out[3][1] = y25;
  assign data_out[3][2] = y26;
  assign data_out[3][3] = y27;
  assign data_out[3][4] = y28;
  assign data_out[3][5] = y29;
  assign data_out[3][6] = y30;
  assign data_out[3][7] = y31;

endmodule : stv_aes_mixcolumn

