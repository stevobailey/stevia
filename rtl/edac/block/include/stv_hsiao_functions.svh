//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Functions for generating the HSIAO SECDED parity check matrix
//
//////////////////////////////////////////////////////////////////////////////

`ifndef __STV_HSIAO_FUNCTIONS_H__
`define __STV_HSIAO_FUNCTIONS_H__

`include "stv_functions.svh"

typedef bit stv_edac_2d_array[][];

//////////////////////////////////////////////////////////////////////////////
// Hsiao parity check matrix generator
//////////////////////////////////////////////////////////////////////////////

// merge two matrices left and right
function automatic stv_edac_2d_array stv_hsiao_lr_union(stv_edac_2d_array a, stv_edac_2d_array b); 
  stv_hsiao_lr_union = new[a.size];
  foreach (stv_hsiao_lr_union[i])
    stv_hsiao_lr_union[i] = new[a[0].size + b[0].size];
  for (int i = 0; i < a.size; i++) begin
    for (int j = 0; j < a[0].size; j++) begin
      stv_hsiao_lr_union[i][j] = a[i][j];
    end 
    for (int j = 0; j < b[0].size; j++) begin
      int out_col = j + a[0].size;
      stv_hsiao_lr_union[i][out_col] = b[i][j];
    end 
  end 
endfunction

// merge two matrices top and bottom
function automatic stv_edac_2d_array stv_hsiao_ud_union(stv_edac_2d_array a, stv_edac_2d_array b); 
  stv_hsiao_ud_union = new[a.size + b.size];
  foreach (stv_hsiao_ud_union[i])
    stv_hsiao_ud_union[i] = new[a[0].size];
  for (int i = 0; i < a.size; i++) begin
    for (int j = 0; j < a[0].size; j++) begin
      stv_hsiao_ud_union[i][j] = a[i][j];
    end 
  end 
  for (int i = 0; i < b.size; i++) begin
    for (int j = 0; j < b[0].size; j++) begin
      int out_row = i + a.size;
      stv_hsiao_ud_union[out_row][j] = b[i][j];
    end 
  end 
endfunction

// flip a matrix vertically
function automatic stv_edac_2d_array stv_hsiao_flip(stv_edac_2d_array a); 
  stv_hsiao_flip = new[a.size];
  foreach (stv_hsiao_flip[i])
    stv_hsiao_flip[i] = new[a[0].size];
  for (int i = 0; i < a.size; i++) begin
    for (int j = 0; j < a[0].size; j++) begin
      int row_inv = a.size - i - 1;
      stv_hsiao_flip[i][j] = a[row_inv][j];
    end 
  end 
endfunction

// sort a matrix's rows by the number of 1s in each row
// rows with more 1s are placed at the top
function automatic stv_edac_2d_array stv_hsiao_sort(stv_edac_2d_array a); 
  int row_sums[];
  int prev_sum = -1; 
  int sum_row_cnt = 0;
  int row_cnt = 0;
  int curr_sum = 0;
  stv_hsiao_sort = new[a.size];
  row_sums = new[a.size];
  foreach (row_sums[i])
    row_sums[i] = int'(a[i].sum);
  row_sums.rsort;
  for (int i = 0; i < stv_hsiao_sort.size; i++) begin
    stv_hsiao_sort[i] = new[a[0].size];
    curr_sum = row_sums[i];
    if (curr_sum == prev_sum) begin
      sum_row_cnt += 1;
    end else begin
      sum_row_cnt = 0;
      prev_sum = curr_sum;
    end 
    row_cnt = 0;
    for (int j = 0; j < a.size; j++) begin
      if (a[j].sum == curr_sum) begin
        if (row_cnt == sum_row_cnt) begin
          for (int k = 0; k < a[0].size; k++) begin
            stv_hsiao_sort[i][k] = a[j][k];
          end
          break;
        end else begin
          row_cnt += 1;
        end
      end 
    end 
  end 
endfunction

// recursively generate parity check matrix
// https://arxiv.org/pdf/0803.1217.pdf
function automatic stv_edac_2d_array stv_hsiao_recurse(int r, int j, int m); 

  // variables
  int m1, m2; 
  stv_edac_2d_array a, b1, b2, c, d;

  //$display("recurse(%d, %d, %d)", r, j, m);

  // degenerate cases
  if (m == 0) begin
    // return empty array
  end else if (j == 0) begin
    stv_hsiao_recurse = new[r];
    for (int i = 0; i < r; i++) begin
      stv_hsiao_recurse[i] = new[m];
      for (int k = 0; k < m; k++) begin
        stv_hsiao_recurse[i][k] = 0;
      end 
    end 
  end else if (m == 1) begin
    stv_hsiao_recurse = new[r];
    for (int i = 0; i < j; i++) begin
      stv_hsiao_recurse[i] = new[1];
      stv_hsiao_recurse[i][0] = 1;
    end 
    for (int i = j; i < r; i++) begin
      stv_hsiao_recurse[i] = new[1];
      stv_hsiao_recurse[i][0] = 0;
    end 
  end else if (j == 1) begin
    stv_hsiao_recurse = new[r];
    for (int i = 0; i < r; i++) begin
      stv_hsiao_recurse[i] = new[m];
      for (int k = 0; k < m; k++) begin
        stv_hsiao_recurse[i][k] = 0;
      end 
    end 
    for (int i = 0; i < m; i++) begin
      stv_hsiao_recurse[i][i] = 1;
    end 
  end else if (j == (r-1)) begin
    stv_hsiao_recurse = new[r];
    for (int i = 0; i < r; i++) begin
      stv_hsiao_recurse[i] = new[m];
      for (int k = 0; k < m; k++) begin
        stv_hsiao_recurse[i][k] = 1;
      end 
    end 
    for (int i = 0; i < m; i++) begin
      stv_hsiao_recurse[r-m+i][i] = 0;
    end 
  end else begin

    // decompose
    m1 = (m*j+r-1)/r;
    m2 = m - m1; 
    a = new[1];
    a[0] = new[m];
    for (int i = 0; i < m1; i++) begin
      a[0][i] = 1;
    end
    for (int i = m1; i < m; i++) begin
      a[0][i] = 0;
    end
    b1 = stv_hsiao_recurse(r-1, j-1, m1);
    b2 = stv_hsiao_recurse(r-1, j, m2);

    // special operator
    c = stv_hsiao_lr_union(b1, stv_hsiao_flip(b2));
    d = stv_hsiao_sort(c);
    stv_hsiao_recurse = stv_hsiao_ud_union(a, d);

  end

endfunction

// Hsiao SECDED parity check matrix function
// k = total message width
// p = total parity bits
// k_bit = message bit index
// p_bit = parity bit index
// returns 1 if this parity bit protects this message bit, otherwise 0
function automatic bit stv_hsiao(int k, int p, int k_bit, int p_bit);

  // variables
  stv_edac_2d_array h, a;
  int k2 = k;
  int j = 3;
  int m;

  // construct parity check matrix h
  h = new[p];
  while (k2 > 0) begin
    m = stv_comb(p, j);
    if (k2 < m)
      m = k2;
    a = stv_hsiao_recurse(p, j, m);
    h = stv_hsiao_lr_union(h, a);
    k2 -= m;
    j += 2;
  end

  for (int i = 0; i < h.size; i++) begin
    $write("[");
    for (int j = 0; j < h[0].size; j++) begin
      $write("%01d", h[i][j]);
      if (j == h[0].size-1) begin
        $display("]");
      end else begin
        $write(", ");
      end
    end
  end

  // return entry
  stv_hsiao = h[p_bit][k_bit];
endfunction

`endif // __STV_HSIAO_FUNCTIONS_H__
