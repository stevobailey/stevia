//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// General purpose functions
//
//////////////////////////////////////////////////////////////////////////////

`ifndef __STV_FUNCTIONS__
`define __STV_FUNCTIONS__

// unsigned int onehot
// can be used in generate blocks to avoid $onehot but is not synthesizeable
function automatic bit stv_onehot(int n); 
  stv_onehot = 0;
  for (int g = 0; g < 32; g++) begin
    if (n == (1 << g)) begin
      stv_onehot = 1;
    end 
  end 
endfunction

// factorial
function automatic int stv_factorial(int n); 
  stv_factorial = 1;
  for (int i = 2; i <= n; i++) begin
    stv_factorial *= i;
  end
endfunction

// combination
function automatic int stv_comb(int n, int k); 
  stv_comb = stv_factorial(n)/(stv_factorial(k) * stv_factorial(n-k));
endfunction

`endif // __STV_FUNCTIONS__

