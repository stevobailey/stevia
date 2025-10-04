//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Gray Counter
//
// Counts in gray-coded values; namely, successive values differ by only 1
// bit. The count is stored gray-coded, meaning it comes directly from a
// register. The wrap output is high when en == 1 and the next count is 0.
// A synchronous clear resets the counter to its initial value. A synchronous
// load will set the counter to the din input. The down option just counts in
// reverse, with wrap high when en == 1 and the counter is 0. Note that wrap 
// is not affected by the INIT_VAL parameter. This counter always counts a 
// power-of-2 number of values.
//////////////////////////////////////////////////////////////////////////////

module stv_gray_counter #(
  // width of the counter
  parameter int WIDTH    = 5,
  // initial (reset) value
  parameter int INIT_VAL = 0
) (
  input                    clk,
  input                    arst_n,

  input  logic             clear,
  input  logic             load,
  input  logic [WIDTH-1:0] din,
  input  logic             en,
  input  logic             down,

  output logic [WIDTH-1:0] count,
  output logic             wrap
);

  logic [WIDTH-1:0] counter, counter_next; 
  logic [WIDTH-1:0] counter_bin;
  logic [WIDTH-1:0] counter_bin_p1;
  logic [WIDTH-1:0] counter_bin_m1;

  always_comb begin
    // convert gray to binary
    for (int i = 0; i < WIDTH; i++)
      counter_bin[i] = ^(counter >> i);

    // binary steps
    counter_bin_p1 = counter_bin + 1;
    counter_bin_m1 = counter_bin - 1;

    // update counter, convert binary to gray
    counter_next = counter;
    wrap = 1'b0;
    if (clear) begin
      counter_next = INIT_VAL[WIDTH-1:0];
    end else if (load) begin
      counter_next = din;
    end else if (en) begin
      if (down) begin
        wrap = counter == 0;
        counter_next = counter_bin_m1 ^ (counter_bin_m1 >> 1);
      end else begin
        wrap = counter == {1'b1, {(WIDTH-1){1'b0}}};
        counter_next = counter_bin_p1 ^ (counter_bin_p1 >> 1);
      end
    end

    count = counter;
  end

  always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      counter <= INIT_VAL[WIDTH-1:0];
    end else begin
      counter <= counter_next;
    end
  end

endmodule : stv_gray_counter
