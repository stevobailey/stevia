//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Counter
//
// Generic up/down counter with runtime programmable maximum and minimum. The
// wrap output is high when en == 1 and count == max (if counting up) or
// count == min (if counting down). A synchronous clear resets the counter to
// its initial value. A synchronous load will set the counter to the din input.
// This counter always counts up or down in steps of 1. If the counter value
// is outside the range of min and max, it will continue to count until it
// wraps around and enters the min/max range again.
//////////////////////////////////////////////////////////////////////////////

module stv_counter #(
  // width of the counter
  parameter int WIDTH    = 8,
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
  input  logic [WIDTH-1:0] max,
  input  logic [WIDTH-1:0] min,

  output logic [WIDTH-1:0] count,
  output logic             wrap
);

  logic [WIDTH-1:0] counter, counter_next;

  always_comb begin
    counter_next = counter;
    wrap = 1'b0;
    if (clear) begin
      counter_next = INIT_VAL[WIDTH-1:0];
    end else if (load) begin
      counter_next = din;
    end else if (en) begin
      if (down) begin
        if (counter == min) begin
          wrap = 1'b1;
          counter_next = max;
        end else begin
          counter_next = counter - 1;
        end
      end else begin // up
        if (counter == max) begin
          wrap = 1'b1;
          counter_next = min;
        end else begin
          counter_next = counter + 1;
        end
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

//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifndef SYNTHESIS
  initial begin
    assert (WIDTH >= 1) else $fatal(1, "Counter width must be at least 1.");
  end
`endif // SYNTHESIS
// pragma translate_on

endmodule : stv_counter
