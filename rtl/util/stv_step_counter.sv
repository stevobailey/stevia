//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Counter with programmable step size
//
// Generic up/down counter with runtime programmable maximum, minimum, and
// step size. The wrap output is high when en == 1 and count+step > max (if
// counting up) or count-step < min (if counting down). A synchronous clear
// resets the counter to its initial value. A synchronous load will set the
// counter to the din input. The MODULO_WRAP parameter changes the wrap
// behavior of the counter. If 0, the counter will always wrap to the min
// input (if counting up) or max input (if counting down). If 1, the counter
// will wrap by continuing to count by the step size, but module the min/max
// range. For example, a min of 0, max of 7, and step of 3 with modulo wrap
// off will count 0, 3, 6, 0, 3, ... and with modulo wrap on will count
// 0, 3, 6, 1, 4, 7, 2, 5, 0, 3, ...
//
// If you only need a step size of 1, use the stv_counter module, as it has
// minor optimizations for this specific condition.
//////////////////////////////////////////////////////////////////////////////

module stv_step_counter #(
  // width of the counter
  parameter int WIDTH       = 8,
  // initial (reset) value
  parameter int INIT_VAL    = 0,
  // modulo wrap instead of wrapping to min/max
  parameter bit MODULO_WRAP = 1'b0
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
  input  logic [WIDTH-1:0] step,

  output logic [WIDTH-1:0] count,
  output logic             wrap
);

  logic        [WIDTH-1:0] counter, counter_next;
  logic signed [WIDTH:0]   smax;
  logic signed [WIDTH:0]   smin;
  logic        [WIDTH:0]   counter_next_up;
  logic signed [WIDTH+1:0] counter_next_down;
  logic signed [WIDTH+1:0] modulo_next_up;
  logic signed [WIDTH+1:0] modulo_next_down;

  always_comb begin
    smax              = $signed({1'b0, max});
    smin              = $signed({1'b0, min});
    counter_next_up   = counter + step;
    counter_next_down = $signed({1'b0, counter}) - $signed({1'b0, step});
    modulo_next_up    = $signed({1'b0, counter_next_up}) + smin - smax - 1;
    modulo_next_down  = counter_next_down + smax - smin + 1;

    counter_next = counter;
    wrap = 1'b0;
    if (clear) begin
      counter_next = INIT_VAL[WIDTH-1:0];
    end else if (load) begin
      counter_next = din;
    end else if (en) begin
      if (down) begin
        /* verilator lint_off WIDTH */
        if (counter_next_down < smin) begin
        /* verilator lint_on WIDTH */
          wrap = 1'b1;
          if (MODULO_WRAP) begin
            counter_next = modulo_next_down[WIDTH-1:0];
          end else begin
            counter_next = max;
          end
        end else begin
          counter_next = counter_next_down[WIDTH-1:0];
        end
      end else begin // up
        /* verilator lint_off WIDTH */
        if (counter_next_up > max) begin
        /* verilator lint_on WIDTH */
          wrap = 1'b1;
          if (MODULO_WRAP) begin
            counter_next = modulo_next_up[WIDTH-1:0];
          end else begin
            counter_next = min;
          end
        end else begin
          counter_next = counter_next_up[WIDTH-1:0];
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

endmodule : stv_step_counter
