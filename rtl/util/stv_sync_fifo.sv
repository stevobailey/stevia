//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Synchronous FIFO
//
// Uses ready/valid interfaces. Includes full and empty indicators, and
// current count. The memory is not reset. FLOW and SKID parameters cut
// the forward and backward paths. Specifically, FLOW allows reading and
// writing on the same cycle when empty, and SKID prevents reading and
// writing on the same cycle when full. This base module uses a basic
// architecture, where inputs are written directly to the next memory
// location, and outputs are read from their current memory location.
//////////////////////////////////////////////////////////////////////////////

module stv_sync_fifo #(
  // data type
  parameter  type data_t   = logic [7:0],
  // depth, must be > 1
  parameter  int  DEPTH    = 8,
  // allows reading and writing on the same cycle when empty
  parameter  bit  FLOW     = 1'b0,
  // prevents reading and writing on the same cycle when full
  parameter  bit  SKID     = 1'b0,
  // count signal width
  localparam int  CNTWIDTH = $clog2(DEPTH+1)
) (
  input                       clk,
  input                       arst_n,

  // synchronous reset
  input  logic                clear,

  // push
  input  logic                din_valid,
  output logic                din_ready,
  input  data_t               din,

  // pop
  output logic                dout_valid,
  input  logic                dout_ready,
  output data_t               dout,

  // meta
  output logic                empty,
  output logic                full,
  output logic [CNTWIDTH-1:0] count
);


//////////////////////////////////////////////////////////////////////////////
// Local parameters
//////////////////////////////////////////////////////////////////////////////

  localparam bit DEPTH_IS_POW2 = (DEPTH & (DEPTH-1)) == 0;
  localparam int PTRWIDTH      = $clog2(DEPTH);

//////////////////////////////////////////////////////////////////////////////
// Logic
//////////////////////////////////////////////////////////////////////////////

  // memory
  data_t mem [DEPTH];

  // pointers
  logic [PTRWIDTH-1:0] wptr, wptr_next;
  logic [PTRWIDTH-1:0] rptr, rptr_next;
  logic [PTRWIDTH-1:0] ptr_diff;

  // internal
  logic ptr_match;
  logic maybe_full, maybe_full_next;
  logic reading;
  logic writing;

  // control signals and IO
  always_comb begin
    ptr_match = wptr == rptr;

    maybe_full_next = maybe_full;
    if (clear)
      maybe_full_next = 1'b0;
    else if (!ptr_match)
      maybe_full_next = !dout_ready;

    empty = ptr_match && !maybe_full;
    full  = ptr_match &&  maybe_full;

    ptr_diff = wptr - rptr;
    count = CNTWIDTH'(((!DEPTH_IS_POW2 && (rptr > wptr)) || full) ? DEPTH : 0) + ptr_diff;

    reading = dout_ready && !empty;
    writing = din_valid && (!FLOW || !empty || !dout_ready) && (!full || (!SKID && dout_ready));

    din_ready  = !full || (!SKID && dout_ready);
    dout_valid = !empty || (FLOW && din_valid);
    dout       = (FLOW && empty) ? din : mem[rptr];
  end

  // pointer logic
  always_comb begin
    // write pointer
    wptr_next = wptr;
    if (clear) begin
      wptr_next = 0;
    end else if (writing) begin
      if ((!DEPTH_IS_POW2) && (wptr == PTRWIDTH'(DEPTH-1)))
        wptr_next = 0;
      else
        wptr_next = wptr + 1;
    end

    // read pointer
    rptr_next = rptr;
    if (clear) begin
      rptr_next = 0;
    end else if (reading) begin
      if ((!DEPTH_IS_POW2) && (rptr == PTRWIDTH'(DEPTH-1)))
        rptr_next = 0;
      else
        rptr_next = rptr + 1;
    end
  end

  // registers
  always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      maybe_full <= 1'b0;
      wptr       <= '0;
      rptr       <= '0;
    end else begin
      maybe_full <= maybe_full_next;
      wptr       <= wptr_next;
      rptr       <= rptr_next;
    end
  end

  // memory
  always_ff @(posedge clk) begin
    if (writing)
      mem[wptr] <= din;
  end

//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifdef STV_ASSERT_ON

  initial begin
    assert (DEPTH > 1) else $fatal(1, "Synchronous FIFO depth must be greater than 1.");
  end

  default disable iff (!arst_n);

  valid_stable: assert property ( @(posedge clk)
    (!clear && din_valid && !din_ready) |=> din_valid)
    else $fatal(1, "Valid unstable");

  data_stable: assert property ( @(posedge clk)
    (!clear && din_valid && !din_ready) |=> $stable(din))
    else $fatal(1, "Data unstable");

`endif // STV_ASSERT_ON
// pragma translate_on

endmodule : stv_sync_fifo
