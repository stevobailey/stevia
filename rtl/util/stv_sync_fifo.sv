//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Synchronous FIFO
//
// Uses ready/valid interfaces. Includes full and empty indicators, and
// current count. The memory is not reset.
//
// FLOW controls the forward valid/data path. FLOW=1 allows fallthrough when
// the FIFO is empty, so a push and pop can occur in the same cycle.
//
// SKID controls the reverse ready path. SKID=1 cuts ready coupling when full,
// so a full FIFO cannot accept a push in the same cycle as a pop.
//
// This base module uses a basic architecture, where inputs are written directly
// to the next memory location, and outputs are read from their current memory
// location.
//////////////////////////////////////////////////////////////////////////////

module stv_sync_fifo #(
  // data width
  parameter  int  WIDTH    = 8,
  // depth, must be > 1
  parameter  int  DEPTH    = 8,
  // allows reading and writing on the same cycle when empty
  parameter  int  FLOW     = 0,
  // prevents reading and writing on the same cycle when full
  parameter  int  SKID     = 0,
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
  input  logic [WIDTH-1:0]    din,

  // pop
  output logic                dout_valid,
  input  logic                dout_ready,
  output logic [WIDTH-1:0]    dout,

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

  function automatic logic [PTRWIDTH-1:0] ptr_next(
    input logic [PTRWIDTH-1:0] ptr
  );
    if ((!DEPTH_IS_POW2) && (ptr == PTRWIDTH'(DEPTH-1)))
      ptr_next = '0;
    else
      ptr_next = ptr + 1'b1;
  endfunction

//////////////////////////////////////////////////////////////////////////////
// Logic
//////////////////////////////////////////////////////////////////////////////

  // memory
  logic [WIDTH-1:0] mem [DEPTH];

  // pointers
  logic [PTRWIDTH-1:0] wptr;
  logic [PTRWIDTH-1:0] rptr;
  logic [PTRWIDTH-1:0] ptr_diff;

  // internal
  logic ptr_match;
  logic maybe_full;
  logic reading;
  logic writing;

  // control signals and IO
  always_comb begin
    ptr_match = wptr == rptr;

    empty = ptr_match && !maybe_full;
    full  = ptr_match &&  maybe_full;

    ptr_diff = wptr - rptr;
    count = CNTWIDTH'(((!DEPTH_IS_POW2 && (rptr > wptr)) || full) ? DEPTH : 0) + ptr_diff;

    reading = dout_ready && !empty;
    writing = din_valid && ((FLOW == 0) || !empty || !dout_ready)
              && (!full || ((SKID == 0) && dout_ready));

    din_ready  = !full || ((SKID == 0) && dout_ready);
    dout_valid = !empty || ((FLOW != 0) && din_valid);
    dout       = ((FLOW != 0) && empty) ? din : mem[rptr];
  end

  // registers
  always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      maybe_full <= 1'b0;
      wptr       <= '0;
      rptr       <= '0;
    end else if (clear) begin
      maybe_full <= 1'b0;
      wptr       <= '0;
      rptr       <= '0;
    end else begin
      // When the pointers differ, the operation that closes the distance
      // determines whether the next pointer match means full or empty. Writing
      // this in terms of the current pointer relationship and downstream ready
      // keeps the maybe_full D path smaller than an equivalent push/pop update.
      if (!ptr_match)
        maybe_full <= !dout_ready;

      if (writing)
        wptr <= ptr_next(wptr);
      if (reading)
        rptr <= ptr_next(rptr);
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
`ifndef SYNTHESIS

  initial begin
    assert (WIDTH >= 1) else $fatal(1, "Synchronous FIFO width must be at least 1.");
    assert (DEPTH > 1) else $fatal(1, "Synchronous FIFO depth must be greater than 1.");
    assert ((FLOW == 0) || (FLOW == 1)) else $fatal(1, "Synchronous FIFO FLOW must be 0 or 1.");
    assert ((SKID == 0) || (SKID == 1)) else $fatal(1, "Synchronous FIFO SKID must be 0 or 1.");
  end

`endif // SYNTHESIS

`ifdef STV_ASSERT_ON

  default disable iff (!arst_n);

  input_valid_stable: assert property ( @(posedge clk)
    (!clear && din_valid && !din_ready) |=> din_valid)
    else $fatal(1, "Input valid changed under backpressure.");

  input_data_stable: assert property ( @(posedge clk)
    (!clear && din_valid && !din_ready) |=> $stable(din))
    else $fatal(1, "Input data changed under backpressure.");

  output_valid_stable: assert property ( @(posedge clk)
    (!clear && dout_valid && !dout_ready) |=> dout_valid)
    else $fatal(1, "Output valid changed under backpressure.");

  output_data_stable: assert property ( @(posedge clk)
    (!clear && dout_valid && !dout_ready) |=> $stable(dout))
    else $fatal(1, "Output data changed under backpressure.");

  clear_resets_metadata: assert property ( @(posedge clk)
    clear |=> (empty && !full && (count == '0)))
    else $fatal(1, "Synchronous FIFO metadata was not cleared.");

  empty_count_zero: assert property ( @(posedge clk)
    empty |-> (count == '0))
    else $fatal(1, "Synchronous FIFO empty did not imply count zero.");

  full_count_depth: assert property ( @(posedge clk)
    full |-> (count == CNTWIDTH'(DEPTH)))
    else $fatal(1, "Synchronous FIFO full did not imply count depth.");

  no_simultaneous_full_empty: assert property ( @(posedge clk)
    !(full && empty))
    else $fatal(1, "Synchronous FIFO was both full and empty.");

  bounded_count: assert property ( @(posedge clk)
    count <= CNTWIDTH'(DEPTH))
    else $fatal(1, "Synchronous FIFO count exceeded depth.");

`endif // STV_ASSERT_ON
// pragma translate_on

endmodule : stv_sync_fifo
