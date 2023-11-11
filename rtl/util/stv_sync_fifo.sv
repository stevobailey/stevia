//////////////////////////////////////////////////////////////////////////////
// Synchronous FIFO
//
// Uses ready/valid interfaces. Includes full and empty indicators, and
// current count. The memory is not reset. The depth must be a power of 2.
// A FLOWTHROUGH parameter allows for reading and writing on the same cycle
// when full or empty, which can increase performance but creates
// combinational timing paths between inputs and outputs. The data type is
// parameterized.
//////////////////////////////////////////////////////////////////////////////

module stv_sync_fifo #(
  // data type
  parameter  type        DTYPE       = logic[7:0],
  // depth, must be a power of 2 and > 1
  parameter  logic[31:0] DEPTH       = 8,
  // allows reading and writing on the same cycle when full or empty
  parameter  bit         FLOWTHROUGH = 0,
  // pointer width
  localparam logic[31:0] PTRWIDTH    = $clog2(DEPTH)
) (
  input  logic              clk,
  input  logic              arst_n,

  input  logic              rready,
  output logic              rvalid,
  output DTYPE              rdata,

  input  logic              wvalid,
  output logic              wready,
  input  DTYPE              wdata,

  output logic              empty,
  output logic              full,
  output logic [PTRWIDTH:0] count
);

  // memory
  DTYPE mem [DEPTH];

  // pointers
  logic [PTRWIDTH:0] wptr, wptr_next;
  logic [PTRWIDTH:0] rptr, rptr_next;

  // internal
  logic ptr_match, ptr_msb_match;
  logic reading, writing;

  // empty, full, and count logic
  always_comb begin
    ptr_match     = wptr[PTRWIDTH-1:0] == rptr[PTRWIDTH-1:0];
    ptr_msb_match = wptr[PTRWIDTH] == rptr[PTRWIDTH];
    empty         = ptr_match &&  ptr_msb_match;
    full          = ptr_match && !ptr_msb_match;
    count         = {full, wptr[PTRWIDTH-1:0] - rptr[PTRWIDTH-1:0]};
  end

  // control signals
  always_comb begin
    wready  = !full  || (FLOWTHROUGH && rready);
    rvalid  = !empty || (FLOWTHROUGH && wvalid);
    writing = wvalid && ((FLOWTHROUGH && rready) ? !empty : !full);
    reading = rready && !empty;
  end

  // pointer updates
  always_comb begin
    wptr_next = wptr + {{(PTRWIDTH-1){1'b0}}, writing};
    rptr_next = rptr + {{(PTRWIDTH-1){1'b0}}, reading};
  end

  always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      wptr <= '0;
      rptr <= '0;
    end else begin
      wptr <= wptr_next;
      rptr <= rptr_next;
    end
  end

  // write to memory
  always_ff @(posedge clk) begin
    if (writing)
      mem[wptr[PTRWIDTH-1:0]] <= wdata;
  end

  // output read data from memory
  always_comb
    rdata = (FLOWTHROUGH && empty) ? wdata : mem[rptr[PTRWIDTH-1:0]];


//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifndef SYNTHESIS
  initial begin
    assert (DEPTH > 1)      else $fatal(1, "Synchronous FIFO depth must be greater than 1.");
    assert ($onehot(DEPTH)) else $fatal(1, "Synchronous FIFO depth must be a power of 2.");
  end
`endif // SYNTHESIS
// pragma translate_on

endmodule : stv_sync_fifo
