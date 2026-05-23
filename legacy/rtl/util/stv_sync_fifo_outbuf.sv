//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Synchronous FIFO with dedicated output buffer
//
// Uses ready/valid interfaces. Includes full and empty indicators, and
// current count. The memory is not reset. A SKID parameter cuts the backward
// paths. Specifically, SKID prevents reading and writing on the same cycle
// when full. This outbuf module forces the output to come from a single
// buffer, which should improve downstream timing. Inputs always take at least
// one cycle to appear on the output (i.e. the FLOW parameter is 0).
//////////////////////////////////////////////////////////////////////////////

module stv_sync_fifo_outbuf #(
  // data type
  parameter  type data_t   = logic [7:0],
  // depth, must be > 2
  parameter  int  DEPTH    = 8,
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

  localparam int FIFO_CNTWIDTH = $clog2(DEPTH);

//////////////////////////////////////////////////////////////////////////////
// Base FIFO
//////////////////////////////////////////////////////////////////////////////

  logic                     fifo_din_valid;
  logic                     fifo_din_ready;
  data_t                    fifo_din;
  logic                     fifo_dout_valid;
  logic                     fifo_dout_ready;
  data_t                    fifo_dout;
  logic                     fifo_empty;
  logic                     fifo_full;
  logic [FIFO_CNTWIDTH-1:0] fifo_count;

  always_comb begin
    fifo_din_valid = din_valid;
    din_ready      = fifo_din_ready;
    fifo_din       = din;
  end

  stv_sync_fifo #(
    .data_t     (data_t         ),
    .DEPTH      (DEPTH-1        ),
    .FLOW       (1'b1           ),
    .SKID       (SKID           )
  ) u_fifo_base (
    .clk        (clk            ),
    .arst_n     (arst_n         ),
    .clear      (clear          ),
    .din_valid  (fifo_din_valid ),
    .din_ready  (fifo_din_ready ),
    .din        (fifo_din       ),
    .dout_valid (fifo_dout_valid),
    .dout_ready (fifo_dout_ready),
    .dout       (fifo_dout      ),
    .empty      (fifo_empty     ),
    .full       (fifo_full      ),
    .count      (fifo_count     )
  );

//////////////////////////////////////////////////////////////////////////////
// Output buffer
//////////////////////////////////////////////////////////////////////////////

  logic  buffer_din_valid;
  logic  buffer_din_ready;
  data_t buffer_din;
  logic  buffer_dout_valid;
  logic  buffer_dout_ready;
  data_t buffer_dout;

  always_comb begin
    buffer_din_valid = fifo_dout_valid;
    fifo_dout_ready  = buffer_din_ready;
    buffer_din       = fifo_dout;
  end

  stv_buffer #(
    .data_t     (data_t           ),
    .FLOW       (1'b0             ),
    .SKID       (1'b0             )
  ) u_buffer (
    .clk        (clk              ),
    .arst_n     (arst_n           ),
    .clear      (clear            ),
    .din_valid  (buffer_din_valid ),
    .din_ready  (buffer_din_ready ),
    .din        (buffer_din       ),
    .dout_valid (buffer_dout_valid),
    .dout_ready (buffer_dout_ready),
    .dout       (buffer_dout      )
  );

  always_comb begin
    dout_valid        = buffer_dout_valid;
    buffer_dout_ready = dout_ready;
    dout              = buffer_dout;

    empty = fifo_empty && !buffer_dout_valid;
    full  = fifo_full && buffer_dout_valid;
    count = fifo_count + (buffer_dout_valid ? 1 : 0);
  end

//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifdef STV_ASSERT_ON

  initial begin
    assert (DEPTH > 2)
      else $fatal(1, "Synchronous FIFO (with output buffer) depth must be greater than 2.");
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

endmodule : stv_sync_fifo_outbuf
