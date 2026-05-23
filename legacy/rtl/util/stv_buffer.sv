//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Buffer
//
// Uses ready/valid interfaces. Optionally cuts forward and/or backward logic
// paths. If both are cut, the buffer is twice as deep.
//
// FLOW=0, SKID=0 => pipeline, cuts forward paths
// FLOW=0, SKID=1 => skid buffer, cuts both forward and backward paths
// FLOW=1, SKID=0 => no timing benefit, but can absorb 1 cycle bubble
// FLOW=1, SKID=1 => reverse pipeline, cuts backward paths
//////////////////////////////////////////////////////////////////////////////

module stv_buffer #(
  // data type
  parameter type data_t = logic [7:0],
  // when 0, cuts the valid and data (feed forward) signals
  parameter bit  FLOW   = 1'b0,
  // when 1, cuts the ready (feedback) signals
  parameter bit  SKID   = 1'b0,
  // not much faster, but cuts some logic at the cost of power
  parameter bit  FAST   = 1'b0
) (
  input         clk,
  input         arst_n,

  // synchronous reset
  input  logic  clear,

  // initiator side
  input  logic  din_valid,
  output logic  din_ready,
  input  data_t din,

  // target side
  output logic  dout_valid,
  input  logic  dout_ready,
  output data_t dout
);

  // separate state bits to simplify logic optimization
  logic state_stream, state_stream_next;
  logic state_skid, state_skid_next;

  // buffers
  data_t pipe, pipe_next;
  data_t skid, skid_next;

  always_comb begin
    // default register feedback
    state_stream_next = state_stream;
    state_skid_next = state_skid;
    pipe_next = pipe;
    skid_next = skid;

    // enumerate all 4 flow/skid options to ensure correct optimizations
    if (!FLOW && !SKID) begin // forward pipeline

      // state update
      if (clear)
        state_stream_next = 1'b0;
      else if (din_valid || dout_ready)
        state_stream_next = din_valid;

      // buffer update
      if (FAST) begin
        if (!state_stream || dout_ready)
          pipe_next = din;
      end else begin
        if (din_valid && (!state_stream || dout_ready))
          pipe_next = din;
      end

      // outputs
      din_ready = !state_stream || dout_ready;
      dout_valid = state_stream;
      dout = pipe;

    end else if (!FLOW && SKID) begin // skid buffer

      // state updates
      if (clear) begin
        state_stream_next = 1'b0;
        state_skid_next = 1'b0;
      end else if (din_valid || dout_ready) begin
        state_stream_next = state_skid || din_valid;
        state_skid_next = state_stream && !dout_ready;
      end

      // buffer updates
      if (FAST) begin
        if (!state_stream || dout_ready)
          pipe_next = state_skid ? skid : din;
        if (!state_skid)
          skid_next = din;
      end else begin
        if ((state_skid || din_valid) && (!state_stream || dout_ready))
          pipe_next = state_skid ? skid : din;
        if (!state_skid && state_stream && din_valid && !dout_ready)
          skid_next = din;
      end

      // outputs
      din_ready = !state_skid;
      dout_valid = state_stream;
      dout = pipe;

    end else if (FLOW && !SKID) begin // feedthrough buffer

      // state update
      if (clear)
        state_stream_next = 1'b0;
      else if (din_valid ^ dout_ready)
        state_stream_next = din_valid;

      // buffer update
      if (FAST) begin
        if (!state_stream || dout_ready)
          pipe_next = din;
      end else begin
        if (din_valid && (state_stream == dout_ready))
          pipe_next = din;
      end

      // outputs
      din_ready = !state_stream || dout_ready;
      dout_valid = state_stream || din_valid;
      dout = state_stream ? pipe : din;

    end else begin // reverse pipeline

      // state udpate
      if (clear)
        state_skid_next = 1'b0;
      else if (din_valid || dout_ready)
        state_skid_next = !dout_ready;

      // buffer update
      if (FAST) begin
        if (!state_skid)
          skid_next = din;
      end else begin
        if (!state_skid && din_valid && !dout_ready)
          skid_next = din;
      end

      // outputs
      din_ready = !state_skid;
      dout_valid = state_skid || din_valid;
      dout = state_skid ? skid : din;
    end
  end

  // state registers
  always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      state_stream <= 1'b0;
      state_skid   <= 1'b0;
    end else begin
      state_stream <= state_stream_next;
      state_skid   <= state_skid_next;
    end
  end

  // buffers do not need to be reset
  always_ff @(posedge clk) begin
    pipe <= pipe_next;
    skid <= skid_next;
  end

//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifdef STV_ASSERT_ON

  default disable iff (!arst_n);

  valid_stable: assert property ( @(posedge clk)
    (!clear && din_valid && !din_ready) |=> din_valid)
    else $fatal(1, "Valid unstable");

  data_stable: assert property ( @(posedge clk)
    (!clear && din_valid && !din_ready) |=> $stable(din))
    else $fatal(1, "Data unstable");

`endif // STV_ASSERT_ON
// pragma translate_on

endmodule : stv_buffer
