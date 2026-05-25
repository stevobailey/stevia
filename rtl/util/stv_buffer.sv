//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Ready/valid elastic buffer.
//
// FLOW controls the forward valid/data path:
//   FLOW=0 cuts the forward path with a registered output.
//   FLOW=1 allows forward fallthrough when the buffer is empty.
//
// SKID controls the reverse ready path:
//   SKID=0 allows ready to couple backward through the buffer.
//   SKID=1 cuts the ready path and adds skid storage where needed.
//
// Modes:
//   FLOW=0, SKID=0 => forward pipeline, cuts valid/data
//   FLOW=0, SKID=1 => skid buffer, cuts valid/data and ready
//   FLOW=1, SKID=0 => fallthrough buffer, couples valid/data and ready
//   FLOW=1, SKID=1 => reverse pipeline, cuts ready
//////////////////////////////////////////////////////////////////////////////

module stv_buffer #(
  // data width
  parameter int  WIDTH         = 8,
  // allow forward valid/data fallthrough when empty
  parameter int  FLOW          = 0,
  // cut the reverse ready path
  parameter int  SKID          = 0,
  // favor smaller/faster data-path logic at the cost of extra register toggles
  parameter int  OPT_AREA_TIMING = 0
) (
  input         clk,
  input         arst_n,

  // synchronous reset
  input  logic  clear,

  // initiator side
  input  logic  din_valid,
  output logic  din_ready,
  input  logic [WIDTH-1:0] din,

  // target side
  output logic  dout_valid,
  input  logic  dout_ready,
  output logic [WIDTH-1:0] dout
);

  // state_stream tracks data in the forward output register.
  // state_skid tracks data in the reverse-path skid register.
  logic state_stream, state_stream_next;
  logic state_skid, state_skid_next;

  logic [WIDTH-1:0] pipe, pipe_next;
  logic [WIDTH-1:0] skid, skid_next;

  generate
    if ((FLOW == 0) && (SKID == 0)) begin : gen_forward_pipeline
      always_comb begin
        state_stream_next = state_stream;
        state_skid_next   = state_skid;
        pipe_next         = pipe;
        skid_next         = skid;

        if (clear)
          state_stream_next = 1'b0;
        else if (din_valid || dout_ready)
          state_stream_next = din_valid;

        if (OPT_AREA_TIMING != 0) begin
          if (!state_stream || dout_ready)
            pipe_next = din;
        end else begin
          if (din_valid && (!state_stream || dout_ready))
            pipe_next = din;
        end

        din_ready  = !state_stream || dout_ready;
        dout_valid = state_stream;
        dout       = pipe;
      end
    end else if ((FLOW == 0) && (SKID != 0)) begin : gen_skid_buffer
      always_comb begin
        state_stream_next = state_stream;
        state_skid_next   = state_skid;
        pipe_next         = pipe;
        skid_next         = skid;

        if (clear) begin
          state_stream_next = 1'b0;
          state_skid_next   = 1'b0;
        end else if (din_valid || dout_ready) begin
          state_stream_next = state_skid || din_valid;
          state_skid_next   = state_stream && !dout_ready;
        end

        if (OPT_AREA_TIMING != 0) begin
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

        din_ready  = !state_skid;
        dout_valid = state_stream;
        dout       = pipe;
      end
    end else if ((FLOW != 0) && (SKID == 0)) begin : gen_fallthrough_buffer
      always_comb begin
        state_stream_next = state_stream;
        state_skid_next   = state_skid;
        pipe_next         = pipe;
        skid_next         = skid;

        if (clear)
          state_stream_next = 1'b0;
        else if (din_valid ^ dout_ready)
          state_stream_next = din_valid;

        if (OPT_AREA_TIMING != 0) begin
          if (!state_stream || dout_ready)
            pipe_next = din;
        end else begin
          if (din_valid && (state_stream == dout_ready))
            pipe_next = din;
        end

        din_ready  = !state_stream || dout_ready;
        dout_valid = state_stream || din_valid;
        dout       = state_stream ? pipe : din;
      end
    end else begin : gen_reverse_pipeline
      always_comb begin
        state_stream_next = state_stream;
        state_skid_next   = state_skid;
        pipe_next         = pipe;
        skid_next         = skid;

        if (clear)
          state_skid_next = 1'b0;
        else if (din_valid || dout_ready)
          state_skid_next = !dout_ready;

        if (OPT_AREA_TIMING != 0) begin
          if (!state_skid)
            skid_next = din;
        end else begin
          if (!state_skid && din_valid && !dout_ready)
            skid_next = din;
        end

        din_ready  = !state_skid;
        dout_valid = state_skid || din_valid;
        dout       = state_skid ? skid : din;
      end
    end
  endgenerate

  always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      state_stream <= 1'b0;
      state_skid   <= 1'b0;
    end else begin
      state_stream <= state_stream_next;
      state_skid   <= state_skid_next;
    end
  end

  // Payload registers do not need reset because valid state controls whether
  // their contents are observable.
  always_ff @(posedge clk) begin
    pipe <= pipe_next;
    skid <= skid_next;
  end

//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifndef SYNTHESIS
  initial begin
    assert (WIDTH >= 1) else $fatal(1, "Buffer width must be at least 1.");
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

  clear_drops_output_valid: assert property ( @(posedge clk)
    clear |=> !dout_valid)
    else $fatal(1, "Buffer output valid was not cleared.");

`endif // STV_ASSERT_ON
// pragma translate_on

endmodule : stv_buffer
