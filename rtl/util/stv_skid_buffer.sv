//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Skid buffer
//
// Uses ready/valid interfaces. Fully cuts all signals by pipeline registers.
//////////////////////////////////////////////////////////////////////////////

module stv_skid_buffer #(
  // data width
  parameter int WIDTH = 8
) (
  input  logic             clk,
  input  logic             arst_n,

  // initiator side
  input  logic             valid_in,
  output logic             ready_out,
  input  logic [WIDTH-1:0] data_in,

  // target side
  input  logic             ready_in,
  output logic             valid_out,
  output logic [WIDTH-1:0] data_out
);

  typedef enum logic[1:0] {
    IDLE   = 0,
    STREAM = 1,
    SKID   = 3
  } state_t;

  state_t state, state_next;
  logic [WIDTH-1:0] data_pipe, data_pipe_next;
  logic [WIDTH-1:0] data_skid, data_skid_next;

  always_comb begin
    data_out = data_pipe;
    case (state)
      IDLE: begin
        valid_out      = 0;
        ready_out      = 1;
        data_pipe_next = valid_in ? data_in : data_pipe;
        data_skid_next = data_skid;
        state_next     = valid_in ? STREAM : state;
      end
      STREAM: begin
        valid_out      = 1;
        ready_out      = 1;
        data_pipe_next = (valid_in &&  ready_in) ? data_in : data_pipe;
        data_skid_next = (valid_in && !ready_in) ? data_in : data_skid;
        state_next     = (valid_in && !ready_in) ? SKID : (!valid_in && ready_in) ? IDLE : state;
      end
      SKID: begin
        valid_out      = 1;
        ready_out      = 0;
        data_pipe_next = ready_in ? data_skid : data_pipe;
        data_skid_next = data_skid;
        state_next     = ready_in ? STREAM : state;
      end
      default: begin
        // impossible
      end
    endcase
  end

  always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      state <= IDLE;
    end else begin
      state <= state_next;
    end
  end

  always_ff @(posedge clk) begin
    data_pipe <= data_pipe_next;
    data_skid <= data_skid_next;
  end

endmodule : stv_skid_buffer
