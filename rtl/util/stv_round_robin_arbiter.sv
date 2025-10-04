//////////////////////////////////////////////////////////////////////////////
//
// author: Stevo Bailey (stevo.bailey@gmail.com)
//
// Round-Robin Arbiter
//
// The lock input will keep the chosen request granted until released. This
// assumes the chosen req stays high until the lock is released.
//////////////////////////////////////////////////////////////////////////////

module stv_round_robin_arbiter #(
  // number of inputs
  parameter int INPUTS = 8
) (
  input  logic              clk,
  input  logic              arst_n,

  input  logic [INPUTS-1:0] req,
  input  logic              lock,
  output logic [INPUTS-1:0] gnt
);

  // Store previous grant or lock
  logic [INPUTS-1:0] mask, mask_next;
  // Use unpacked array and for loops to avoid verilator complaints
  logic              priority_mask [INPUTS];
  logic [INPUTS-1:0] masked_req;
  logic              no_req_above;
  logic [INPUTS-1:0] selected_req;

  always_comb begin
    // Mask requests above the current position
    masked_req = req & ~mask;
    no_req_above = masked_req == 0;

    // If no requests above current position, look at all requests
    selected_req = no_req_above ? req : masked_req;
    
    priority_mask[0] = 1'b0;
    for (int i = 1; i < INPUTS; i++)
      priority_mask[i] = priority_mask[i-1] | selected_req[i-1];
    
    for (int i = 0; i < INPUTS; i++)
      gnt[i] = selected_req[i] & ~priority_mask[i];

    // Update mask register
    mask_next = mask;
    if (|req) begin
      if (lock) begin
        // Force current choice as highest priority
        for (int i = 0; i < INPUTS; i++)
          mask_next[i] = ~selected_req[i] & ~priority_mask[i];
      end else begin
        // Force current choice as lowest priority
        for (int i = 0; i < INPUTS; i++)
          mask_next[i] = ~priority_mask[i];
      end
    end
  end

  always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      mask <= '0;
    end else begin
      mask <= mask_next;
    end
  end

//////////////////////////////////////////////////////////////////////////////
// Assertions
//////////////////////////////////////////////////////////////////////////////

// pragma translate_off
`ifdef STV_ASSERT_ON

  initial begin
    assert (INPUTS > 0) else $fatal(1, "Round-robin arbiter needs at least 1 input.");
  end

  default disable iff (!arst_n);

  // Check that grant is one-hot when REQ_MASK is true
  onehot_gnt: assert property ( @(posedge clk)
    $onehot0(gnt)
    else $fatal(1, "Grant is not one-hot");

  // Check that granted request is actually requested when REQ_MASK is true
  gnt_implies_req: assert property ( @(posedge clk)
    (gnt & ~req) == 0
    else $fatal(1, "Granted request was not requested");

  // Check lock behavior
  lock_stable: assert property ( @(posedge clk)
    lock && (gnt != 0) |=> $stable(gnt);
    else $fatal(1, "Lock error");

`endif // STV_ASSERT_ON
// pragma translate_on

endmodule : stv_round_robin_arbiter
