module stv_sync_fifo_formal #(
  parameter  int WIDTH    = 4,
  parameter  int DEPTH    = 3,
  parameter  int FLOW     = 0,
  parameter  int SKID     = 0,
  localparam int CNTWIDTH = $clog2(DEPTH+1)
) ();

  (* gclk *) logic clk;
  (* anyseq *) logic arst_n;
  (* anyseq *) logic clear;

  (* anyseq *) logic din_valid;
  logic             din_ready;
  (* anyseq *) logic [WIDTH-1:0] din;

  logic             dout_valid;
  (* anyseq *) logic dout_ready;
  logic [WIDTH-1:0] dout;

  logic                empty;
  logic                full;
  logic [CNTWIDTH-1:0] count;

  logic [WIDTH-1:0]    model [DEPTH];
  logic [CNTWIDTH-1:0] model_count;

  stv_sync_fifo #(
    .WIDTH (WIDTH),
    .DEPTH (DEPTH),
    .FLOW  (FLOW ),
    .SKID  (SKID )
  ) dut (
    .clk        (clk        ),
    .arst_n     (arst_n     ),
    .clear      (clear      ),
    .din_valid  (din_valid  ),
    .din_ready  (din_ready  ),
    .din        (din        ),
    .dout_valid (dout_valid ),
    .dout_ready (dout_ready ),
    .dout       (dout       ),
    .empty      (empty      ),
    .full       (full       ),
    .count      (count      )
  );

  wire push             = din_valid && din_ready;
  wire pop              = dout_valid && dout_ready;
  wire pop_stored       = pop && (model_count != 0);
  wire pop_fallthrough  = pop && (model_count == 0);
  wire push_stored      = push && !pop_fallthrough;
  wire [CNTWIDTH-1:0] append_index =
    model_count - (pop_stored ? CNTWIDTH'(1) : CNTWIDTH'(0));

  initial begin
    assume (!arst_n);
    model_count = 0;
  end

  always_ff @(posedge clk) begin
    if ($initstate) begin
      assume (!arst_n);
    end else begin
      assume (arst_n);
    end

    if (arst_n && $past(arst_n) && $past(din_valid && !din_ready && !clear)) begin
      assume (din_valid);
      assume (din == $past(din));
    end

    if (!arst_n || clear) begin
      model_count <= 0;
    end else begin
      assert (model_count <= CNTWIDTH'(DEPTH));
      assert (!(push_stored && !pop_stored && (model_count == CNTWIDTH'(DEPTH))));

      if (pop) begin
        if (model_count == 0) begin
          assert (push);
          assert (FLOW != 0);
          assert (dout == din);
        end else begin
          assert (dout == model[0]);
        end
      end

      for (int index = 0; index < DEPTH-1; index++) begin
        if (pop_stored) begin
          model[index] <= model[index+1];
        end
      end

      for (int index = 0; index < DEPTH; index++) begin
        if (push_stored && (append_index == CNTWIDTH'(index))) begin
          model[index] <= din;
        end
      end

      model_count <= model_count
                     - (pop_stored  ? CNTWIDTH'(1) : CNTWIDTH'(0))
                     + (push_stored ? CNTWIDTH'(1) : CNTWIDTH'(0));
    end
  end

  always_comb begin
    assert (WIDTH >= 1);
    assert (DEPTH > 1);
    assert (FLOW == 0 || FLOW == 1);
    assert (SKID == 0 || SKID == 1);

    if (arst_n && !clear) begin
      assert (model_count <= CNTWIDTH'(DEPTH));
      assert (count == model_count);
      assert (empty == (model_count == 0));
      assert (full == (model_count == CNTWIDTH'(DEPTH)));

      if (FLOW == 0) begin
        if (model_count == 0) begin
          assert (!dout_valid);
        end
      end else begin
        if (model_count == 0) begin
          assert (dout_valid == din_valid);
          if (din_valid) begin
            assert (dout == din);
          end
        end
      end

      if (SKID != 0) begin
        assert (din_ready == (model_count < CNTWIDTH'(DEPTH)));
      end else begin
        assert (din_ready == ((model_count < CNTWIDTH'(DEPTH)) || dout_ready));
      end
    end
  end

endmodule : stv_sync_fifo_formal
