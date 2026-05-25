module stv_buffer_formal #(
  parameter  int WIDTH           = 4,
  parameter  int FLOW            = 0,
  parameter  int SKID            = 0,
  parameter  int OPT_AREA_TIMING = 0,
  localparam int CAPACITY        = ((FLOW == 0) && (SKID != 0)) ? 2 : 1
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

  logic [WIDTH-1:0] model_0;
  logic [WIDTH-1:0] model_1;
  logic [1:0]       model_count;

  stv_buffer #(
    .WIDTH           (WIDTH          ),
    .FLOW            (FLOW           ),
    .SKID            (SKID           ),
    .OPT_AREA_TIMING (OPT_AREA_TIMING)
  ) dut (
    .clk        (clk        ),
    .arst_n     (arst_n     ),
    .clear      (clear      ),
    .din_valid  (din_valid  ),
    .din_ready  (din_ready  ),
    .din        (din        ),
    .dout_valid (dout_valid ),
    .dout_ready (dout_ready ),
    .dout       (dout       )
  );

  wire push = din_valid && din_ready;
  wire pop  = dout_valid && dout_ready;

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
      assert (model_count <= CAPACITY[1:0]);
      assert (!(push && !pop && (model_count == CAPACITY[1:0])));

      if (pop) begin
        if (model_count == 0) begin
          assert (push);
          assert (FLOW != 0);
          assert (dout == din);
        end else begin
          assert (dout == model_0);
        end
      end

      unique case ({push, pop})
        2'b00: begin
          model_count <= model_count;
        end
        2'b01: begin
          if (model_count > 0) begin
            model_0 <= model_1;
            model_count <= model_count - 1'b1;
          end
        end
        2'b10: begin
          if (model_count == 0) begin
            model_0 <= din;
          end else begin
            model_1 <= din;
          end
          model_count <= model_count + 1'b1;
        end
        2'b11: begin
          if (model_count == 0) begin
            model_count <= 0;
          end else if (model_count == 1) begin
            model_0 <= din;
            model_count <= 1;
          end else begin
            model_0 <= model_1;
            model_1 <= din;
            model_count <= 2;
          end
        end
      endcase
    end
  end

  always_comb begin
    assert (WIDTH >= 1);
    assert (FLOW == 0 || FLOW == 1);
    assert (SKID == 0 || SKID == 1);
    assert (OPT_AREA_TIMING == 0 || OPT_AREA_TIMING == 1);

    if (arst_n && !clear) begin
      assert (model_count <= CAPACITY[1:0]);

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
        assert (din_ready == (model_count < CAPACITY[1:0]));
      end

    end
  end

endmodule : stv_buffer_formal
