module Cxu0 (
  input               cmd_valid,
  output              cmd_ready,
  input      [2:0]    cmd_payload_function_id,
  input      [31:0]   cmd_payload_inputs_0,
  input      [31:0]   cmd_payload_inputs_1,
  input      [2:0]    cmd_payload_state_id,
  input      [3:0]    cmd_payload_cxu_id,
  input               cmd_payload_ready,
  output              rsp_valid,
  input               rsp_ready,
  output reg [31:0]   rsp_payload_outputs_0,
  output              rsp_payload_ready,
  input      [2047:0] state_read,
  output     [2047:0] state_write,
  output              state_write_en,
  input               clk,
  input               reset
);

  assign rsp_valid        = cmd_valid;
  assign cmd_ready        = rsp_ready;
  assign rsp_payload_ready = 1'b1;
  assign state_write_en   = 1'b0;
  assign state_write      = 2048'b0;

  wire [31:0] b  = cmd_payload_inputs_0;
  wire [31:0] kn = cmd_payload_inputs_1;

  wire [31:0] bitrev_result;
  genvar gi;
  generate
    for (gi = 0; gi < 32; gi = gi + 1)
      assign bitrev_result[gi] = b[31 - gi];
  endgenerate

  wire [4:0] clz_result;
  assign clz_result =
    b[31] ? 5'd0  : b[30] ? 5'd1  : b[29] ? 5'd2  : b[28] ? 5'd3  :
    b[27] ? 5'd4  : b[26] ? 5'd5  : b[25] ? 5'd6  : b[24] ? 5'd7  :
    b[23] ? 5'd8  : b[22] ? 5'd9  : b[21] ? 5'd10 : b[20] ? 5'd11 :
    b[19] ? 5'd12 : b[18] ? 5'd13 : b[17] ? 5'd14 : b[16] ? 5'd15 :
    b[15] ? 5'd16 : b[14] ? 5'd17 : b[13] ? 5'd18 : b[12] ? 5'd19 :
    b[11] ? 5'd20 : b[10] ? 5'd21 : b[9]  ? 5'd22 : b[8]  ? 5'd23 :
    b[7]  ? 5'd24 : b[6]  ? 5'd25 : b[5]  ? 5'd26 : b[4]  ? 5'd27 :
    b[3]  ? 5'd28 : b[2]  ? 5'd29 : b[1]  ? 5'd30 : 5'd31;

  wire [4:0]  mask_n      = kn[4:0];
  wire [31:0] mask_result = (32'd1 << mask_n) - 32'd1;

  wire [31:0] huft_mask   = (32'd1 << kn[4:0]) - 32'd1;
  wire [31:0] huft_index  = b & huft_mask;

  wire [15:0] w_pos    = b[31:16];
  wire [15:0] dist_base= b[15:0];
  wire [15:0] copy_d   = (w_pos - dist_base - kn[15:0]) & 16'hFFFF;
  wire [31:0] copy_result = {w_pos, copy_d & 16'h7FFF};

  always @(*) begin
    case (cmd_payload_function_id)
      3'b000:  rsp_payload_outputs_0 = bitrev_result;
      3'b001:  rsp_payload_outputs_0 = {27'b0, clz_result};
      3'b010:  rsp_payload_outputs_0 = mask_result;
      3'b011:  rsp_payload_outputs_0 = huft_index;
      3'b100:  rsp_payload_outputs_0 = copy_result;
      default: rsp_payload_outputs_0 = 32'b0;
    endcase
  end

endmodule
