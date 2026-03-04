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

  localparam MAX_IN  = 4096;
  localparam MAX_OUT = 16384;

  localparam FN_PUT_BYTE    = 3'd0;
  localparam FN_UNZIP       = 3'd1;
  localparam FN_GET_LEN_IN  = 3'd2;
  localparam FN_CLEAR       = 3'd3;
  localparam FN_GET_LEN_OUT = 3'd4;
  localparam FN_GET_BYTE    = 3'd5;

  reg [7:0] in_buf  [0:MAX_IN-1];
  reg [7:0] out_buf [0:MAX_OUT-1];

  reg [12:0] in_len;
  reg [14:0] out_len;

  reg [31:0] bit_pos;
  reg [31:0] bit_buf;
  reg [4:0]  bit_avail;

  localparam S_IDLE         = 5'd0;
  localparam S_ACCEPT       = 5'd1;
  localparam S_CLEAR        = 5'd2;
  localparam S_RESPOND      = 5'd3;

  localparam S_BLOCK_HDR    = 5'd4;
  localparam S_STORED_LEN   = 5'd5;
  localparam S_STORED_COPY  = 5'd6;
  localparam S_FIXED_LIT    = 5'd7;
  localparam S_FIXED_DIST   = 5'd8;
  localparam S_FIXED_EXTRA_LEN  = 5'd9;
  localparam S_FIXED_EXTRA_DIST = 5'd10;
  localparam S_COPY_MATCH   = 5'd11;
  localparam S_ERROR        = 5'd12;
  localparam S_DONE         = 5'd13;

  reg [4:0] state;
  reg [4:0] next_state_after_respond;

  reg        bfinal;
  reg [1:0]  btype;
  reg        last_block;

  reg [31:0] tmp32;
  reg [15:0] stored_len;
  reg [15:0] stored_nlen;
  reg [15:0] stored_cnt;

  reg [8:0]  lit_val;
  reg [31:0] match_len;
  reg [31:0] match_dist;
  reg [31:0] copy_cnt;
  reg [31:0] copy_src;
  reg [31:0] error_code;

  reg        busy;
  reg        rsp_valid_r;
  reg [31:0] rsp_data;

  assign cmd_ready         = ~busy;
  assign rsp_valid         = rsp_valid_r;
  assign rsp_payload_ready = 1'b1;
  assign state_write       = 2048'd0;
  assign state_write_en    = 1'b0;

  function [31:0] peek_bits;
    input [4:0] n;
    input [31:0] bp;
    reg [31:0] val;
    reg [31:0] bi;
    reg [2:0]  bo;
    integer i;
    begin
      val = 0;
      for (i = 0; i < 32; i = i + 1) begin
        if (i < n) begin
          bi = (bp + i) >> 3;
          bo = (bp + i) & 3'h7;
          if (bi < MAX_IN)
            val = val | (((in_buf[bi] >> bo) & 1) << i);
        end
      end
      peek_bits = val;
    end
  endfunction


  task get_length_info;
    input  [8:0] sym;
    output [31:0] base;
    output [3:0]  extra;
    begin
      case (sym)
        257: begin base=3;   extra=0; end
        258: begin base=4;   extra=0; end
        259: begin base=5;   extra=0; end
        260: begin base=6;   extra=0; end
        261: begin base=7;   extra=0; end
        262: begin base=8;   extra=0; end
        263: begin base=9;   extra=0; end
        264: begin base=10;  extra=0; end
        265: begin base=11;  extra=1; end
        266: begin base=13;  extra=1; end
        267: begin base=15;  extra=1; end
        268: begin base=17;  extra=1; end
        269: begin base=19;  extra=2; end
        270: begin base=23;  extra=2; end
        271: begin base=27;  extra=2; end
        272: begin base=31;  extra=2; end
        273: begin base=35;  extra=3; end
        274: begin base=43;  extra=3; end
        275: begin base=51;  extra=3; end
        276: begin base=59;  extra=3; end
        277: begin base=67;  extra=4; end
        278: begin base=83;  extra=4; end
        279: begin base=99;  extra=4; end
        280: begin base=115; extra=4; end
        281: begin base=131; extra=5; end
        282: begin base=163; extra=5; end
        283: begin base=195; extra=5; end
        284: begin base=227; extra=5; end
        285: begin base=258; extra=0; end
        default: begin base=0; extra=0; end
      endcase
    end
  endtask

  task get_dist_info;
    input  [4:0] code;
    output [31:0] base;
    output [3:0]  extra;
    begin
      case (code)
        0:  begin base=1;     extra=0;  end
        1:  begin base=2;     extra=0;  end
        2:  begin base=3;     extra=0;  end
        3:  begin base=4;     extra=0;  end
        4:  begin base=5;     extra=1;  end
        5:  begin base=7;     extra=1;  end
        6:  begin base=9;     extra=2;  end
        7:  begin base=13;    extra=2;  end
        8:  begin base=17;    extra=3;  end
        9:  begin base=25;    extra=3;  end
        10: begin base=33;    extra=4;  end
        11: begin base=49;    extra=4;  end
        12: begin base=65;    extra=5;  end
        13: begin base=97;    extra=5;  end
        14: begin base=129;   extra=6;  end
        15: begin base=193;   extra=6;  end
        16: begin base=257;   extra=7;  end
        17: begin base=385;   extra=7;  end
        18: begin base=513;   extra=8;  end
        19: begin base=769;   extra=8;  end
        20: begin base=1025;  extra=9;  end
        21: begin base=1537;  extra=9;  end
        22: begin base=2049;  extra=10; end
        23: begin base=3073;  extra=10; end
        24: begin base=4097;  extra=11; end
        25: begin base=6145;  extra=11; end
        26: begin base=8193;  extra=12; end
        27: begin base=12289; extra=12; end
        28: begin base=16385; extra=13; end
        29: begin base=24577; extra=13; end
        default: begin base=0; extra=0; end
      endcase
    end
  endfunction

  task decode_fixed_lit;
    input  [31:0] bp;
    output [8:0]  sym;
    output [3:0]  bits_used;
    reg [8:0] code7, code8, code9;
    begin
      code7 = {1'b0, peek_bits(7, bp)};
      code7 = {code7[0],code7[1],code7[2],code7[3],code7[4],code7[5],code7[6],code7[7],code7[8]};
      code7 = code7 >> 2;

      begin
        reg [6:0] b7;
        reg [7:0] b8;
        reg [8:0] b9;
        reg [6:0] rb7;
        reg [7:0] rb8;
        reg [8:0] rb9;
        integer k;

        b7 = peek_bits(7, bp);
        rb7 = {b7[0],b7[1],b7[2],b7[3],b7[4],b7[5],b7[6]};

        b8 = peek_bits(8, bp);
        rb8 = {b8[0],b8[1],b8[2],b8[3],b8[4],b8[5],b8[6],b8[7]};

        b9 = peek_bits(9, bp);
        rb9 = {b9[0],b9[1],b9[2],b9[3],b9[4],b9[5],b9[6],b9[7],b9[8]};

        if (rb7 <= 7'h17) begin
          sym = rb7 + 9'd256;
          bits_used = 7;
        end else if (rb8 <= 8'hBF && rb8 >= 8'h30) begin
          sym = rb8 - 8'h30;
          bits_used = 8;
        end else if (rb8 <= 8'hC7 && rb8 >= 8'hC0) begin
          sym = rb8 - 8'hC0 + 9'd280;
          bits_used = 8;
        end else if (rb9 >= 9'h190 && rb9 <= 9'h1FF) begin
          sym = rb9 - 9'h190 + 9'd144;
          bits_used = 9;
        end else begin
          sym = 9'h1FF;
          bits_used = 7;
        end
      end
    end
  endtask

  task decode_fixed_dist;
    input  [31:0] bp;
    output [4:0]  code;
    begin
      reg [4:0] b5;
      b5 = peek_bits(5, bp);
      code = {b5[0],b5[1],b5[2],b5[3],b5[4]};
    end
  endtask

  integer ii;

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      state       <= S_IDLE;
      busy        <= 0;
      rsp_valid_r <= 0;
      in_len      <= 0;
      out_len     <= 0;
      bit_pos     <= 0;
      last_block  <= 0;
      error_code  <= 0;
    end else begin
      case (state)

        S_IDLE: begin
          rsp_valid_r <= 0;
          if (cmd_valid) begin
            case (cmd_payload_function_id)

              FN_PUT_BYTE: begin
                if (in_len < MAX_IN) begin
                  in_buf[in_len] <= cmd_payload_inputs_0[7:0];
                  in_len <= in_len + 1;
                end
                rsp_data    <= in_len;
                state       <= S_RESPOND;
              end

              FN_UNZIP: begin
                out_len    <= 0;
                bit_pos    <= 0;
                last_block <= 0;
                busy       <= 1;
                state      <= S_BLOCK_HDR;
              end

              FN_GET_LEN_IN: begin
                rsp_data <= {19'd0, in_len};
                state    <= S_RESPOND;
              end

              FN_CLEAR: begin
                state <= S_CLEAR;
                busy  <= 1;
              end

              FN_GET_LEN_OUT: begin
                rsp_data <= {17'd0, out_len};
                state    <= S_RESPOND;
              end

              FN_GET_BYTE: begin
                if (cmd_payload_inputs_0 < out_len)
                  rsp_data <= {24'd0, out_buf[cmd_payload_inputs_0[13:0]]};
                else
                  rsp_data <= 32'hFFFFFFFF;
                state <= S_RESPOND;
              end

              default: begin
                rsp_data <= 32'hDEAD0000;
                state    <= S_RESPOND;
              end

            endcase
          end
        end

        S_CLEAR: begin
          in_len  <= 0;
          out_len <= 0;
          bit_pos <= 0;
          busy    <= 0;
          rsp_data <= 0;
          state   <= S_RESPOND;
        end

        S_RESPOND: begin
          rsp_payload_outputs_0 <= rsp_data;
          rsp_valid_r           <= 1;
          busy                  <= 0;
          if (rsp_ready) begin
            rsp_valid_r <= 0;
            state       <= S_IDLE;
          end
        end

        S_BLOCK_HDR: begin
          if (last_block) begin
            error_code <= 0;
            rsp_data   <= 0;
            busy       <= 0;
            state      <= S_RESPOND;
          end else begin
            bfinal  <= peek_bits(1, bit_pos);
            btype   <= peek_bits(2, bit_pos + 1) & 2'h3;
            begin
              reg [2:0] hdr;
              hdr    = peek_bits(3, bit_pos);
              bfinal <= hdr[0];
              btype  <= hdr[2:1];
              bit_pos <= bit_pos + 3;
            end

            case (btype)
              2'b00: begin
                bit_pos <= ((bit_pos + 7) >> 3) << 3;
                state   <= S_STORED_LEN;
              end
              2'b01: state <= S_FIXED_LIT;
              2'b10: begin
                error_code <= 32'hE0000002;
                rsp_data   <= 32'hE0000002;
                busy       <= 0;
                state      <= S_RESPOND;
              end
              2'b11: begin
                error_code <= 32'hE0000003;
                rsp_data   <= 32'hE0000003;
                busy       <= 0;
                state      <= S_RESPOND;
              end
            endcase

            if (hdr[0]) last_block <= 1;
          end
        end

        S_STORED_LEN: begin
          begin
            reg [7:0] b0, b1, b2, b3;
            reg [31:0] byte_pos;
            byte_pos  = bit_pos >> 3;
            b0 = in_buf[byte_pos];
            b1 = in_buf[byte_pos+1];
            b2 = in_buf[byte_pos+2];
            b3 = in_buf[byte_pos+3];
            stored_len  <= {b1, b0};
            stored_nlen <= {b3, b2};
            bit_pos     <= bit_pos + 32;
            stored_cnt  <= 0;
            state       <= S_STORED_COPY;
          end
        end

        S_STORED_COPY: begin
          if (stored_cnt < stored_len) begin
            begin
              reg [31:0] byte_pos;
              byte_pos = (bit_pos >> 3) + stored_cnt;
              if (out_len < MAX_OUT) begin
                out_buf[out_len] <= in_buf[byte_pos[12:0]];
                out_len <= out_len + 1;
              end
            end
            stored_cnt <= stored_cnt + 1;
          end else begin
            bit_pos <= bit_pos + {stored_len, 3'b000};
            if (last_block) begin
              error_code <= 0;
              rsp_data   <= 0;
              busy       <= 0;
              state      <= S_RESPOND;
            end else
              state <= S_BLOCK_HDR;
          end
        end

        S_FIXED_LIT: begin
          begin
            reg [8:0]  sym;
            reg [3:0]  bits_used;
            reg [31:0] base_len;
            reg [3:0]  extra_bits;

            decode_fixed_lit(bit_pos, sym, bits_used);
            bit_pos <= bit_pos + bits_used;
            lit_val <= sym;

            if (sym < 256) begin
              if (out_len < MAX_OUT) begin
                out_buf[out_len] <= sym[7:0];
                out_len <= out_len + 1;
              end
            end else if (sym == 256) begin
              if (last_block) begin
                error_code <= 0;
                rsp_data   <= 0;
                busy       <= 0;
                state      <= S_RESPOND;
              end else
                state <= S_BLOCK_HDR;
            end else if (sym <= 285) begin
              get_length_info(sym, base_len, extra_bits);
              match_len <= base_len + peek_bits(extra_bits, bit_pos + bits_used);
              match_len <= base_len + peek_bits(extra_bits, bit_pos);
              bit_pos   <= bit_pos + extra_bits;
              state     <= S_FIXED_DIST;
            end else begin
              error_code <= 32'hE0000004;
              rsp_data   <= 32'hE0000004;
              busy       <= 0;
              state      <= S_RESPOND;
            end
          end
        end

        S_FIXED_DIST: begin
          begin
            reg [4:0]  dist_code;
            reg [31:0] base_dist;
            reg [3:0]  extra_bits;

            decode_fixed_dist(bit_pos, dist_code);
            bit_pos <= bit_pos + 5;
            get_dist_info(dist_code, base_dist, extra_bits);
            match_dist <= base_dist + peek_bits(extra_bits, bit_pos + 5);
            bit_pos    <= bit_pos + 5 + extra_bits;
            copy_cnt   <= 0;
            state      <= S_COPY_MATCH;
          end
        end

        S_COPY_MATCH: begin
          if (copy_cnt < match_len) begin
            begin
              reg [31:0] src;
              src = out_len - match_dist + copy_cnt;
              if (out_len < MAX_OUT) begin
                out_buf[out_len] <= out_buf[src[13:0]];
                out_len <= out_len + 1;
              end
            end
            copy_cnt <= copy_cnt + 1;
          end else
            state <= S_FIXED_LIT;
        end

        default: state <= S_IDLE;

      endcase
    end
  end

  always @(posedge clk) begin
    if (state == S_RESPOND)
      rsp_payload_outputs_0 <= rsp_data;
  end

endmodule
