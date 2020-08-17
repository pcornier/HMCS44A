/* verilator lint_off CASEINCOMPLETE */

module HMCS44A(
  input clk, // 400kHz
  input reset,

  input [15:0] i_D,
  output reg [15:0] o_D,

  input [3:0] i_R0,
  input [3:0] i_R1,
  input [3:0] i_R2,
  input [3:0] i_R3,

  output [3:0] o_R0,
  output [3:0] o_R1,
  output [3:0] o_R2,
  output [3:0] o_R3,

  input i_int0,
  input i_int1
);

reg [3:0] R[7:0];

assign o_R0 = R[0];
assign o_R1 = R[1];
assign o_R2 = R[2];
assign o_R3 = R[3];

reg [9:0] ROM[4095:0];
reg [3:0] RAM[159:0];

reg [4:0] PC_page;
reg [5:0] PC_addr;
reg [10:0] ST[3:0]; // stack
reg [3:0] A, B, X, Y, SPX, SPY;
reg alu_c, carry, status;
reg [9:0] op;
reg [3:0] RAM_din;
reg [3:0] RAM_dout;
reg RAM_we;
reg [7:0] RAM_addr;
reg [3:0] mask;
reg [1:0] alu_op;
reg [3:0] alu_a, alu_b, alu_out;
reg [3:0] counter;
reg [5:0] prescaler;
reg po; // prescaler, overflow output pulse
reg CF; // 0 = timer mode, 1 = counter mode (i_int1)
reg TF; // timer/counter interrupt mask
reg IF0, IF1; // input interrupt masks
reg IE; // interrupt enable
reg IR; // interrupt request

wire [10:0] PC = { PC_page, PC_addr };
wire [3:0] imm = { op[0], op[1], op[2], op[3] };
wire [2:0] p3 = op[2:0];

reg [1:0] clk_div;
wire clk_mcu = clk_div[1]; // 100
always @(posedge clk)
  clk_div <= clk_div + 2'b1;

// PAT
reg PAT;
always @*
  PAT = (op[9:3] == 7'b1101101) ? 1'b1 : 1'b0;

reg odf; // op data flag
always @(posedge clk_mcu)
  odf <= PAT;

// D out
always @(posedge clk_mcu)
  casez (op)
    10'b10_1001_0000: o_D[Y] <= 1'b0; // red
    10'b00_1001_0000: o_D[Y] <= 1'b1; // sed
    10'b00_1101_00??: o_D[3:0] <= o_D[3:0] | mask; // sedd D[3:0] only
    10'b10_1101_00??: o_D[3:0] <= o_D[3:0] & ~mask; // redd
  endcase

// alu
// 00: add 01: sub
// 10: sbc 11: adc
always @*
  case (alu_op)
    2'b00: { alu_c, alu_out } = alu_a + alu_b;
    2'b01: { alu_c, alu_out } = alu_a - alu_b;
    2'b10: { alu_c, alu_out } = alu_a - alu_b - { 3'd0, carry };
    2'b11: { alu_c, alu_out } = alu_a + alu_b + { 3'd0, carry };
    default: { alu_c, alu_out } = alu_a + alu_b;
  endcase

// status
always @*
  if (reset)
    status = 1'b1;
  else if (~odf)
    casez (op)
      10'b11_11??_????, // cal
      10'b01_11??_????: status = 1'b1; // br
      10'b00_1001_0100: status = i_D[Y]; // td
      10'b10_0011_0100, // alem
      10'b00_0010_0100, // blem
      10'b10_0111_????: status = ~alu_c; // alei
      10'b10_0101_1000, // syy
      10'b10_0011_0000, // smc
      10'b00_0011_0100, // am
      10'b00_1000_????: status = alu_c; // ai
      10'b01_0001_000?, // lmaiy
      10'b00_0110_0100, // ib
      10'b00_0101_0100, // iy
      10'b10_0101_0100, // dy
      10'b10_0110_0111, // db
      10'b00_0001_????: status = ~alu_c; // lmiiy
      10'b10_0000_00??: status = (buffer & mask) != 0 ? 1'b1 : 1'b0; // tm
      10'b01_1010_0000: status = IF1; // tif1
      10'b01_1010_0001: status = i_int1; // ti1
      10'b01_1010_0010: status = IF0; // tif0
      10'b01_1010_0011: status = i_int0; // ti0
      10'b01_1010_0101: status = TF; // ttf
      10'b11_0010_0100, // bnem
      10'b10_0001_????, // mnei
      10'b10_1000_????, // ynei
      10'b01_0010_0100: status = alu_out != 0 ? 1'b1 : 1'b0; // anem
      10'b10_0100_1111: status = carry; // tc
      default: status = status;
    endcase

// carry
always @(posedge clk_mcu)
  casez (op)
    10'b00_0100_1100: carry <= 1'b0; // rec
    10'b10_0011_0000, // smc
    10'b00_0011_0000: carry <= alu_c; // amc
    10'b00_0100_0101: if (A >= 9) carry <= 0; // das todo: use alu
    10'b00_0100_0110: if (A >= 9) carry <= 1; // daa todo: use alu
    10'b00_0100_1111:  carry <= 1'b1; // sec
    10'b10_0010_0100: carry <= A[0]; // rotr
    10'b10_0010_0101: carry <= A[3]; // rotl
  endcase

// alu_a
always @(posedge clk)
  casez (op)
    10'b11_0010_0100, // bnem
    10'b10_0110_0111, // db
    10'b00_0110_0100: alu_a <= B; // ib
    10'b10_0101_1000, // syy
    10'b01_0001_010?, // lmady
    10'b01_0001_000?, // lmaiy
    10'b10_1000_????, // ynei
    10'b10_0101_0100, // dy
    10'b00_0101_1000, // ayy
    10'b00_0101_0100, // iy
    10'b00_0001_????: alu_a <= Y; // lmiiy
    10'b01_0010_0100, // anem
    10'b00_1000_????, // ai
    10'b00_0011_0100, // am
    10'b00_0011_0000: alu_a <= A; // amc
    10'b10_0011_0100, // alem
    10'b10_0001_????, // mnei
    10'b10_0011_0000, // smc
    10'b00_0010_0100: alu_a <= buffer; // blem
    10'b10_0100_0100: alu_a <= ~A; // nega
    10'b10_0111_????: alu_a <= imm; // alei
  endcase

// alu_b
always @(posedge clk)
  casez (op)
    10'b11_0010_0100, // bnem
    10'b01_0010_0100, // anem
    10'b00_0011_0100, // am
    10'b00_0011_0000: alu_b <= buffer; // amc
    10'b01_0001_010?, // lmady
    10'b01_0001_000?, // lmaiy
    10'b00_0110_0100, // ib
    10'b10_0101_0100, // dy
    10'b10_0100_0100, // nega
    10'b10_0110_0111, // db
    10'b00_0101_0100, // iy
    10'b00_0001_????: alu_b <= 4'b1; // lmiiy
    10'b10_0111_????, // alei
    10'b10_0011_0100, // alem
    10'b10_0101_1000, // syy
    10'b10_0011_0000, // smc
    10'b00_0101_1000: alu_b <= A; // ayy
    10'b10_0001_????, // mnei
    10'b10_1000_????, // ynei
    10'b00_1000_????: alu_b <= imm; // ai
    10'b00_0010_0100: alu_b <= B; // blem
  endcase

// alu_op
always @(posedge clk)
  casez (op)
    10'b10_0011_0100, // alem
    10'b11_0010_0100, // bnem
    10'b10_0101_1000, // syy
    10'b10_0001_????, // mnei
    10'b01_0001_010?, // lmady
    10'b10_0101_0100, // dy
    10'b10_1000_????, // ynei
    10'b10_0111_????, // alei
    10'b00_0010_0100, // blem
    10'b01_0010_0100, // anem
    10'b10_0110_0111: alu_op <= 2'b01; // db
    10'b00_0011_0000: alu_op <= 2'b11; // amc
    10'b10_0011_0000: alu_op <= 2'b10; // smc
    default: alu_op <= 2'b00;
  endcase

wire [11:0] mpc = { op[2], { op[1:0], carry, B[3:2] } | PC_page, { B[1:0], A } };
wire [11:0] ROM_addr = op[9:3] == 7'b1101101 ? mpc : { 1'b0, PC };

// op
always @(posedge clk)
  nxtop <= ROM[ROM_addr];

// next op
reg [9:0] nxtop;
always @(posedge clk_mcu)
  op <= nxtop;

// RAM_dout
always @(posedge clk)
  RAM_dout <= RAM[RAM_addr];

// RAM buffer
reg [3:0] buffer;
always @(negedge clk_mcu)
  buffer <= RAM_dout;

// RAM
always @(posedge clk)
  if (~RAM_we) RAM[RAM_addr] <= RAM_din;

// RAM_din
always @(posedge clk)
  casez (op)
    10'b10_0000_01??: RAM_din <= buffer & ~mask; // rem
    10'b00_0000_01??: RAM_din <= buffer | mask; // sem
    10'b00_0001_????: RAM_din <= imm; // lmiiy
    10'b10_0000_10??, // xma
    10'b01_0001_010?, // lmady
    10'b01_0001_000?, // lmaiy
    10'b00_1111_????: RAM_din <= A; // xamr
    10'b10_0010_00??: RAM_din <= B; // xmb
  endcase

// RAM_addr
always @*
  casez (op)
    10'b00_1111_????: RAM_addr = { 4'd9, op[3:0] }; // xamr
    default: RAM_addr = X[3] ? { X[3], 2'b00, X[2], Y } : { X, Y };
  endcase

// RAM_we
always @*
  if (~odf)
    casez (op)
      10'b10_0010_00??, // xmb
      10'b10_0000_10??, // xma
      10'b01_0001_010?, // lmady
      10'b01_0001_000?, // lmaiy
      10'b10_0000_01??, // rem
      10'b00_1111_????, // xamr
      10'b00_0001_????, // lmiiy
      10'b00_0000_01??: RAM_we = 1'b0; // sem
      default: RAM_we = 1'b1;
    endcase

// A
always @(posedge clk_mcu)
  if (~odf)
    casez (op)
      10'b00_0111_????: A <= imm; // lai
      10'b00_0011_0100, // am
      10'b10_0011_0000, // smc
      10'b10_0100_0100, // nega
      10'b00_1000_????, // ai
      10'b00_0011_0000: A <= alu_out; // amc
      10'b00_0100_0101: if (~carry || A >= 9) A <= A + 4'd10; // das
      10'b00_0100_0110: if (~carry || A >= 9) A <= A + 4'd6; // daa
      10'b00_1100_0???: A <= R[p3]; // lar
      10'b10_0011_1100: A <= counter; // lat
      10'b01_0010_0000: A <= A | B; // or
      10'b10_0110_0000: A <= B; // lab
      10'b10_0000_10??, // xma
      10'b00_0000_10??, // lam
      10'b00_1111_????: A <= buffer; // xamr
      10'b10_0101_0000: A <= SPY; // laspy
      10'b10_0100_0000: A <= SPX; // laspx
      10'b01_0001_1000: A <= Y; // lay
      10'b10_0010_0100: A <= { carry, A[3:1] }; // rotr
      10'b10_0010_0101: A <= { A[2:0], carry }; // rotl
    endcase
  else
    if (op[8]) A <= { op[0], op[1], op[2], op[3] };

// B
always @(posedge clk_mcu)
  if (~odf)
    casez (op)
      10'b00_0110_0000: B <= A; // lba
      10'b10_0010_00??, // xmb
      10'b00_0010_00??: B <= buffer; // lbm
      10'b10_0110_0111, // db
      10'b00_0110_0100: B <= alu_out; // ib
      10'b00_1110_0???: B <= R[p3]; // lbr
      10'b01_0110_????: B <= imm; // lbi
      10'b11_0010_0000: B <= ~B; // comb
    endcase
  else
    if (op[8]) B <= op[7:4];

// X
always @(posedge clk_mcu)
  if (~odf)
    casez (op)
      10'b01_0001_0101, // lmady
      10'b01_0001_0001, // lmaiy
      10'b10_0010_00?1, // xmb
      10'b10_0000_10?1, // xma
      10'b00_0010_00?1, // lbm
      10'b00_0000_10?1, // lam
      10'b00_0000_00?1: X <= SPX; // xsp
      10'b00_0100_0000: X <= A; // lxa
      10'b01_0100_????: X <= imm; // lxi
    endcase

// Y
always @(posedge clk_mcu)
  if (~odf)
    casez (op)
      10'b10_0010_001?, // xmb
      10'b10_0000_101?, // xma
      10'b00_0010_001?, // lbm
      10'b00_0000_101?, // lam
      10'b00_0000_001?: Y <= SPY; // xsp
      10'b10_0101_1000, // syy
      10'b01_0001_010?, // lmady
      10'b01_0001_000?, // lmaiy
      10'b00_0101_0100, // iy
      10'b10_0101_0100, // dy
      10'b00_0101_1000, // ayy
      10'b00_0001_????: Y <= alu_out; // lmiiy
      10'b00_0101_0000: Y <= A; // lya
      10'b01_0101_????: Y <= imm; // lyi
    endcase

// SPX
always @(posedge clk_mcu)
  if (~odf)
    casez (op)
      10'b00_0010_00?1, // lbm
      10'b01_0001_0101, // lmady
      10'b01_0001_0001: SPX <= X; // lmaiy
      10'b10_0010_00?1, // xmb
      10'b10_0000_10?1, // xma
      10'b00_0000_10?1, // lam
      10'b00_0000_00?1: SPX <= X; // xsp
    endcase

// SPY
always @(posedge clk_mcu)
  if (~odf)
    casez (op)
      10'b00_0010_001?, // lbm
      10'b10_0010_001?, // xmb
      10'b10_0000_101?, // xma
      10'b00_0000_101?, // lam
      10'b00_0000_001?: // xsp
        SPY <= Y;
    endcase

// o_R
wire [3:0] src = op[5] ? B : A;
always @(posedge clk_mcu) begin
  if (i_R0 != R[0]) R[0] <= i_R0;
  //if (i_R1 != 4'b0) R[1] <= i_R1;
  //if (i_R2 != 4'b0) R[2] <= i_R2;
  //if (i_R3 != 4'b0) R[3] <= i_R3;
  casez (op)
    10'b10_11?0_0???: // lra/lrb
      R[p3] <= src;
    10'b11_0110_1???: // p
      if (nxtop[9])
        { R[2], R[3] } <= {
          nxtop[0], nxtop[1],
          nxtop[2], nxtop[3],
          nxtop[4], nxtop[5],
          nxtop[6], nxtop[7]
        };
  endcase
end

// mask
always @*
  case (op[1:0])
    2'b00: mask = 4'b0001;
    2'b01: mask = 4'b0010;
    2'b10: mask = 4'b0100;
    2'b11: mask = 4'b1000;
  endcase

// prescaler 100khz
always @(posedge clk_mcu)
  if (~reset) begin
    prescaler <= prescaler + 6'b1;
    if (~odf)
      casez (op)
        10'b01_0111_????, // lti
        10'b00_0011_1100: // lta
          prescaler <= 6'b1; // todo change to zero?
      endcase
  end
  else
    prescaler <= 0;

// prescaler overflow
always @(posedge clk)
  po <= prescaler == 6'b111111;

// counter pulse
reg cpulse;
always @(posedge clk_mcu)
  cpulse <= (i_int1 & CF) | (~CF & po);

// counter
always @(posedge clk_mcu)
  if (reset) begin
    counter <= 0;
    TF <= 1'b1;
  end
  else begin
    if (cpulse) begin
      counter <= counter + 4'b1;
      if (counter == 4'b1111) TF <= 1'b1;
    end
    casez (op)
      10'b00_0011_1100: counter <= A; // lta
      10'b01_0111_????: if (~odf) counter <= imm; // lti
      10'b00_1010_0101: TF <= 1'b1; // setf
      10'b10_1010_0101: TF <= 1'b0; // retf
    endcase
  end

// IR, IE
always @(posedge clk)
  if ((i_int0 & ~IF0) | (i_int1 & ~IF1) | ~TF)
    IR <= 1'b1;
  else if (IR & IE) begin
    IR <= 1'b0;
    IE <= 1'b0;
  end
  else
    case (op)
      10'b11_1010_0100, // rtni
      10'b00_1010_0100: IE <= 1'b1; // seie
      10'b10_1010_0100: IE <= 1'b0; // reie
    endcase

// CF
always @(posedge clk_mcu)
  casez (op)
    10'b00_1010_0001: CF <= 1'b1; // secf
    10'b10_1010_0001: CF <= 1'b0; // recf
  endcase

// IF0
always @(posedge clk)
  if (clk_mcu)
    casez (op)
      10'b00_1010_0010: IF0 <= 1'b1; // seif0
      10'b10_1010_0010: IF0 <= 1'b0; // reif0
    endcase

// IF1
always @(posedge clk)
  if (clk_mcu)
    casez (op)
      10'b00_1010_0000: IF1 <= 1'b1; // seif1
      10'b10_1010_0000: IF1 <= 1'b0; // reif1
    endcase

// stack
always @(posedge clk_mcu) begin
  casez (nxtop)
    10'b11_1010_0111, // rtn
    10'b11_1010_0100: { ST[0], ST[1], ST[2] } <= { ST[1], ST[2], ST[3] };
    10'b11_11??_????: if (status) { ST[0], ST[1], ST[2], ST[3] } <= { PC_page, PC_addr_next, ST[0], ST[1], ST[2] }; // cal
  endcase
  if (IR & IE) { ST[0], ST[1], ST[2], ST[3] } <= { PC_page, PC_addr_next, ST[0], ST[1], ST[2] };
end

// PC_addr_next
reg [5:0] PC_addr_next;
always @*
  PC_addr_next = {
    PC_addr[4:0],
      PC_addr == 6'b011111 ? 1'b1 :
      PC_addr == 6'b111111 ? 1'b0 :
      PC_addr[5] == PC_addr[4]
  };

// PC_page, PC_addr
always @(posedge clk_mcu)
  if (~reset) begin

    if (~PAT) begin

      if (IR & IE)

        { PC_page, PC_addr } <= ~TF ? 11'h13f : 11'h03f;

      else begin

        { PC_page, PC_addr } <= { PC_page, PC_addr_next };

        casez (nxtop)
          10'b01_11??_????: if (status) PC_addr <= nxtop[5:0]; // br
          10'b11_11??_????: if (status) { PC_page, PC_addr } <= { 5'd0, nxtop[5:0] }; // cal
          10'b11_1010_0111, // rtn
          10'b11_1010_0100: { PC_page, PC_addr } <= ST[0]; // rtni
          10'b11_0110_0???: { PC_page, PC_addr } <= mpc[10:0]; // tbr
          default: PC_addr <= PC_addr_next;
        endcase

        if (op[9:5] == 5'b11010 && status) PC_page <= op[4:0]; // lpu

      end

    end

  end
  else
    { PC_page, PC_addr } <= 11'h7ff;

endmodule
