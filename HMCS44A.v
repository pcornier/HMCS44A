
module HMCS44A(
  input clk, // 400kHz
  input reset,

  input [15:0] Di,
  output reg [15:0] Do,

  input [3:0] Ri0,
  input [3:0] Ri1,
  input [3:0] Ri2,
  input [3:0] Ri3,

  output [3:0] Ro0,
  output [3:0] Ro1,
  output [3:0] Ro2,
  output [3:0] Ro3,

  input int0,
  input int1
);

reg [3:0] R[7:0];

assign Ro0 = R[0];
assign Ro1 = R[1];
assign Ro2 = R[2];
assign Ro3 = R[3];

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
reg [2:0] alu_op;
reg [3:0] alu_a, alu_b, alu_out;
reg [3:0] counter;
reg [5:0] prescaler;
reg po; // prescaler, overflow output pulse
reg CF; // 0 = timer mode, 1 = counter mode (int1)
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
  if (PAT)
    odf <= 1'b1;
  else
    odf <= 1'b0;

// Do
always @(posedge clk_mcu)
    casez (op)
      10'b10_1001_0000: // red
        Do[Y] <= 1'b0;
      10'b00_1001_0000: // sed
        Do[Y] <= 1'b1;
      10'b00_1101_00??: // sedd affects D[3:0] only
        Do[3:0] <= Do[3:0] | mask;
      10'b10_1101_00??: // redd
        Do[3:0] <= Do[3:0] & ~mask;
    endcase

// alu
// 000: add
// 001: sub
// 010: sbc
// 011: adc
always @*
  case (alu_op)
    3'b000: { alu_c, alu_out } = alu_a + alu_b;
    3'b001: { alu_c, alu_out } = alu_a - alu_b;
    3'b010: { alu_c, alu_out } = alu_a - alu_b - { 3'd0, carry };
    3'b011: { alu_c, alu_out } = alu_a + alu_b + { 3'd0, carry };
  endcase

// status
always @*
  if (reset)
    status = 1'b1;
  else if (~odf)
		  casez (op)
		    10'b11_11??_????, // cal
		    10'b01_11??_????: // br
		      status = 1'b1;
		    10'b00_1001_0100: // td
		      status = Di[Y];
		    10'b10_0011_0100, // alem
		    10'b00_0010_0100, // blem
		    10'b10_0111_????: // alei
		      status = ~alu_c;
		    10'b10_0101_1000, // syy
		    10'b10_0011_0000, // smc
		    10'b00_0011_0100, // am
		    10'b00_1000_????: // ai
		      status = alu_c;
		    10'b01_0001_000?, // lmaiy
		    10'b00_0110_0100, // ib
		    10'b00_0101_0100, // iy
		    10'b10_0101_0100, // dy
		    10'b10_0110_0111, // db
		    10'b00_0001_????: // lmiiy
		      status = ~alu_c;
		    10'b10_0000_00??: // tm
		      status = (buffer & mask) != 0 ? 1'b1 : 1'b0;
		    10'b01_1010_0000: // tif1
		      status = IF1;
		    10'b01_1010_0001: // ti1
		      status = int1;
		    10'b01_1010_0010: // tif0
		      status = IF0;
		    10'b01_1010_0011: // ti0
		      status = int0;
		    10'b01_1010_0101: // ttf
		      status = TF;
		    10'b11_0010_0100, // bnem
		    10'b10_0001_????, // mnei
		    10'b10_1000_????, // ynei
		    10'b01_0010_0100: // anem
		      status = alu_out != 0 ? 1'b1 : 1'b0;
		    10'b10_0100_1111: // tc
		      status = carry;
		  endcase

// carry
always @(posedge clk_mcu)
  casez (op)
    10'b00_0100_1100: // rec
      carry <= 1'b0;
    10'b10_0011_0000, // smc
    10'b00_0011_0000: // amc
      carry <= alu_c;
    10'b00_0100_0101: // das
      if (A >= 9) carry <= 0; // todo: use alu
    10'b00_0100_0110: // daa
      if (A >= 9) carry <= 1; // todo: use alu
    10'b00_0100_1111: // sec
      carry <= 1'b1;
    10'b10_0010_0100: // rotr
      carry <= A[0];
    10'b10_0010_0101: // rotl
      carry <= A[3];
  endcase

// alu_a
always @(posedge clk)
  casez (op)
    10'b11_0010_0100, // bnem
    10'b10_0110_0111, // db
    10'b00_0110_0100: // ib
      alu_a <= B;
    10'b10_0101_1000, // syy
    10'b01_0001_010?, // lmady
    10'b01_0001_000?, // lmaiy
    10'b10_1000_????, // ynei
    10'b10_0101_0100, // dy
    10'b00_0101_1000, // ayy
    10'b00_0101_0100, // iy
    10'b00_0001_????: // lmiiy
      alu_a <= Y;
    10'b01_0010_0100, // anem
    10'b00_1000_????, // ai
    10'b00_0011_0100, // am
    10'b00_0011_0000: // amc
      alu_a <= A;
    10'b10_0011_0100, // alem
    10'b10_0001_????, // mnei
    10'b10_0011_0000, // smc
    10'b00_0010_0100: // blem
      alu_a <= buffer;
    10'b10_0100_0100: // nega
      alu_a <= ~A;
    10'b10_0111_????: // alei
      alu_a <= imm;
  endcase

// alu_b
always @(posedge clk)
  casez (op)
    10'b11_0010_0100, // bnem
    10'b01_0010_0100, // anem
    10'b00_0011_0100, // am
    10'b00_0011_0000: // amc
      alu_b <= buffer;
    10'b01_0001_010?, // lmady
    10'b01_0001_000?, // lmaiy
    10'b00_0110_0100, // ib
    10'b10_0101_0100, // dy
    10'b10_0100_0100, // nega
    10'b10_0110_0111, // db
    10'b00_0101_0100, // iy
    10'b00_0001_????: // lmiiy
      alu_b <= 4'b1;
    10'b10_0111_????, // alei
    10'b10_0011_0100, // alem
    10'b10_0101_1000, // syy
    10'b10_0011_0000, // smc
    10'b00_0101_1000: // ayy
      alu_b <= A;
    10'b10_0001_????, // mnei
    10'b10_1000_????, // ynei
    10'b00_1000_????: // ai
      alu_b <= imm;
    10'b00_0010_0100: // blem
      alu_b <= B;
  endcase

// alu_op
always @(posedge clk)
  casez (op)
    10'b01_0001_000?, // lmaiy
    10'b10_0100_0100, // nega
    10'b00_1000_????, // ai
    10'b00_0110_0100, // ib
    10'b00_0101_1000, // ayy
    10'b00_0101_0100, // iy
    10'b00_0011_0100, // am
    10'b00_0001_????: // lmiiy
      alu_op <= 3'b000;
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
    10'b10_0110_0111: // db
      alu_op <= 3'b001;
    10'b00_0011_0000: // amc
      alu_op <= 3'b011;
    10'b10_0011_0000: // smc
      alu_op <= 3'b010;
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
  if (~RAM_we)
    RAM[RAM_addr] <= RAM_din;

// RAM_din
always @(posedge clk)
  casez (op)
    10'b10_0000_01??: // rem
      RAM_din <= buffer & ~mask;
    10'b00_0000_01??: // sem
      RAM_din <= buffer | mask;
    10'b00_0001_????: // lmiiy
      RAM_din <= imm;
    10'b10_0000_10??, // xma
    10'b01_0001_010?, // lmady
    10'b01_0001_000?, // lmaiy
    10'b00_1111_????: // xamr
      RAM_din <= A;
    10'b10_0010_00??: // xmb
      RAM_din <= B;
  endcase

// RAM_addr
always @*
  casez (op)
    10'b00_1111_????: // xamr
      RAM_addr = { 4'd9, op[3:0] };
    default:
      RAM_addr = X[3] ? { X[3], 2'b00, X[2], Y } : { X, Y };
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
		    10'b00_0000_01??: // sem
		      RAM_we = 1'b0;
		    default:
		      RAM_we = 1'b1;
		  endcase

// A
always @(posedge clk_mcu)
  if (~odf)
		  casez (op)
		    10'b00_0111_????: // lai
		      A <= imm;
		    10'b00_0011_0100, // am
		    10'b10_0011_0000, // smc
		    10'b10_0100_0100, // nega
		    10'b00_1000_????, // ai
		    10'b00_0011_0000: // amc
		      A <= alu_out;
		    10'b00_0100_0101: // das
		      if (~carry || A >= 9)
		        A <= A + 4'd10;
		    10'b00_0100_0110: // daa
		      if (~carry || A >= 9)
		        A <= A + 4'd6;
		    10'b00_1100_0???: // lar
		      A <= R[p3];
		    10'b10_0011_1100: // lat
		      A <= counter;
		    10'b01_0010_0000: // or
		      A <= A | B;
		    10'b10_0110_0000: // lab
		      A <= B;
		    10'b10_0000_10??, // xma
		    10'b00_0000_10??, // lam
		    10'b00_1111_????: // xamr
		      A <= buffer;
		    10'b10_0101_0000: // laspy
		      A <= SPY;
		    10'b10_0100_0000: // laspx
		      A <= SPX;
		    10'b01_0001_1000: // lay
		      A <= Y;
		    10'b10_0010_0100: // rotr
		      A <= { carry, A[3:1] };
		    10'b10_0010_0101: // rotl
		      A <= { A[2:0], carry };
		  endcase
		else
		  if (op[8])
		    A <= { op[0], op[1], op[2], op[3] };

// B
always @(posedge clk_mcu)
  if (~odf)
    casez (op)
      10'b00_0110_0000: // lba
        B <= A;
      10'b10_0010_00??, // xmb
      10'b00_0010_00??: // lbm
        B <= buffer;
      10'b10_0110_0111, // db
      10'b00_0110_0100: // ib
        B <= alu_out;
      10'b00_1110_0???: // lbr
        B <= R[p3];
      10'b01_0110_????: // lbi
        B <= imm;
      10'b11_0010_0000: // comb
        B <= ~B;
    endcase
  else
    if (op[8])
      B <= op[7:4];

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
		    10'b00_0000_00?1: // xsp
		      X <= SPX;
		    10'b00_0100_0000: // lxa
		      X <= A;
		    10'b01_0100_????: // lxi
		      X <= imm;
		  endcase

// Y
always @(posedge clk_mcu)
  if (~odf)
		  casez (op)
		    10'b10_0010_001?, // xmb
		    10'b10_0000_101?, // xma
		    10'b00_0010_001?, // lbm
		    10'b00_0000_101?, // lam
		    10'b00_0000_001?: // xsp
		      Y <= SPY;
		    10'b10_0101_1000, // syy
		    10'b01_0001_010?, // lmady
		    10'b01_0001_000?, // lmaiy
		    10'b00_0101_0100, // iy
		    10'b10_0101_0100, // dy
		    10'b00_0101_1000, // ayy
		    10'b00_0001_????: // lmiiy
		      Y <= alu_out;
		    10'b00_0101_0000: // lya
		      Y <= A;
		    10'b01_0101_????: // lyi
		      Y <= imm;
		  endcase

// SPX
always @(posedge clk_mcu)
  if (~odf)
		  casez (op)
		    10'b00_0010_00?1, // lbm
		    10'b01_0001_0101, // lmady
		    10'b01_0001_0001: // lmaiy
		      SPX <= X;
		    10'b10_0010_00?1, // xmb
		    10'b10_0000_10?1, // xma
		    10'b00_0000_10?1, // lam
		    10'b00_0000_00?1: // xsp
		      SPX <= X;
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

// Ro
wire [3:0] src = op[5] ? B : A;
always @(posedge clk_mcu) begin
  if (Ri0 != R[0]) R[0] <= Ri0;
  //if (Ri1 != 4'b0) R[1] <= Ri1;
  //if (Ri2 != 4'b0) R[2] <= Ri2;
  //if (Ri3 != 4'b0) R[3] <= Ri3;
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
				      prescaler <= 0; // todo set to 0
				  endcase
		end
		else
		  prescaler <= 0;

// prescaler overflow
always @(posedge clk)
  po <= prescaler == 6'b111111;

// CF
always @(posedge clk_mcu)
  casez (op)
    10'b00_1010_0001: // secf
      CF <= 1'b1;
    10'b10_1010_0001: // recf
      CF <= 1'b0;
  endcase

// counter pulse
reg cpulse;
always @(posedge clk_mcu)
  cpulse <= (int1 & CF) | (~CF & po);

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
      10'b00_0011_1100: // lta
        counter <= A;
      10'b01_0111_????: // lti
        if (~odf)
          counter <= imm;
      10'b00_1010_0101: // setf
		      TF <= 1'b1;
		    10'b10_1010_0101: // retf
		      TF <= 1'b0;
    endcase
  end

// IR, IE
always @(posedge clk)
  if ((int0 & ~IF0) | (int1 & ~IF1) | ~TF)
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

// IF0
always @(posedge clk)
  if (clk_mcu)
    casez (op)
      10'b00_1010_0010: // seif0
        IF0 <= 1'b1;
      10'b10_1010_0010: // reif0
        IF0 <= 1'b0;
    endcase

// IF1
always @(posedge clk)
  if (clk_mcu)
    casez (op)
      10'b00_1010_0000: // seif1
        IF1 <= 1'b1;
      10'b10_1010_0000: // reif1
        IF1 <= 1'b0;
    endcase

// push
reg push;
always @*
  if (IR & IE) push = 1'b1;
  else if (nxtop[9:6] == 4'b1111 & status) push = 1'b1;
  else push = 1'b0;

// pop
reg pop;
always @*
  case (nxtop)
    10'b11_1010_0111, // rtn
    10'b11_1010_0100: pop = 1'b1; // rtni
    default: pop = 1'b0;
  endcase

// stack
always @(posedge clk_mcu)
  if (push) begin
    ST[0] <= { PC_page, PC_addr_next };
    ST[1] <= ST[0];
    ST[2] <= ST[1];
    ST[3] <= ST[2];
  end
  else if (pop) begin
    ST[2] <= ST[3];
    ST[1] <= ST[2];
    ST[0] <= ST[1];
  end

reg [5:0] PC_addr_next;
always @*
  PC_addr_next = {
		  PC_addr[4:0],
			 PC_addr == 6'b011111 ? 1'b1 :
			 PC_addr == 6'b111111 ? 1'b0 :
			 PC_addr[5] == PC_addr[4]
		};

// PC_addr
always @(posedge clk_mcu)
  if (~reset) begin
    if (~PAT) begin
		    if (IR & IE)
		      if (~TF) // priority to inputs
		        { PC_page, PC_addr } <= 11'h13f;
		      else
		        { PC_page, PC_addr } <= 11'h03f;
		    else begin

		      if (nxtop[9:6] == 4'b0111 && status) // br
		        PC_addr <= nxtop[5:0];
		      else if (nxtop[9:6] == 4'b1111 && status) // cal
		        { PC_page, PC_addr } <= { 5'd0, nxtop[5:0] };
		      else if (pop) // rtn, rtni
		        { PC_page, PC_addr } <= ST[0];
		      else if (nxtop[9:3] == 7'b1101100)
		        { PC_page, PC_addr } <= mpc[10:0];
		      else
		        PC_addr <= PC_addr_next;

		      if (op[9:5] == 5'b11010 && status) // lpu
		        PC_page <= op[4:0];
			   end
	   end
 	end
  else
    { PC_page, PC_addr } <= 11'h7ff;

endmodule;