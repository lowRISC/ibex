// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * AES Sbox unit
 */
module ibex_aes_sbox (
input  logic       fw,
input  logic [7:0] in,
output logic [7:0] fx

);

// aes_sbox_top
function automatic logic [20:0] aes_sbox_top(logic [7:0] x);
    logic  y20;
    logic  y19, y18, y17, y16, y15, y14, y13, y12, y11, y10;
    logic  y9,  y8,  y7,  y6,  y5,  y4,  y3,  y2,  y1,  y0 ;
    logic  t5,  t4,  t3,  t2,  t1,  t0 ;

    assign y0    = x[ 0] ;
    assign y1    = x[ 7] ^     x[ 4];
    assign y2    = x[ 7] ^     x[ 2];
    assign y3    = x[ 7] ^     x[ 1];
    assign y4    = x[ 4] ^     x[ 2];
    assign t0    = x[ 3] ^     x[ 1];
    assign y5    = y1    ^     t0   ;
    assign t1    = x[ 6] ^     x[ 5];
    assign y6    = x[ 0] ^     y5   ;
    assign y7    = x[ 0] ^     t1   ;
    assign y8    = y5    ^     t1   ;
    assign t2    = x[ 6] ^     x[ 2];
    assign t3    = x[ 5] ^     x[ 2];
    assign y9    = y3    ^     y4   ;
    assign y10   = y5    ^     t2   ;
    assign y11   = t0    ^     t2   ;
    assign y12   = t0    ^     t3   ;
    assign y13   = y7    ^     y12  ;
    assign t4    = x[ 4] ^     x[ 0];
    assign y14   = t1    ^     t4   ;
    assign y15   = y1    ^     y14  ;
    assign t5    = x[ 1] ^     x[ 0];
    assign y16   = t1    ^     t5   ;
    assign y17   = y2    ^     y16  ;
    assign y18   = y2    ^     y8   ;
    assign y19   = y15   ^     y13  ;
    assign y20   = y1    ^     t3   ;

    return {y20, y19, y18, y17, y16, y15, y14, y13, y12, y11,
            y10, y9,  y8,  y7,  y6,  y5,  y4,  y3,  y2,  y1,  y0};
endfunction

// aes_sbox_out
function automatic logic [7:0] aes_sbox_out(logic [17:0] x);
    logic [7:0] y;
    logic  t29, t28, t27, t26, t25, t24, t23, t22, t21, t20;
    logic  t19, t18, t17, t16, t15, t14, t13, t12, t11, t10;
    logic  t9,  t8,  t7,  t6,  t5,  t4,  t3,  t2,  t1,  t0 ;
    assign t0   = x[11] ^  x[12];
    assign t1   = x[0] ^   x[6];
    assign t2   = x[14] ^  x[16];
    assign t3   = x[15] ^  x[5];
    assign t4   = x[4] ^   x[8];
    assign t5   = x[17] ^  x[11];
    assign t6   = x[12] ^  t5;
    assign t7   = x[14] ^  t3;
    assign t8   = x[1] ^   x[9];
    assign t9   = x[2] ^   x[3];
    assign t10  = x[3] ^   t4;
    assign t11  = x[10] ^  t2;
    assign t12  = x[16] ^  x[1];
    assign t13  = x[0] ^   t0;
    assign t14  = x[2] ^   x[11];
    assign t15  = x[5] ^   t1;
    assign t16  = x[6] ^   t0;
    assign t17  = x[7] ^   t1;
    assign t18  = x[8] ^   t8;
    assign t19  = x[13] ^  t4;
    assign t20  = t0 ^     t1;
    assign t21  = t1 ^     t7;
    assign t22  = t3 ^     t12;
    assign t23  = t18 ^    t2;
    assign t24  = t15 ^    t9;
    assign t25  = t6 ^     t10;
    assign t26  = t7 ^     t9;
    assign t27  = t8 ^     t10;
    assign t28  = t11 ^    t14;
    assign t29  = t11 ^    t17;
    assign  y[0] = t6 ^~  t23;
    assign  y[1] = t13 ^~ t27;
    assign  y[2] = t25 ^  t29;
    assign  y[3] = t20 ^  t22;
    assign  y[4] = t6 ^   t21;
    assign  y[5] = t19 ^~ t28;
    assign  y[6] = t16 ^~ t26;
    assign  y[7] = t6 ^   t24;
    return  y;
endfunction


// aes_sbox_inv_mid
function automatic logic [17:0] aes_sbox_inv_mid(logic [20:0] x);
    logic [17:0] y;
    logic  t45, t44, t43, t42, t41, t40;
    logic  t39, t38, t37, t36, t35, t34, t33, t32, t31, t30;
    logic  t29, t28, t27, t26, t25, t24, t23, t22, t21, t20;
    logic  t19, t18, t17, t16, t15, t14, t13, t12, t11, t10;
    logic  t9,  t8,  t7,  t6,  t5,  t4,  t3,  t2,  t1,  t0 ;
    assign t0  = x[ 3] ^     x[12];
    assign t1  = x[ 9] &     x[ 5];
    assign t2  = x[17] &     x[ 6];
    assign t3  = x[10] ^     t1   ;
    assign t4  = x[14] &     x[ 0];
    assign t5  = t4    ^     t1   ;
    assign t6  = x[ 3] &     x[12];
    assign t7  = x[16] &     x[ 7];
    assign t8  = t0    ^     t6   ;
    assign t9  = x[15] &     x[13];
    assign t10 = t9    ^     t6   ;
    assign t11 = x[ 1] &     x[11];
    assign t12 = x[ 4] &     x[20];
    assign t13 = t12   ^     t11  ;
    assign t14 = x[ 2] &     x[ 8];
    assign t15 = t14   ^     t11  ;
    assign t16 = t3    ^     t2   ;
    assign t17 = t5    ^     x[18];
    assign t18 = t8    ^     t7   ;
    assign t19 = t10   ^     t15  ;
    assign t20 = t16   ^     t13  ;
    assign t21 = t17   ^     t15  ;
    assign t22 = t18   ^     t13  ;
    assign t23 = t19   ^     x[19];
    assign t24 = t22   ^     t23  ;
    assign t25 = t22   &     t20  ;
    assign t26 = t21   ^     t25  ;
    assign t27 = t20   ^     t21  ;
    assign t28 = t23   ^     t25  ;
    assign t29 = t28   &     t27  ;
    assign t30 = t26   &     t24  ;
    assign t31 = t20   &     t23  ;
    assign t32 = t27   &     t31  ;
    assign t33 = t27   ^     t25  ;
    assign t34 = t21   &     t22  ;
    assign t35 = t24   &     t34  ;
    assign t36 = t24   ^     t25  ;
    assign t37 = t21   ^     t29  ;
    assign t38 = t32   ^     t33  ;
    assign t39 = t23   ^     t30  ;
    assign t40 = t35   ^     t36  ;
    assign t41 = t38   ^     t40  ;
    assign t42 = t37   ^     t39  ;
    assign t43 = t37   ^     t38  ;
    assign t44 = t39   ^     t40  ;
    assign t45 = t42   ^     t41  ;

    assign  y[ 0] = t38 &     x[ 7];
    assign  y[ 1] = t37 &     x[13];
    assign  y[ 2] = t42 &     x[11];
    assign  y[ 3] = t45 &     x[20];
    assign  y[ 4] = t41 &     x[ 8];
    assign  y[ 5] = t44 &     x[ 9];
    assign  y[ 6] = t40 &     x[17];
    assign  y[ 7] = t39 &     x[14];
    assign  y[ 8] = t43 &     x[ 3];
    assign  y[ 9] = t38 &     x[16];
    assign  y[10] = t37 &     x[15];
    assign  y[11] = t42 &     x[ 1];
    assign  y[12] = t45 &     x[ 4];
    assign  y[13] = t41 &     x[ 2];
    assign  y[14] = t44 &     x[ 5];
    assign  y[15] = t40 &     x[ 6];
    assign  y[16] = t39 &     x[ 0];
    assign  y[17] = t43 &     x[12];

    return y;
endfunction

// inverse aes_sbox_top
function automatic logic [20:0] aes_inv_sbox_top(logic [7:0] x);
    logic  y20;
    logic  y19, y18, y17, y16, y15, y14, y13, y12, y11, y10;
    logic  y9,  y8,  y7,  y6,  y5,  y4,  y3,  y2,  y1,  y0 ;
    logic  t4,  t3,  t2,  t1,  t0 ;
    assign y17 = x[ 7] ^     x[ 4];
    assign y16 = x[ 6] ^~ x[ 4];
    assign y2  = x[ 7] ^~ x[ 6];
    assign y1  = x[ 4] ^     x[ 3];
    assign y18 = x[ 3] ^~ x[ 0];
    assign t0  = x[ 1] ^     x[ 0];
    assign y6  = x[ 6] ^~ y17 ;
    assign y14 = y16  ^     t0;
    assign y7  = x[ 0] ^~ y1;
    assign y8  = y2  ^     y18;
    assign y9  = y2  ^     t0;
    assign y3  = y1  ^     t0;
    assign y19 = x[ 5] ^~ y1;
    assign t1  = x[ 6] ^    x[ 1];
    assign y13 = x[ 5] ^~ y14;
    assign y15 = y18  ^     t1;
    assign y4  = x[ 3] ^     y6;
    assign t2  = x[ 5] ^~ x[ 2];
    assign t3  = x[ 2] ^~ x[ 1];
    assign t4  = x[ 5] ^~ x[ 3];
    assign y5  = y16  ^     t2 ;
    assign y12 = t1  ^     t4 ;
    assign y20 = y1  ^     t3 ;
    assign y11 = y8  ^     y20 ;
    assign y10 = y8  ^     t3 ;
    assign y0  = x[ 7] ^     t2 ;

    return {y20, y19, y18, y17, y16, y15, y14, y13, y12, y11,
            y10, y9,  y8,  y7,  y6,  y5,  y4,  y3,  y2,  y1,  y0};
endfunction

// inverse aes_sbox_out
function automatic logic [7:0] aes_inv_sbox_out(logic [17:0] x);
    logic [7:0] y;
    logic  t29, t28, t27, t26, t25, t24, t23, t22,      t20;
    logic  t19, t18, t17, t16, t15, t14, t13, t12, t11, t10;
    logic  t9,  t8,  t7,  t6,  t5,  t4,  t3,  t2,  t1,  t0 ;
    assign t0  = x[ 2] ^     x[11];
    assign t1  = x[ 8] ^     x[ 9];
    assign t2  = x[ 4] ^     x[12];
    assign t3  = x[15] ^     x[ 0];
    assign t4  = x[16] ^     x[ 6];
    assign t5  = x[14] ^     x[ 1];
    assign t6  = x[17] ^     x[10];
    assign t7  = t0    ^     t1   ;
    assign t8  = x[ 0] ^     x[ 3];
    assign t9  = x[ 5] ^     x[13];
    assign t10 = x[ 7] ^     t4   ;
    assign t11 = t0    ^     t3   ;
    assign t12 = x[14] ^     x[16];
    assign t13 = x[17] ^     x[ 1];
    assign t14 = x[17] ^     x[12];
    assign t15 = x[ 4] ^     x[ 9];
    assign t16 = x[ 7] ^     x[11];
    assign t17 = x[ 8] ^     t2 ;
    assign t18 = x[13] ^     t5 ;
    assign t19 = t2   ^     t3 ;
    assign t20 = t4   ^     t6 ;
    assign t22 = t2   ^     t7 ;
    assign t23 = t7   ^     t8 ;
    assign t24 = t5   ^     t7 ;
    assign t25 = t6   ^     t10;
    assign t26 = t9   ^     t11;
    assign t27 = t10  ^     t18;
    assign t28 = t11  ^     t25;
    assign t29 = t15  ^     t20;

    assign y[ 0] = t9  ^ t16;
    assign y[ 1] = t14 ^ t23;
    assign y[ 2] = t19 ^ t24;
    assign y[ 3] = t23 ^ t27;
    assign y[ 4] = t12 ^ t22;
    assign y[ 5] = t17 ^ t28;
    assign y[ 6] = t26 ^ t29;
    assign y[ 7] = t13 ^ t22;
    return  y;
endfunction

logic [20:0] fwd_top, inv_top, top_box;
assign fwd_top = aes_sbox_top(in);
assign inv_top = aes_inv_sbox_top(in);
assign top_box = (fw)? fwd_top : inv_top;

logic [17:0] mid;
assign mid     = aes_sbox_inv_mid(top_box);

logic [ 7:0] fwd_out, inv_out;
assign fwd_out = aes_sbox_out(mid);
assign inv_out = aes_inv_sbox_out(mid);
assign fx      = (fw)? fwd_out : inv_out;

endmodule



