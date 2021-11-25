// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * SM4 Sbox unit
 */
module ibex_sm4_sbox (
input  logic [7:0] in,
output logic [7:0] fx
);

// sm4_sbox_top
function automatic logic [20:0] sm4_sbox_top(logic [7:0] x);
    logic  y20;
    logic  y19, y18, y17, y16, y15, y14, y13, y12, y11, y10;
    logic  y9,  y8,  y7,  y6,  y5,  y4,  y3,  y2,  y1,  y0 ;
    logic  t6,  t5,  t4,  t3,  t2,  t1,  t0 ;

    assign y18 = x[ 2] ^  x[ 6];
    assign t0  = x[ 3] ^  x[ 4];
    assign t1  = x[ 2] ^  x[ 7];
    assign t2  = x[ 7] ^  y18  ;
    assign t3  = x[ 1] ^  t1   ;
    assign t4  = x[ 6] ^  x[ 7];
    assign t5  = x[ 0] ^  y18  ;
    assign t6  = x[ 3] ^  x[ 6];
    assign y10 = x[ 1] ^  y18;
    assign y0  = x[ 5] ^~ y10;
    assign y1  = t0    ^  t3 ;
    assign y2  = x[ 0] ^  t0 ;
    assign y4  = x[ 0] ^  t3 ;
    assign y3  = x[ 3] ^  y4 ;
    assign y5  = x[ 5] ^  t5 ;
    assign y6  = x[ 0] ^~ x[ 1];
    assign y7  = t0    ^~ y10;
    assign y8  = t0    ^  t5 ;
    assign y9  = x[ 3];
    assign y11 = t0    ^  t4 ;
    assign y12 = x[ 5] ^  t4 ;
    assign y13 = x[ 5] ^~ y1 ;
    assign y14 = x[ 4] ^~ t2 ;
    assign y15 = x[ 1] ^~ t6 ;
    assign y16 = x[ 0] ^~ t2 ;
    assign y17 = t0    ^~ t2 ;
    assign y19 = x[ 5] ^~ y14;
    assign y20 = x[ 0] ^  t1 ;

    return {y20, y19, y18, y17, y16, y15, y14, y13, y12, y11,
            y10, y9,  y8,  y7,  y6,  y5,  y4,  y3,  y2,  y1,  y0};
endfunction

// sm4_sbox_out
function automatic logic [7:0] sm4_sbox_out(logic [17:0] x);
    logic [7:0] y;
    logic  t29, t28, t27, t26, t25, t24, t23, t22, t21, t20;
    logic  t19, t18, t17, t16, t15, t14, t13, t12, t11, t10;
    logic  t9,  t8,  t7,  t6,  t5,  t4,  t3,  t2,  t1,  t0 ;
    assign t0   = x[ 4] ^  x[ 7];
    assign t1   = x[13] ^  x[15];
    assign t2   = x[ 2] ^  x[16];
    assign t3   = x[ 6] ^  t0;
    assign t4   = x[12] ^  t1;
    assign t5   = x[ 9] ^  x[10];
    assign t6   = x[11] ^  t2;
    assign t7   = x[ 1] ^  t4;
    assign t8   = x[ 0] ^  x[17];
    assign t9   = x[ 3] ^  x[17];
    assign t10  = x[ 8] ^  t3;
    assign t11  = t2    ^  t5;
    assign t12  = x[14] ^  t6;
    assign t13  = t7    ^  t9;
    assign t14  = x[ 0] ^  x[ 6];
    assign t15  = x[ 7] ^  x[16];
    assign t16  = x[ 5] ^  x[13];
    assign t17  = x[ 3] ^  x[15];
    assign t18  = x[10] ^  x[12];
    assign t19  = x[ 9] ^  t1 ;
    assign t20  = x[ 4] ^  t4 ;
    assign t21  = x[14] ^  t3 ;
    assign t22  = x[16] ^  t5 ;
    assign t23  = t7    ^  t14;
    assign t24  = t8    ^  t11;
    assign t25  = t0    ^  t12;
    assign t26  = t17   ^  t3 ;
    assign t27  = t18   ^  t10;
    assign t28  = t19   ^  t6 ;
    assign t29  = t8    ^  t10;
    assign y[0] = t11   ^~ t13;
    assign y[1] = t15   ^~ t23;
    assign y[2] = t20   ^  t24;
    assign y[3] = t16   ^  t25;
    assign y[4] = t26   ^~ t22;
    assign y[5] = t21   ^  t13;
    assign y[6] = t27   ^~ t12;
    assign y[7] = t28   ^~ t29;

    return  y;
endfunction


// sm4_sbox_inv_mid
function automatic logic [17:0] sm4_sbox_inv_mid(logic [20:0] x);
    logic [17:0] y;
    logic  t45, t44, t43, t42, t41, t40;
    logic  t39, t38, t37, t36, t35, t34, t33, t32, t31, t30;
    logic  t29, t28, t27, t26, t25, t24, t23, t22, t21, t20;
    logic  t19, t18, t17, t16, t15, t14, t13, t12, t11, t10;
    logic  t9,  t8,  t7,  t6,  t5,  t4,  t3,  t2,  t1,  t0 ;
    assign t0  = x[ 3] ^  x[12];
    assign t1  = x[ 9] &  x[ 5];
    assign t2  = x[17] &  x[ 6];
    assign t3  = x[10] ^  t1   ;
    assign t4  = x[14] &  x[ 0];
    assign t5  = t4    ^  t1   ;
    assign t6  = x[ 3] &  x[12];
    assign t7  = x[16] &  x[ 7];
    assign t8  = t0    ^  t6   ;
    assign t9  = x[15] &  x[13];
    assign t10 = t9    ^  t6   ;
    assign t11 = x[ 1] &  x[11];
    assign t12 = x[ 4] &  x[20];
    assign t13 = t12   ^  t11  ;
    assign t14 = x[ 2] &  x[ 8];
    assign t15 = t14   ^  t11  ;
    assign t16 = t3    ^  t2   ;
    assign t17 = t5    ^  x[18];
    assign t18 = t8    ^  t7   ;
    assign t19 = t10   ^  t15  ;
    assign t20 = t16   ^  t13  ;
    assign t21 = t17   ^  t15  ;
    assign t22 = t18   ^  t13  ;
    assign t23 = t19   ^  x[19];
    assign t24 = t22   ^  t23  ;
    assign t25 = t22   &  t20  ;
    assign t26 = t21   ^  t25  ;
    assign t27 = t20   ^  t21  ;
    assign t28 = t23   ^  t25  ;
    assign t29 = t28   &  t27  ;
    assign t30 = t26   &  t24  ;
    assign t31 = t20   &  t23  ;
    assign t32 = t27   &  t31  ;
    assign t33 = t27   ^  t25  ;
    assign t34 = t21   &  t22  ;
    assign t35 = t24   &  t34  ;
    assign t36 = t24   ^  t25  ;
    assign t37 = t21   ^  t29  ;
    assign t38 = t32   ^  t33  ;
    assign t39 = t23   ^  t30  ;
    assign t40 = t35   ^  t36  ;
    assign t41 = t38   ^  t40  ;
    assign t42 = t37   ^  t39  ;
    assign t43 = t37   ^  t38  ;
    assign t44 = t39   ^  t40  ;
    assign t45 = t42   ^  t41  ;
    assign y[ 0] = t38 &  x[ 7];
    assign y[ 1] = t37 &  x[13];
    assign y[ 2] = t42 &  x[11];
    assign y[ 3] = t45 &  x[20];
    assign y[ 4] = t41 &  x[ 8];
    assign y[ 5] = t44 &  x[ 9];
    assign y[ 6] = t40 &  x[17];
    assign y[ 7] = t39 &  x[14];
    assign y[ 8] = t43 &  x[ 3];
    assign y[ 9] = t38 &  x[16];
    assign y[10] = t37 &  x[15];
    assign y[11] = t42 &  x[ 1];
    assign y[12] = t45 &  x[ 4];
    assign y[13] = t41 &  x[ 2];
    assign y[14] = t44 &  x[ 5];
    assign y[15] = t40 &  x[ 6];
    assign y[16] = t39 &  x[ 0];
    assign y[17] = t43 &  x[12];

    return y;
endfunction

logic [20:0] t1;
logic [17:0] t2;

assign t1 = sm4_sbox_top(in);
assign t2 = sm4_sbox_inv_mid(t1);
assign fx = sm4_sbox_out(t2);

endmodule



