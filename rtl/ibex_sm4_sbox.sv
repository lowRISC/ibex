// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * SM4 Sbox unit
 * This modified version is derived from the orignal implemenatation by Markku-Juhani O. Saarinen,
 * which bases on the optimised AES structure proposed by Boyar & Peralta [BoPe12].
 * S-Boxes are broken into a nonlinear middle layer and two linear top and bottom layers.
 * Two linear top and bottom layers are modified to adapt for SM4 cipher.
 *
 * [BoPe12] Boyar J., Peralta R. "A Small Depth-16 Circuit for the AES
 *     S-Box." Proc.SEC 2012. IFIP AICT 376. Springer, pp. 287-298 (2012)
 *     DOI: https://doi.org/10.1007/978-3-642-30436-1_24
 *     Preprint: https://eprint.iacr.org/2011/332.pdf
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

    y18 = x[ 2] ^  x[ 6];
    t0  = x[ 3] ^  x[ 4];
    t1  = x[ 2] ^  x[ 7];
    t2  = x[ 7] ^  y18  ;
    t3  = x[ 1] ^  t1   ;
    t4  = x[ 6] ^  x[ 7];
    t5  = x[ 0] ^  y18  ;
    t6  = x[ 3] ^  x[ 6];
    y10 = x[ 1] ^  y18;
    y0  = x[ 5] ^~ y10;
    y1  = t0    ^  t3 ;
    y2  = x[ 0] ^  t0 ;
    y4  = x[ 0] ^  t3 ;
    y3  = x[ 3] ^  y4 ;
    y5  = x[ 5] ^  t5 ;
    y6  = x[ 0] ^~ x[ 1];
    y7  = t0    ^~ y10;
    y8  = t0    ^  t5 ;
    y9  = x[ 3];
    y11 = t0    ^  t4 ;
    y12 = x[ 5] ^  t4 ;
    y13 = x[ 5] ^~ y1 ;
    y14 = x[ 4] ^~ t2 ;
    y15 = x[ 1] ^~ t6 ;
    y16 = x[ 0] ^~ t2 ;
    y17 = t0    ^~ t2 ;
    y19 = x[ 5] ^~ y14;
    y20 = x[ 0] ^  t1 ;

    return {y20, y19, y18, y17, y16, y15, y14, y13, y12, y11,
            y10, y9,  y8,  y7,  y6,  y5,  y4,  y3,  y2,  y1,  y0};
endfunction

// sm4_sbox_out
function automatic logic [7:0] sm4_sbox_out(logic [17:0] x);
    logic [7:0] y;
    logic  t29, t28, t27, t26, t25, t24, t23, t22, t21, t20;
    logic  t19, t18, t17, t16, t15, t14, t13, t12, t11, t10;
    logic  t9,  t8,  t7,  t6,  t5,  t4,  t3,  t2,  t1,  t0 ;
    t0   = x[ 4] ^  x[ 7];
    t1   = x[13] ^  x[15];
    t2   = x[ 2] ^  x[16];
    t3   = x[ 6] ^  t0;
    t4   = x[12] ^  t1;
    t5   = x[ 9] ^  x[10];
    t6   = x[11] ^  t2;
    t7   = x[ 1] ^  t4;
    t8   = x[ 0] ^  x[17];
    t9   = x[ 3] ^  x[17];
    t10  = x[ 8] ^  t3;
    t11  = t2    ^  t5;
    t12  = x[14] ^  t6;
    t13  = t7    ^  t9;
    t14  = x[ 0] ^  x[ 6];
    t15  = x[ 7] ^  x[16];
    t16  = x[ 5] ^  x[13];
    t17  = x[ 3] ^  x[15];
    t18  = x[10] ^  x[12];
    t19  = x[ 9] ^  t1 ;
    t20  = x[ 4] ^  t4 ;
    t21  = x[14] ^  t3 ;
    t22  = x[16] ^  t5 ;
    t23  = t7    ^  t14;
    t24  = t8    ^  t11;
    t25  = t0    ^  t12;
    t26  = t17   ^  t3 ;
    t27  = t18   ^  t10;
    t28  = t19   ^  t6 ;
    t29  = t8    ^  t10;
    y[0] = t11   ^~ t13;
    y[1] = t15   ^~ t23;
    y[2] = t20   ^  t24;
    y[3] = t16   ^  t25;
    y[4] = t26   ^~ t22;
    y[5] = t21   ^  t13;
    y[6] = t27   ^~ t12;
    y[7] = t28   ^~ t29;

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
    t0  = x[ 3] ^  x[12];
    t1  = x[ 9] &  x[ 5];
    t2  = x[17] &  x[ 6];
    t3  = x[10] ^  t1   ;
    t4  = x[14] &  x[ 0];
    t5  = t4    ^  t1   ;
    t6  = x[ 3] &  x[12];
    t7  = x[16] &  x[ 7];
    t8  = t0    ^  t6   ;
    t9  = x[15] &  x[13];
    t10 = t9    ^  t6   ;
    t11 = x[ 1] &  x[11];
    t12 = x[ 4] &  x[20];
    t13 = t12   ^  t11  ;
    t14 = x[ 2] &  x[ 8];
    t15 = t14   ^  t11  ;
    t16 = t3    ^  t2   ;
    t17 = t5    ^  x[18];
    t18 = t8    ^  t7   ;
    t19 = t10   ^  t15  ;
    t20 = t16   ^  t13  ;
    t21 = t17   ^  t15  ;
    t22 = t18   ^  t13  ;
    t23 = t19   ^  x[19];
    t24 = t22   ^  t23  ;
    t25 = t22   &  t20  ;
    t26 = t21   ^  t25  ;
    t27 = t20   ^  t21  ;
    t28 = t23   ^  t25  ;
    t29 = t28   &  t27  ;
    t30 = t26   &  t24  ;
    t31 = t20   &  t23  ;
    t32 = t27   &  t31  ;
    t33 = t27   ^  t25  ;
    t34 = t21   &  t22  ;
    t35 = t24   &  t34  ;
    t36 = t24   ^  t25  ;
    t37 = t21   ^  t29  ;
    t38 = t32   ^  t33  ;
    t39 = t23   ^  t30  ;
    t40 = t35   ^  t36  ;
    t41 = t38   ^  t40  ;
    t42 = t37   ^  t39  ;
    t43 = t37   ^  t38  ;
    t44 = t39   ^  t40  ;
    t45 = t42   ^  t41  ;
    y[ 0] = t38 &  x[ 7];
    y[ 1] = t37 &  x[13];
    y[ 2] = t42 &  x[11];
    y[ 3] = t45 &  x[20];
    y[ 4] = t41 &  x[ 8];
    y[ 5] = t44 &  x[ 9];
    y[ 6] = t40 &  x[17];
    y[ 7] = t39 &  x[14];
    y[ 8] = t43 &  x[ 3];
    y[ 9] = t38 &  x[16];
    y[10] = t37 &  x[15];
    y[11] = t42 &  x[ 1];
    y[12] = t45 &  x[ 4];
    y[13] = t41 &  x[ 2];
    y[14] = t44 &  x[ 5];
    y[15] = t40 &  x[ 6];
    y[16] = t39 &  x[ 0];
    y[17] = t43 &  x[12];

    return y;
endfunction

logic [20:0] t1;
logic [17:0] t2;

assign t1 = sm4_sbox_top(in);
assign t2 = sm4_sbox_inv_mid(t1);
assign fx = sm4_sbox_out(t2);

endmodule



