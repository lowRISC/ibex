/*!
 * THIS checks that CSetBoundsRoundDown meets its description: the result leaves
 * the base unaltered and returns a capability with length at most the requested
 * size.
 */
$property
function prop_setboundsrounddown_brief(reqBase : CapAddrBits, reqLen : CapAddrBits) -> bool = {
    let c = setCapBoundsRoundDown(root_cap_mem, reqBase, reqLen);
    let (resBase, resTop) = getCapBoundsBits(c);
    let reqTop = (0b0 @ reqBase) + (0b0 @ reqLen);
    let saneTop = reqTop <=_u 0b1@0x00000000;
    saneTop --> ((resBase == reqBase) & (resTop <=_u reqTop) & 
                 (0b0 @ resBase <=_u resTop) & capEncodable(c))
}

/*!
 * THIS checks that exactly representable requests give equal answers between
 * CSetBoundsRoundDown and CSetBounds, so long as the requested length is
 * representable with exponent 14 or below.
 */
$property
function prop_setboundsrounddown_exact(reqBase : CapAddrBits, reqLen : CapAddrBits) -> bool = {
    let cRD = setCapBoundsRoundDown(root_cap_mem, reqBase, reqLen);
    let (exact, cSB) = setCapBounds(root_cap_mem, reqBase, reqLen);
    let threshold14 : CapAddrBits = zero_extend(ones(cap_mantissa_width)) << 14;
    (exact & (reqLen <=_u threshold14)) --> (cRD == cSB)
}

/*!
 * THIS checks that the resulting capability has nonzero length unless requested
 */
$property
function prop_setboundsrounddown_nonzero(reqBase : CapAddrBits, reqLen : CapAddrBits) -> bool = {
    let c = setCapBoundsRoundDown(root_cap_mem, reqBase, reqLen);
    let (resBase, resTop) = getCapBoundsBits(c);
    let reqTop = (0b0 @ reqBase) + (0b0 @ reqLen);
    let saneTop = reqTop <=_u 0b1@0x00000000;
    saneTop --> ( (0b0 @ resBase <_u resTop)
                | ((0b0 @ resBase == resTop) & (reqLen == zeros())))
}

/*!
 * THIS checks that [setCapBoundsRoundDown] returns the most precise encodable
 * bounds that satisfy the requested bounds, unless the requested length is
 * very large (above exponent 14), in which case the result is the largest
 * exponent 14 capability.
 */
$property
function prop_setboundsrounddown_precise(reqBase1 : CapAddrBits, reqLen1 : CapAddrBits,
        c2 : CapBits) -> bool = {
    let c1 = setCapBoundsRoundDown(root_cap_mem, reqBase1, reqLen1);
    let (b1, t1) = getCapBoundsBits(c1);
    let reqTop1 = (0b0 @ reqBase1) + (0b0 @ reqLen1);
    let saneTop1 = reqTop1 <=_u 0b1@0x00000000;
    let (b2, t2) = getCapBoundsBits(capBitsToCapability(false, c2));
    let validBase = b2 == reqBase1;
    let validTop = t2 <=_u reqTop1;
    let betterTop = t1 <_u t2;
    let threshold14 : CapAddrBits = zero_extend(ones(cap_mantissa_width)) << 14;
    (saneTop1 & validBase & validTop & betterTop) -->
      ((reqLen1 >=_u threshold14) & (t1 - (0b0 @ b1) == 0b0 @ threshold14))
}

/*!
 * THIS checks that the resulting capability is aligned to at least the
 * minimum of the requested base and length alignments (when the requested
 * top is sane and the minimum alignment is at most 14). This is important for
 * a use in the switcher where we want to ensure that stack pointers and bounds
 * are aligned to at least 16 bytes as per discussion at
 * https://github.com/CHERIoT-Platform/cheriot-rtos/pull/632 .
 */
$property
function prop_setboundsrounddown_aligned(reqBase : CapAddrBits, reqLen : CapAddrBits) -> bool = {
    let minReqAlign = min(count_trailing_zeros(reqBase),
                          count_trailing_zeros(reqLen));

    let c = setCapBoundsRoundDown(root_cap_mem, reqBase, reqLen);
    let (resBase, resTop) = getCapBoundsBits(c);

    let reqTop = (0b0 @ reqBase) + (0b0 @ reqLen);
    let saneTop = reqTop <=_u 0b1@0x00000000;

    (saneTop & (minReqAlign <= 14)) -->
      (count_trailing_zeros(resTop) >= minReqAlign)
}

/*!
 * THIS checks that any bounds returned by [setCapBoundsRoundDown] could also
 * be returned by [setCapBounds] i.e. that setCapBoundsRoundDown doesn't use
 * any non-canonoical encodings that setCapBounds won't produce. This is 
 * important important for [prop_setbounds_monotonic] which uses an inductive
 * argument based on the output of setCapBounds.
 */
$property
function prop_setboundsrounddown_canonical(reqBase : CapAddrBits, reqLen : CapAddrBits) -> bool = {
    let cRD = setCapBoundsRoundDown(root_cap_mem, reqBase, reqLen);
    let (bRD, tRD) = getCapBoundsBits(cRD);
    let reqTop = (0b0 @ reqBase) + (0b0 @ reqLen);
    let saneTop = reqTop <=_u 0b1@0x00000000;
    let rd_len = tRD - (0b0 @ bRD);
    /* since setCapBoundsRoundDown can't produce a length greater than 2**32 - 1
     * (checked below) we can safely truncate it to 32 bits and use setCapBounds
     * to check that the resulting encoding is identical. */
    let (exact, cSB) = setCapBounds(root_cap_mem, bRD, truncate(rd_len, 32));
    (rd_len <_u 0b1@0x00000000) & (saneTop --> (exact & cRD == cSB))
}
