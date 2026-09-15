// $property
/*
 * THIS is not actually an invariant but is useful for characterising unusable
 * encodings. Ideally we'd like an encoding that ensures base is less than or
 * equal to top, but sadly this isn't true. Counterexamples are unusable
 * encodings. This can happen when a_top ends up being zero and T < B because
 * the attempted corrections can underflow a_top. There are other unusable
 * encodings too, for example those with top larger than 2**32.
 */
function prop_base_lteq_top(b : CapBits) -> bool = {
    let c = capBitsToCapability(false, b);
    let (base, top) = getCapBoundsBits(c);
    a_top = c.address >> (unsigned(c.E) + cap_mantissa_width);
    (a_top != zeros() | (c.B <_u c.T)) --> ((0b0 @ base) <=_u top)
}

$property
/*!
 * Check that null_cap as defined in the Sail encodes to all zeros.
 */
function prop_nullzero() -> bool = {
    capEncodable(null_cap)
  & (capToBits(null_cap) == zeros())
  & (null_cap.tag == false)
}

function hasMaxBounds(c: Capability) -> bool = {
    let (b, t) = getCapBounds(c) in
    b == 0 & t == pow2(32)
}

function validateRootCap(c : Capability) -> bool = {
    c.tag == true & capEncodable(c) & hasMaxBounds(c) & not(isCapSealed(c))
}

$property
/*!
 * Check that null_cap has no set permission bits.
 */
function prop_null_noperms() -> bool = {
  getCapPerms(null_cap) == zeros()
}

$property
/*!
 * Check that [root_cap_mem] is encodable
 */
function prop_mem_root() -> bool = { validateRootCap(root_cap_mem) }

$property
/*!
 * Check that [root_cap_exe] is encodable
 */
function prop_exe_root() -> bool = { validateRootCap(root_cap_exe) }

$property
/*!
 * Check that [root_cap_seal] is encodable
 */
function prop_seal_root() -> bool = { validateRootCap(root_cap_seal) }

$property
/*!
 * THIS checks that going from bits to Capability and back preserves bits. This is
 * a vital property to ensure that `memcpy` works.
 */
function prop_decEnc(t : bool, c : CapBits) -> bool  = {
    let cap = capBitsToCapability(t, c);
    let b = capToBits(cap);
    (c == b) & (cap.tag == t)
}

// $counterexample
/*!
 * THIS property attempts to prove that it is possible to recover T and B bits
 * from the decoded base and top. This would be important in an implementation
 * that decodes fully on load and recompresses on store. It fails when E is
 * cap_max_E because base is only 32-bits and we lose the top bit of B, but I
 * think it would hold if getCapBoundsBits returned a 33-bit base.
 */
function prop_decEnc2(c : CapBits) -> bool  = {
    let cap = capBitsToCapability(false, c);
    let (base, top) = getCapBoundsBits(cap);
    let newB = truncate(base >> unsigned(cap.E), cap_mantissa_width);
    let newT = truncate(top >> unsigned(cap.E), cap_mantissa_width);
    let cap2 = {cap with B=newB, T=newT};
    let c2 = capToBits(cap2);
    (c == c2)
}

// Disabled as currently triggers a performance bug in Sail SMT generation
// See https://github.com/rems-project/sail/issues/783
// $property
/*!
 * THIS checks that for any capability and permissions mask [CAndPerm]
 * will result in a capability whose permissions are a subset of the original
 * permissions and the mask.
 */
function prop_andperms(b : CapBits, mask : CapPermsBits) -> bool = {
    let c = capBitsToCapability(false, b);
    let perms = getCapPerms(c);
    let newCap = setCapPerms(c, perms & mask);
    /* We must encode then decode the resulting Capability to see the effect
     * of permissions compression. */
    let newCap2 = encodeDecode(newCap);
    let newPerms = getCapPerms(newCap2);
    /* Check that newperms are a subset of original perms and requested perms */
    ((newPerms & ~(perms)) == zeros()) & ((newPerms & ~(mask)) == zeros())
}

$property
/*!
 * THIS checks the basic properties of setBounds: that the resutling cap
 * includes the requested region and that the exact flag is correct. Note that
 * we restrict this to bounds where the top is less than or equal to the maximum
 * possible, since the encoding cannot handle all such cases and the ISA should
 * not allow creation of tagged capabilities with such top anyway.
 */
function prop_setbounds(reqBase : CapAddrBits, reqLen : CapAddrBits) -> bool = {
    let (exact, c) = setCapBounds(root_cap_mem, reqBase, reqLen);
    let encodable = capEncodable(c);
    let (b2, t2) = getCapBoundsBits(c);
    let reqTop = (0b0 @ reqBase) + (0b0 @ reqLen);
    let saneTop = reqTop <=_u 0b1@0x00000000;
    saneTop --> (
        encodable &
        (c.address == reqBase) &
        ((exact & (reqBase == b2) & (reqTop == t2))
        | (not(exact) & (b2 <=_u reqBase) & (reqTop <=_u t2)))
    )
}

// takes a while so uncomment to disable
$property
/*!
 * THIS checks monotonicity preservation of [setCapBounds]. For this we use two pairs of
 * base and length and set bounds first to one and then the other. In effect we
 * perform all possible pairs of set bounds operation and check that the result
 * respects monotonicity. This is not as trivial as it might seem
 * due to the rounding that setCapBounds has to do. The reason we don't start
 * with arbitrary capability bits is because some encodings are invalid and
 * won't be generated by setCapBounds, in particular when the exponent is
 * at the maximum and T < B.
 *
 * This is really only the inductive step of a monotonicity proof that relies
 * on the fact that setCapBounds only produces canonical encodings.
 * The base case for the root capability is checked in [prop_setbounds_monotonic_root].
 * This also requires that nothing else produces capabilities with non-canonical
 * bounds encodings. This is checked for setboundsrounddown in 
 * [prop_setboundsrounddown_canonical]. An alternative would be to characterise
 * the set of canonical encodings then we could make the assertion about an
 * arbitrary capability providing it is canonical.
 */
function prop_setbounds_monotonic(
        reqBase1 : CapAddrBits, reqLen1 : CapAddrBits,
        reqBase2 : CapAddrBits, reqLen2 : CapAddrBits) -> bool = {
    let (exact1, c1) = setCapBounds(root_cap_mem, reqBase1, reqLen1);
    let (b1, t1) = getCapBoundsBits(c1);
    let reqTop1 = (0b0 @ reqBase1) + (0b0 @ reqLen1);
    let saneTop1 = reqTop1 <=_u 0b1@0x00000000;
    let reqTop2 = (0b0 @ reqBase2) + (0b0 @ reqLen2);
    let (exact2, c2) = setCapBounds(c1, reqBase2, reqLen2);
    let (b2, t2) = getCapBoundsBits(c2);
    let requestMonotonic = (b1 <=_u reqBase2) & (reqTop2 <=_u t1);
    let resultMonotonic = (b1 <=_u b2) & (t2 <=_u t1);
    (saneTop1 & requestMonotonic) --> resultMonotonic
}

$property
/*!
 * THIS checks monotonicity preservation of [setCapBounds] when applied to the 
 * root capability bounds. This is almost trivially true but since
 * [prop_setbounds_monotonic] is really an inductive proof it needs a base case 
 * so we'd better check it.
 */
function prop_setbounds_monotonic_root(
        reqBase1 : CapAddrBits, reqLen1 : CapAddrBits) -> bool = {
    let (exact, c) = setCapBounds(root_cap_mem, reqBase1, reqLen1);
    let (base, top) = getCapBoundsBits(c);
    let reqTop1 = (0b0 @ reqBase1) + (0b0 @ reqLen1);
    let saneTop1 = reqTop1 <=_u 0b1@0x00000000;
    let resultMonotonic = (base >=_u 0x00000000) & (top <=_u 0b1@0x00000000);
    saneTop1 --> resultMonotonic
}

$property
/*!
 * THIS checks that [setCapBounds] returns the most precise encodable bounds
 * that satisfy the requested bounds. Although not strictly required it is nice
 * to have and turns out to be quite useful for the monotonicity property.
 */
function prop_setbounds_precise(reqBase1 : CapAddrBits, reqLen1 : CapAddrBits,
        c2 : CapBits) -> bool = {
    let (exact, c1) = setCapBounds(root_cap_mem, reqBase1, reqLen1);
    let (b1, t1) = getCapBoundsBits(c1);
    let reqTop1 = (0b0 @ reqBase1) + (0b0 @ reqLen1);
    let saneTop1 = reqTop1 <=_u 0b1@0x00000000;
    let (b2, t2) = getCapBoundsBits(capBitsToCapability(false, c2));
    let validBase = b2 <=_u reqBase1;
    let betterBase = b1 <_u b2;
    let validTop = reqTop1 <=_u t2;
    let betterTop =  t2 <_u t1;
    (saneTop1) --> not(validBase & betterBase & validTop & betterTop)
}

$property
/*!
 * THIS checks that the flag returned by [setCapAddr] is sound with respect to the
 * definition of representability i.e. if it returns `representable' then the
 * bounds remain unchanged. Note that a conservative implementation of the
 * representability check may return false even though the bounds are unchanged,
 * so the converse does not necessarily hold.
 */
function prop_setaddr(reqBase : CapAddrBits, reqLen : CapAddrBits, newAddr : CapAddrBits) -> bool = {
    let (exact, c) = setCapBounds(root_cap_mem, reqBase, reqLen);
    let (representable, newCap) = setCapAddr(c, newAddr);
    let boundsEqual = capBoundsEqual(c, newCap);
    representable <--> boundsEqual
}

$property
/*!
 * THIS checks the representable bounds match the minimum guarantee of the C language
 * i.e. base..one past the end.
 */
function prop_repbounds_c(reqBase : CapAddrBits, reqLen : CapAddrBits, newAddr : CapAddrBits) -> bool = {
    let (exact, c) = setCapBounds(root_cap_mem, reqBase, reqLen);
    let reqTop = (0b0 @ reqBase) + (0b0 @ reqLen);
    let saneTop = reqTop <=_u 0b1@0x00000000;
    let (b, t) = getCapBoundsBits(c);
    let (representable, newCap) = setCapAddr(c, newAddr);
    let inCBounds = (b <=_u newAddr) & ((0b0 @ newAddr) <=_u t);
    (saneTop & inCBounds) --> representable
}

$property
/*!
 * THIS checks the representable bounds match expectations from the encoding,
 * namely $[b, b + 2^{e+9})$.
 */
function prop_repbounds(reqBase : CapAddrBits, reqLen : CapAddrBits, newAddr : CapAddrBits) -> bool = {
    let (exact, c) = setCapBounds(root_cap_mem, reqBase, reqLen);
    let reqTop = (0b0 @ reqBase) + (0b0 @ reqLen);
    let saneTop = reqTop <=_u 0b1@0x00000000;
    let (b, t) = getCapBoundsBits(c);
    let (representable, newCap) = setCapAddr(c, newAddr);
    let repTop = (0b0 @ b) + ((to_bits(33,1) << unsigned(c.E)) << 9);
    /* The representable bounds check: either E is max or address is in range */
    let inRepBounds = c.E == cap_max_E_bits | ((b <=_u newAddr) & ((0b0 @ newAddr) <_u repTop));
    /* For any sane capability the inRepBounds check matches the flag returned 
       by setCapAddr () */
    saneTop --> (inRepBounds <--> representable)
}

$property
/*!
 * THIS checks that the [CRRL] and [CRAM] instructions can be used to derive a
 * representable base and length for given requested base and length. Note that
 * CRRL returns zero for non-zero `reqLen` in the case of rounding up to the max
 * length.
 */
function prop_crrl_cram(reqBase : CapAddrBits, reqLen : CapAddrBits) -> bool = {
    let mask = getRepresentableAlignmentMask(reqLen);
    let reqTop = (0b0 @ reqBase) + (0b0 @ reqLen);
    let saneTop = reqTop <=_u 0b1@0x00000000;
    let newBase = reqBase & mask;
    let newLen = getRepresentableLength(reqLen);
    let (exact, c) = setCapBounds(root_cap_mem, newBase, newLen);
    (saneTop & ((reqLen == zeros()) | (newLen != zeros())))--> 
    (exact & reqLen <=_u newLen)
}

$property
/*!
 * THIS property tests if it matters whether the length is rounded with CRRL
 * before using CRAM. The answer is that it does not matter except in the case
 * where CRRL returns zero as a result of overflow, which needs to be dealt with
 * as a special case anyway.
 */
function prop_crrl_cram_usage(reqLen : CapAddrBits) -> bool = {
    let newLen = getRepresentableLength(reqLen);
    let mask = getRepresentableAlignmentMask(newLen);
    let mask2 = getRepresentableAlignmentMask(reqLen);
    ((reqLen == zeros()) | (newLen != zeros())) --> (mask == mask2)
}