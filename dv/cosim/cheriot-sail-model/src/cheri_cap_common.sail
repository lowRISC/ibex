/*=======================================================================================*/
/*  CHERI RISCV Sail Model                                                               */
/*                                                                                       */
/*  This CHERI Sail RISC-V architecture model here, comprising all files and             */
/*  directories except for the snapshots of the Lem and Sail libraries in the            */
/*  prover_snapshots directory (which include copies of their licenses), is subject      */
/*  to the BSD two-clause licence below.                                                 */
/*                                                                                       */
/*  Copyright (c) 2017-2021                                                              */
/*    Alasdair Armstrong                                                                 */
/*    Thomas Bauereiss                                                                   */
/*    Brian Campbell                                                                     */
/*    Jessica Clarke                                                                     */
/*    Nathaniel Wesley Filardo (contributions prior to July 2020, thereafter Microsoft)  */
/*    Alexandre Joannou                                                                  */
/*    Microsoft                                                                          */
/*    Prashanth Mundkur                                                                  */
/*    Robert Norton-Wright (contributions prior to March 2020, thereafter Microsoft)     */
/*    Alexander Richardson                                                               */
/*    Peter Rugg                                                                         */
/*    Peter Sewell                                                                       */
/*                                                                                       */
/*  All rights reserved.                                                                 */
/*                                                                                       */
/*  This software was developed by SRI International and the University of               */
/*  Cambridge Computer Laboratory (Department of Computer Science and                    */
/*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and                 */
/*  under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA                 */
/*  SSITH research programme.                                                            */
/*                                                                                       */
/*  This software was developed within the Rigorous Engineering of                       */
/*  Mainstream Systems (REMS) project, partly funded by EPSRC grant                      */
/*  EP/K008528/1, at the Universities of Cambridge and Edinburgh.                        */
/*                                                                                       */
/*  This project has received funding from the European Research Council                 */
/*  (ERC) under the European Union’s Horizon 2020 research and innovation                */
/*  programme (grant agreement 789108, ELVER).                                           */
/*                                                                                       */
/*  Redistribution and use in source and binary forms, with or without                   */
/*  modification, are permitted provided that the following conditions                   */
/*  are met:                                                                             */
/*  1. Redistributions of source code must retain the above copyright                    */
/*     notice, this list of conditions and the following disclaimer.                     */
/*  2. Redistributions in binary form must reproduce the above copyright                 */
/*     notice, this list of conditions and the following disclaimer in                   */
/*     the documentation and/or other materials provided with the                        */
/*     distribution.                                                                     */
/*                                                                                       */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''                   */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED                    */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A                      */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR                  */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,                         */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT                     */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF                     */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND                  */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,                   */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT                   */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF                   */
/*  SUCH DAMAGE.                                                                         */
/*=======================================================================================*/

/* width of capability in bytes (excluding tag) */
type cap_size : Int = 8
let  cap_size = sizeof(cap_size)
type log2_cap_size : Int = 3
let  log2_cap_size = sizeof(log2_cap_size)
type CapBits = bits(8 * cap_size)
/*! Width of compressed perms field in bits */
type cap_cperms_width : Int = 6

/*! Width of architectural otype field in bits */
type cap_otype_width : Int = 4
let  cap_otype_width = sizeof(cap_otype_width)
/*! Width of compressed otype field in bits */
type cap_cotype_width : Int = 3
/*! Width of T and B field in bits */
type cap_mantissa_width : Int = 9
let  cap_mantissa_width = sizeof(cap_mantissa_width)
/*! Width of expanded exponent field in bits */
type cap_E_width : Int = 5
let  cap_E_width = sizeof(cap_E_width)
/*! Width of compressed exponent field in bits */
type cap_cE_width : Int = 4
type cap_addr_width : Int = xlen
let  cap_addr_width = sizeof(cap_addr_width)
/*! Cap length width is one larger than address space width in order to 
 represent maximum top / length of 2**xlen. */
type cap_len_width : Int = cap_addr_width + 1
let  cap_len_width = sizeof(cap_len_width)

/*!
 * There is one revocation bit for every 8 bytes.
 */
type log2_revocation_granule_size : Int = 3
let  log2_revocation_granule_size = sizeof(log2_revocation_granule_size)

/*! THIS represents capabilities as stored in memory. */
struct EncCapability = {
  reserved   : bits(1),
  cperms     : bits(cap_cperms_width),
  cotype     : bits(cap_cotype_width),
  cE         : bits(cap_cE_width),
  T          : bits(cap_mantissa_width),
  B          : bits(cap_mantissa_width),
  address    : bits(cap_addr_width)
}

function capBitsToEncCapability(c) : CapBits -> EncCapability = struct {
  reserved   = c[63..63],
  cperms     = c[62..57],
  cotype     = c[56..54],
  cE         = c[53..50],
  T          = c[49..41],
  B          = c[40..32],
  address    = c[31..0]
}

function encCapToBits(cap) : EncCapability -> CapBits =
  cap.reserved @
  cap.cperms @
  cap.cotype @
  cap.cE @
  cap.T @
  cap.B @
  cap.address

let cap_max_addr = MAX(cap_addr_width)
let cap_max_otype = MAX(cap_otype_width)

/*! Width of the architectural perms returned by CGetPerms. */
type cap_perms_width : Int = 12
let  cap_perms_width = sizeof(cap_perms_width)

type CapAddrBits  = bits(cap_addr_width)
type CapAddrInt   = range(0, (2 ^ cap_addr_width) - 1)
type CapLenBits   = bits(cap_len_width)
type CapLen       = range(0, (2 ^ cap_len_width) - 1)
type CapPermsBits = bits(cap_perms_width)

/*! Exponent chosen to permit representing the entire address space. */
type cap_max_E : Int = 24
let cap_max_E = sizeof(cap_max_E)
let cap_max_E_bits = to_bits(cap_E_width, sizeof(cap_max_E))
/* Value for T field that represents max value of top (2**32) when used with cap_max_E. */
let cap_reset_T = 0b1 @ zeros(cap_mantissa_width - 1)

/*!
 * THIS represents a partially decompressed capability. The
 * permissions, E and otype are expanded from their compressed format by
 * [encCapabilityToCapability] and compressed by [capToEncCap].
 */
struct Capability = {
  tag                    : bool,
  perm_user0             : bool,
  permit_seal            : bool,
  permit_unseal          : bool,
  permit_execute         : bool,
  access_system_regs     : bool,
  permit_load_store_cap  : bool,
  permit_load            : bool,
  permit_store_local_cap : bool,
  permit_load_mutable    : bool,
  permit_store           : bool,
  permit_load_global     : bool,
  global                 : bool,
  reserved               : bits(1),
  E                      : bits(cap_E_width),
  B                      : bits(cap_mantissa_width),
  T                      : bits(cap_mantissa_width),
  otype                  : bits(cap_otype_width),
  address                : bits(cap_addr_width)
}

/* The null capability is defined as all zeros, with tag unset. */
let null_cap : Capability = struct {
  tag                    = false,
  perm_user0             = false,
  permit_seal            = false,
  permit_unseal          = false,
  permit_execute         = false,
  access_system_regs     = false,
  permit_load_store_cap  = false,
  permit_load            = false,
  permit_store_local_cap = false,
  permit_load_mutable    = false,
  permit_store           = false,
  permit_load_global     = false,
  global                 = false,
  reserved               = zeros(),
  B                      = zeros(),
  T                      = zeros(),
  E                      = zeros(),
  otype                  = to_bits(cap_otype_width, otype_unsealed),
  address                = zeros()
}

/* A capability from which to derive the root caps. E and T are set such that 
  the bounds decode to the entire address space, and tag and global are set.
  These things are are common to all root caps. For convenience it is derived 
  from null_cap. */
let max_bounds_cap : Capability = {
  null_cap with
  E                      = cap_max_E_bits,
  T                      = cap_reset_T,
  tag                    = true,
  global                 = true
}

/* The capability root for executable format capabilities. */
let root_cap_exe : Capability = {
  max_bounds_cap with
  permit_execute         = true,
  access_system_regs     = true,
  permit_load_store_cap  = true,
  permit_load            = true,
  permit_load_mutable    = true,
  permit_load_global     = true,
  address                = 0x80000000 // match cheriot-ibex sram base & trap address
}

/* The capability root for memory format capabilities. */
let root_cap_mem : Capability = {
  max_bounds_cap with
  permit_load_store_cap  = true,
  permit_load            = true,
  permit_store_local_cap = true,
  permit_load_mutable    = true,
  permit_store           = true,
  permit_load_global     = true
}

/* The capability root for sealing format capabilities. */
let root_cap_seal : Capability = {
  max_bounds_cap with
  perm_user0             = true,
  permit_seal            = true,
  permit_unseal          = true
}

/*! Partially decompress a capability from bits to a [Capability] struct.
  Permissions, otype and exponent are decompressed, but the bounds are left
  in the form of B and T fields. */
function encCapabilityToCapability(t,c) : (bool, EncCapability) -> Capability = {
  var perm_user0             : bool = false;
  var permit_seal            : bool = false;
  var permit_unseal          : bool = false;
  var permit_execute         : bool = false;
  var access_system_regs     : bool = false;
  var permit_load_store_cap  : bool = false;
  var permit_load            : bool = false;
  var permit_store_local_cap : bool = false;
  var permit_load_mutable    : bool = false;
  var permit_store           : bool = false;
  var permit_load_global     : bool = false;
  var global                 : bool = bit_to_bool(c.cperms[5]);
  var isExe : bool = false;
  match c.cperms[4..0] {
    0b11 @ [SL, LM, LG] => {
      /* mem-rw-cap format */
      permit_load = true;
      permit_load_store_cap = true;
      permit_store = true;
      permit_store_local_cap = bit_to_bool(SL);
      permit_load_mutable = bit_to_bool(LM);
      permit_load_global = bit_to_bool(LG);
    },
    0b101 @ [LM, LG] => {
      /* mem-ro-cap format */
      permit_load = true;
      permit_load_store_cap = true;
      permit_load_mutable = bit_to_bool(LM);
      permit_load_global = bit_to_bool(LG);
    },
    0b10000 => {
      /* mem-wo-cap */
      permit_store = true;
      permit_load_store_cap = true;
    },
    0b100 @ [LD, SD] => {
      /* mem-data */
      permit_load = bit_to_bool(LD);
      permit_store = bit_to_bool(SD);
    },
    0b01 @ [SR, LM, LG] => {
      /* Executable format */
      isExe = true;
      permit_execute = true;
      permit_load = true;
      permit_load_store_cap = true;
      access_system_regs  = bit_to_bool(SR);
      permit_load_mutable = bit_to_bool(LM);
      permit_load_global  = bit_to_bool(LG);
    },
    0b00 @ [U0, SE, US] => {
      /* Sealing format */
      perm_user0    = bit_to_bool(U0);
      permit_seal   = bit_to_bool(SE);
      permit_unseal = bit_to_bool(US);
    }
  };
  /* The otype of executable caps is mapped to 1-7 and others to 9-15. Unsealed
    is always 0. */
  let otype = (if isExe | c.cotype == 0b000 then 0b0 else 0b1) @ c.cotype;
  /* The 4-bit exponent is expanded to 5 bits, using 0xf to encode a cap_max_E
    value that enables representing the entire address space. */
  let E = if c.cE == 0xf then cap_max_E_bits else zero_extend(c.cE);
  return struct {
    tag                    = t,
    perm_user0             = perm_user0            ,
    permit_seal            = permit_seal           ,
    permit_unseal          = permit_unseal         ,
    permit_execute         = permit_execute        ,
    access_system_regs     = access_system_regs    ,
    permit_load_store_cap  = permit_load_store_cap ,
    permit_load            = permit_load           ,
    permit_store_local_cap = permit_store_local_cap,
    permit_load_mutable    = permit_load_mutable   ,
    permit_store           = permit_store          ,
    permit_load_global     = permit_load_global    ,
    global                 = global                ,
    reserved               = c.reserved,
    E                      = E,
    B                      = c.B,
    T                      = c.T,
    otype                  = otype,
    address                = c.address
  }
}

function capBitsToCapability(t, c) : (bool, CapBits) -> Capability = encCapabilityToCapability(t, capBitsToEncCapability(c))

/*!
 * Compress a [Capability] back to the bits representation. This is simply
 * the reverse of [encCapabilityToCapability], although it relies on the fields
 * having valid values. In particular E must be either cap_max_E or less than 15,
 * and otype is either 0 (unsealed) or in the correct range for the capability format.
 * Both of these will be true for things returned by [encCapabilityToCapability].
 * [CSetBounds] ensures a sensible value for E and nothing else sets it. For the
 * otype we rely on the fact that sealed capabilities cannot be modified and
 * unsealed is always encoded as zero. It is mildy surprsing that [CAndPerm] on
 * a sealed capability may result in a untagged capability with a different
 * otype, but otypes have no significance on untagged capabilities anyway.
 */
function capToEncCap(cap) : Capability -> EncCapability = {
  var cperms : bits(cap_cperms_width) = zeros();
  cperms[5] = bool_to_bit(cap.global);
  if cap.permit_execute & cap.permit_load & cap.permit_load_store_cap then {
    /* Executable format */
    cperms[4..3] = 0b01;
    cperms[2] = bool_to_bit(cap.access_system_regs);
    cperms[1] = bool_to_bit(cap.permit_load_mutable);
    cperms[0] = bool_to_bit(cap.permit_load_global);
  } else if cap.permit_load & cap.permit_load_store_cap & cap.permit_store then {
    /* mem cap-rw */
    cperms[4..3] = 0b11;
    cperms[2] = bool_to_bit(cap.permit_store_local_cap);
    cperms[1] = bool_to_bit(cap.permit_load_mutable);
    cperms[0] = bool_to_bit(cap.permit_load_global);
  } else if cap.permit_load & cap.permit_load_store_cap then {
    /* mem cap-ro */
    cperms[4..2] = 0b101;
    cperms[1] = bool_to_bit(cap.permit_load_mutable);
    cperms[0] = bool_to_bit(cap.permit_load_global);
  } else if cap.permit_store & cap.permit_load_store_cap then {
    /* mem cap-wo */
    cperms[4..0] = 0b10000;
  } else if cap.permit_load | cap.permit_store then {
    /* mem rw data */
    cperms[4..2] = 0b100;
    cperms[1] = bool_to_bit(cap.permit_load);
    cperms[0] = bool_to_bit(cap.permit_store);
  } else {
    /* Sealing format */
    cperms[4..3] = 0b00;
    cperms[2] = bool_to_bit(cap.perm_user0);
    cperms[1] = bool_to_bit(cap.permit_seal);
    cperms[0] = bool_to_bit(cap.permit_unseal);
  };
  return struct {
    cperms = cperms,
    reserved = cap.reserved,
    cotype = cap.otype[2..0], /* truncate otype when compressing */
    cE = if cap.E == cap_max_E_bits then 0xf else cap.E[3..0],
    T = cap.T,
    B = cap.B,
    address = cap.address
  };
}

/*! Convert from capability struct to bits (no tag) */
function capToBits(cap) : Capability -> CapBits = encCapToBits(capToEncCap(cap))

let null_cap_bits : CapBits = capToBits(null_cap)

/*!
 * Returns the decoded base and top of the given Capability.
 */
function getCapBoundsBits(c) : Capability -> (CapAddrBits, CapLenBits) = {
  let E = unsigned(c.E);
  let a : CapAddrBits = c.address;
  /* Calculate corrections for upper bits of base and top based on relative 
     positions of base, top and address with respect to 
     2**(E+cap_mantissa_width) aligned regions */
  let a_mid = truncate(a >> E, cap_mantissa_width);
  /* If a_mid is less than B then a must be in region above base */
  let a_hi = if a_mid <_u c.B then 1 else 0;
  /* If T is less than B then top must be in region above base */
  let t_hi = if c.T <_u c.B then 1 else 0;
  /* If address is in region above base then we need to subtract one from a_top
    to get top bits of base */
  let c_b = 0 - a_hi;
  /* The correction for top can be -1, 0, or 1 depending on whether a and t lie
    in the same region and, if not, which is in the high region. This boils down
    to a subtraction. */
  let c_t = t_hi - a_hi;
  let a_top = a >> (E + cap_mantissa_width);
  /* Finally reconstruct the base and top using the corrections and truncate. */
  let base : CapAddrBits = truncate((a_top + c_b) @ c.B @ zeros(E), cap_addr_width);
  let top : CapLenBits  = truncate((a_top + c_t) @ c.T @ zeros(E), cap_len_width);
  (base, top)
}
// XXX Not sure whether we need something like this.
// /* If the base and top are more than an address space away from each other,
//    invert the MSB of top.  This corrects for errors that happen when the
//    representable space wraps the address space. */
// let base2 : bits(2) = 0b0 @ [base[cap_addr_width - 1]];
// let top2  : bits(2) = top[cap_addr_width .. cap_addr_width - 1];
// if (E < (cap_max_E - 1)) & (unsigned(top2 - base2) > 1) then {
//   top[cap_addr_width] = ~(top[cap_addr_width]);
// };

function getCapBounds(cap) : Capability -> (CapAddrInt, CapLen) =
  let (base : CapAddrBits, top : CapLenBits) = getCapBoundsBits(cap) in
  (unsigned(base), unsigned(top))

/*!
 * Returns cap with E, B and T set such that the decoded bounds include the
 * region specified by base and length. If the region is not precisely
 * representable the base may be rounded down and the length up. Also returns a
 * boolean indicating whether the bounds are precisely representable, and sets
 * the address of the returned capability to the requested base.
 */
function setCapBounds(cap, base, length) : (Capability, CapAddrBits, CapAddrBits) -> (bool, Capability) = {
  let ext_base = 0b0 @ base;
  /* Compute new top, note extra bit in case of overflow */
  let top : CapLenBits = ext_base + (0b0 @ length);
  /* Find smallest exponent that can represent required length.
   */
  let e : range(0, 23) = 23 - count_leading_zeros(truncateLSB(length, 23));
  /* Saturate e at max if it exceeds representable 4-bit value. */
  var e_sat : range(0,  cap_max_E) = if e > 14 then cap_max_E else e;
  /* Extract B and T bits from base and top, include a spare bit so that we can
   check for length overflow below. */
  var B = truncate(base >> e_sat, cap_mantissa_width + 1);
  var T = truncate(top >> e_sat, cap_mantissa_width + 1);
  /* Work out whether we have lost significant bits in top */
  var maskLo : CapLenBits = zero_extend(ones(e_sat));
  lostSignificantTop  = unsigned(top & maskLo) != 0;
  if lostSignificantTop then {
    /* we must increment T to make sure it is still above top even with lost bits */
    T = T + 1;
  };

  /* If the resulting length is greater than maximum possible, we must
     increment e by one and try again. This time overflow is impossible. */
  if  0b0111111111 <_u (T - B) then {
    if e_sat < 14 then {
      /* increment e_sat by one, note that min is only necessary to satisfy the
         Sail type checker */
      e_sat = min(e_sat + 1, cap_max_E);
    } else {
      e_sat = cap_max_E;
    };
    /* Recompute B, T, mask etc for new e_sat */
    B = truncate(base >> e_sat, cap_mantissa_width + 1);
    T = truncate(top >> e_sat, cap_mantissa_width + 1);
    maskLo = zero_extend(ones(e_sat));
    lostSignificantTop  = unsigned(top & maskLo) != 0;
    if lostSignificantTop then  {
      T = T + 1;
    };
  };
  /* Return cap with new bounds */
  let encE = to_bits(cap_E_width, e_sat);
  let newCap = {cap with address=base, E=encE, B=truncate(B, cap_mantissa_width), T=truncate(T, cap_mantissa_width)};
  lostSignificantBase = unsigned(ext_base & maskLo) != 0;
  let exact = not(lostSignificantBase | lostSignificantTop);
  (exact, newCap)
}

/* count_trailing_zeros is a Sail builtin in Sail >=0.20; add it here for Sail 0.19 compat */
val count_trailing_zeros : forall 'N, 'N >=0 . bits('N) -> range(0, 'N)
function count_trailing_zeros(bv) = {
  foreach(i from 0 to ('N - 1) by 1 in inc) {
    if bv[i] == bitone then {
      return i;
    }
  };
  'N
}

/*!
 * Returns cap with the address and base set to the given base (exactly) and the
 * length set to the largest value less than or equal to given length that can
 * be represented while preserving the alignment of the base.
 */
function setCapBoundsRoundDown(cap, base, length) : (Capability, CapAddrBits, CapAddrBits) -> Capability = {
  let ext_base = 0b0 @ base;
  /* Compute new top, note extra bit in case of overflow */
  let top : CapLenBits = ext_base + (0b0 @ length);
  /* Find smallest exponent that can represent required length. */
  let e_l : range(0, 23) = 23 - count_leading_zeros(truncateLSB(length, 23));
  /* e_l = floor(log2 length), i.e. e_l is such that
   * if length <= 2^9, then e_l = 0
   * if length >  2^9, then e_l = x such that 2^x > floor(length/2^9) >= 2^(x-1)
   *    In this case, the following properties of length and e_l hold (proofs left as exercise):
   *     - e_l > 0
   *     - 2^8 <= floor(length/2^e_l) < 2^9
   *     - forall x > e_l, floor(length/2^x) < 2^8
   *     - forall x < e_l, floor(length/2^x) >= 2^9
   *    This means e_l is the value such that floor(length/2^e_l) is a 9-bit value with MSB set.
   *    Any change to e_l would violate this statement.
   *    Given a requested length, the closest we can reach is floor(length/2^e_l)*2^e_l.
   * Note that we also have the following properties:
   * if e_l = 0, then length <= 2^9
   * if e_l > 0, then length >  2^9
   * Note also that for any x, floor(length/2^x)*2^x <= length. In particular, this holds true when x = 2^e_l.
   */
  /* What is the required alignment of base? */
  let e_b = count_trailing_zeros(base);
  /* base = b * 2^e_b, such that e_b cannot be bigger.
   * For any x <= e_b, base can be written as (b * 2^(e_b-x)) * 2^x, in which case B = truncate(b * 2^(e_b-x), cap_mantissa_width).
   */

  /*
   * We're going to return something below the "band gap" in the encoding, so
   * find the largest exponent that's: below the band gap, less than or equal to
   * what's required by the length (e), and less than or equal to what's
   * required by the base (e_b).
   */
  let E = min(14, min(e_l, e_b));

  /* If e_l gets chosen as E, then the output length will be exactly floor(length/2^e_l) * 2^e_l
   *    This is true even if e_l = 0, and this output length is less than 2^9 as discussed in the properties above.
   * If e_l is not chosen as E, then E < e_l, and the closest length we can get is final_length = floor(length/2^E)*2^E.
   *    Using the property forall x < e_l, floor(length/2^x) >= 2^9, the mantissa portion of final_length will exceed 9 bits.
   */

  /* Extract B for this E */
  let B = truncate(base >> E, cap_mantissa_width);

  let T = if (e_l > e_b) | (e_l > 14) then {
    /*
     * Base unrepresentable using chosen e_l or length over long; choose a
     * smaller exponent, E, and make a maximum length capability for that.
     * This is the case when e_l is not chosen as E and so final_length exceeds 9 bits.
     * So, we make final_length's mantissa the maximum allowed, namely 2^9-1.
     * (Note that when T = B-1, mantissa portion of length is 2^9-1.)
     */
    B - 1;
  } else {
    /* Extract T for E as is */
    truncate(top >> e_l, cap_mantissa_width)
  };

  /* Return the cap with new bounds and address */
  {cap with address=base, E=to_bits(cap_E_width, E), B=B, T=T}
}

function getCapPerms(cap) : Capability -> CapPermsBits = [
  bool_to_bit(cap.perm_user0),
  bool_to_bit(cap.permit_seal),
  bool_to_bit(cap.permit_unseal),
  bool_to_bit(cap.permit_execute),
  bool_to_bit(cap.access_system_regs),
  bool_to_bit(cap.permit_load_store_cap),
  bool_to_bit(cap.permit_load),
  bool_to_bit(cap.permit_store_local_cap),
  bool_to_bit(cap.permit_load_mutable),
  bool_to_bit(cap.permit_store),
  bool_to_bit(cap.permit_load_global),
  bool_to_bit(cap.global)
]

 function setCapPerms(cap, perms) : (Capability, CapPermsBits) -> Capability =
  { cap with
    perm_user0             = bit_to_bool(perms[11]),
    permit_seal            = bit_to_bool(perms[10]),
    permit_unseal          = bit_to_bool(perms[9]),
    permit_execute         = bit_to_bool(perms[8]),
    access_system_regs     = bit_to_bool(perms[7]),
    permit_load_store_cap  = bit_to_bool(perms[6]),
    permit_load            = bit_to_bool(perms[5]),
    permit_store_local_cap = bit_to_bool(perms[4]),
    permit_load_mutable    = bit_to_bool(perms[3]),
    permit_store           = bit_to_bool(perms[2]),
    permit_load_global     = bit_to_bool(perms[1]),
    global                 = bit_to_bool(perms[0])
  }

/*!
 * Returns whether the given capability is sealed i.e. whether its otype is zero.
 */
val isCapSealed : Capability -> bool
function isCapSealed(cap) = signed(cap.otype) != otype_unsealed

/*!
 * Returns true if the given capability has one of the sentry otypes, otherwise false.
 */
val isCapSentry : Capability -> bool
function isCapSentry(cap) =
  match unsigned(cap.otype) {
    otype if otype == otype_sentry     => true,
    otype if otype == otype_sentry_id  => true,
    otype if otype == otype_sentry_ie  => true,
    otype if otype == otype_sentry_bid => true,
    otype if otype == otype_sentry_bie => true,
    _  => false
  }

/*!
 * Returns true if the given capability has one of the forward sentry otypes, otherwise false.
 */
val isCapForwardSentry : Capability -> bool
function isCapForwardSentry(cap) =
  match unsigned(cap.otype) {
    otype if otype == otype_sentry    => true,
    otype if otype == otype_sentry_id => true,
    otype if otype == otype_sentry_ie => true,
    _  => false
  }

/*!
 * Returns true if the given capability has one of the forward interrupt-control sentry otypes, otherwise false.
 */
val isCapForwardControlSentry : Capability -> bool
function isCapForwardControlSentry(cap) =
  match unsigned(cap.otype) {
    otype if otype == otype_sentry_id => true,
    otype if otype == otype_sentry_ie => true,
    _  => false
  }

/*!
 * Returns true if the given capability has one of the backward sentry otypes, otherwise false.
 */
val isCapBackwardSentry : Capability -> bool
function isCapBackwardSentry(cap) =
  match unsigned(cap.otype) {
    otype if otype == otype_sentry_bid => true,
    otype if otype == otype_sentry_bie => true,
    _  => false
  }

/*!
 * Returns true if the given capability has one of the forward interrupt-inherited sentry otype, otherwise false.
 */
val isCapForwardInheritSentry : Capability -> bool
function isCapForwardInheritSentry(cap) =
  match unsigned(cap.otype) {
    otype if otype == otype_sentry => true,
    _  => false
  }

function sealCap(cap, otyp) : (Capability, bits(cap_otype_width)) -> Capability =
    {cap with otype=otyp}

function unsealCap(cap) : Capability -> Capability =
    {cap with otype=to_bits(cap_otype_width, otype_unsealed)}

function getCapBaseBits(c) : Capability -> CapAddrBits =
    let (base, _) = getCapBoundsBits(c) in
    base

function getCapBase(c) : Capability -> CapAddrInt =
    unsigned(getCapBaseBits(c))

function getCapTopBits(c) : Capability -> CapLenBits =
    let (_, top) = getCapBoundsBits(c) in
    top

function getCapTop (c) : Capability -> CapLen =
    unsigned(getCapTopBits(c))

function getCapOffsetBits(c) : Capability -> CapAddrBits =
    let base : CapAddrBits = getCapBaseBits(c) in
    c.address - base

function getCapOffset(c) : Capability -> CapAddrInt =
    unsigned(getCapOffsetBits(c))

function getCapLength(c) : Capability -> CapLen =
    let ('base, 'top) = getCapBounds(c) in {
        /* For valid capabilties we expect top >= base and hence
         * length >= 0 but representation does allow top < base in some
         * cases so might encounter on untagged capabilities. Here we just
         * pretend it is a 65-bit quantitiy and wrap.
         */
        assert (not(c.tag) | top >= base);
        (top - base) % pow2(cap_len_width)
    }

/*!
 * THIS(cap, addr, len) checks whether the capability cap includes the region
 * specified by addr and len. Specifically it checks whether
 * cap.base $\le$ addr AND addr + len $\le$ cap.top. Note that this definition
 * returns true if len is zero and addr $=$ cap.top.
 */
val inCapBounds  : (Capability, CapAddrBits, CapLen) -> bool
function inCapBounds (cap, addr, size) = {
  let (base, top) = getCapBounds(cap);
  let a = unsigned(addr);
  (a >= base) & ((a + size) <= top)
}

function int_to_cap (offset) : CapAddrBits -> Capability =
    {null_cap with address = offset}

/*!
 * Returns the given capability with the tag cleared if the second argument is
 * true, otherwise returns it with the original tag value preserved.
 */
val clearTagIf : (Capability, bool) -> Capability
function clearTagIf(cap, cond) =
    {cap with tag = cap.tag & not(cond)}

/*!
 * Returns the given capability with the tag cleared if the capability
 * is sealed, otherwise returns it with the original tag value preserved.
 */
val clearTagIfSealed : Capability -> Capability
function clearTagIfSealed(cap) : Capability -> Capability =
    clearTagIf(cap, isCapSealed(cap))

/*!
 * Returns the given capability with the tag set to false.
 */
val clearTag : Capability -> Capability
function clearTag(cap) : Capability -> Capability =
    clearTagIf(cap, true)

function capBoundsEqual (c1, c2) : (Capability, Capability) -> bool =
    let (base1, top1) = getCapBounds(c1) in
    let (base2, top2) = getCapBounds(c2) in
    (base1 == base2) & (top1 == top2)

/*!
 * Returns the given capability with the address set to the given value and a boolean
 * indicating whether the new address is within representable range (decoded
 * bounds remain the same).
 */
val setCapAddr : (Capability, CapAddrBits) -> (bool, Capability)
function setCapAddr(c, addr) =
    let newCap = { c with address = addr } in
    let representable = capBoundsEqual(c, newCap) in
    (representable, newCap)

/*!
 * Returns the given capability with the address set to given value. If the new
 * address is not in the representable range or the capability is sealed then
 * the tag is cleared.
 */
val setCapAddrChecked : (Capability, CapAddrBits) -> Capability
function setCapAddrChecked (cap, addr) =
    let (representable, newCap) = setCapAddr(cap, addr) in
    clearTagIf(newCap, not(representable) | isCapSealed(cap))

infix 1 >>_s
overload operator >> = {sail_shiftright}
overload operator << = {sail_shiftleft}
overload operator >>_s = {sail_arith_shiftright}

// function fastRepCheck(c, i) : (Capability, CapAddrBits) -> bool=
//     let E = unsigned(c.E) in
//     if (E >= cap_max_E - 2) then
//         true /* in this case representable region is whole address space */
//     else
//         let i_top    = signed(i >>_s (E + cap_mantissa_width)) in
//         let i_mid    = truncate(i >> E, cap_mantissa_width)in
//         let a_mid    = truncate(c.address >> E, cap_mantissa_width) in
//         let B3 = truncateLSB(c.B, 3) in
//         let R3 = B3 - 0b001 in
//         let R  = R3 @ zeros(cap_mantissa_width - 3) in
//         let diff  = R - a_mid in
//         let diff1 = diff - 1 in
//         /* i_top determines 1. whether the increment is inRange
//            i.e. less than the size of the representable region
//            (2**(E+MW)) and 2. whether it is positive or negative. To
//            satisfy 1. all top bits must be the same so we are
//            interested in the cases i_top is 0 or -1 */
//         if (i_top == 0) then
//           i_mid <_u diff1
//         else if (i_top == -1) then
//           (i_mid >=_u diff) & (R != a_mid)
//         else
//           false

function setCapOffset(c, offset) : (Capability, CapAddrBits) -> (bool, Capability) =
    let base = getCapBaseBits(c) in
    let newAddress = base + offset in
    let newCap     = { c with address = newAddress } in
    let representable = capBoundsEqual(c, newCap) in
    /* let representable = fastRepCheck(c, (newAddress - c.address)) in */
    (representable, newCap)

function setCapOffsetChecked (cap, offset) : (Capability, CapAddrBits) -> Capability =
    let (representable, newCap) = setCapOffset(cap, offset) in
    clearTagIf(newCap, not(representable) | isCapSealed(cap))

/*!
 * Returns the given capability with the address incremented by the given value 
 * and a boolean indicating whether the new address is within representable 
 * range (decoded bounds remain the same).
 */
val incCapAddr : (Capability, CapAddrBits) -> (bool, Capability)
function incCapAddr(c, delta) =
    let newAddress : CapAddrBits = c.address + delta in
    let newCap     = { c with address = newAddress } in
    let representable = capBoundsEqual(c, newCap) in
    /* let representable = fastRepCheck(c, delta) in */
    (representable, newCap)


val capToString : (Capability) -> string
function capToString (cap) = {
  let len = getCapLength(cap);
  let len_str = BitStr(to_bits(cap_len_width + 3, len));
  let (base, top) = getCapBoundsBits(cap);
  let top_str = BitStr(0b000 @ top);
  BitStr(cap.address)
    ^ " (v:" ^ (if cap.tag then "1 " else "0 ")
    ^ BitStr(base) ^ "-" ^ top_str
    ^ " l:" ^ len_str
    ^ " o:" ^ BitStr(cap.otype)
    ^ " p:"
    ^ (if cap.global then "G " else "- ")
    ^ (if cap.permit_load then "R" else "-")
    ^ (if cap.permit_store then "W" else "-")
    ^ (if cap.permit_load_store_cap then "c" else "-")
    ^ (if cap.permit_load_mutable then "m" else "-")
    ^ (if cap.permit_load_global then "g" else "-")
    ^ (if cap.permit_store_local_cap then "l " else "- ")
    ^ (if cap.permit_execute then "X" else "-")
    ^ (if cap.access_system_regs then "a " else "- ")
    ^ (if cap.permit_seal then "S" else "-")
    ^ (if cap.permit_unseal then "U" else "-")
    ^ (if cap.perm_user0 then "0" else "-")
    ^ ")"
}

/*!
 * For a given length computes the exponent, $e$, that would be used to represent
 * a capability of that length and returns a mask consisting of $e$ zeros in the
 * least significant bits and ones in the upper bits.
 */
val getRepresentableAlignmentMask: xlenbits -> xlenbits
/*!
 * The representable alignment mask for a given length depends on the exponent
 * that would be used to represent a region of that length, assuming the base
 * is sufficiently aligned. To compute this we resuse the implementation of
 * [setCapBounds]
 */
function getRepresentableAlignmentMask(len) = {
  let (exact, c) = setCapBounds(root_cap_mem, to_bits(sizeof(xlen), 0), len);
  var e = unsigned(c.E);
  ones(sizeof(xlen)) << e
}

/*!
 * For a given length, $l$, returns a value greater than or equal to $l$ that
 * will result in a precisely representable capability when used with a
 * base that is suitably aligned as per [getRepresentableAlignmentMask].
 */
val getRepresentableLength : xlenbits -> xlenbits
/*!
 * Given the required alignment mask returned by [getRepresentableAlignmentMask]
 * we can round up the length by bit twiddling.
 */
function getRepresentableLength(len) = {
  let m = getRepresentableAlignmentMask(len);
  (len + ~(m)) & m
}
