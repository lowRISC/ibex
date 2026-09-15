

/* Syntactic sugar */

infixr 1 -->

type operator -->('p: Bool, 'q: Bool) -> Bool = not('p) | 'q
val operator --> : forall ('p 'q: Bool). (bool('p), bool('q)) -> bool('p --> 'q)
function operator --> (p, q) = not_bool(p) | q

infix 1 <-->

type operator <-->('p: Bool, 'q: Bool) -> Bool = ('p --> 'q) & ('q --> 'p)
val operator <--> : forall ('p 'q: Bool). (bool('p), bool('q)) -> bool('p <--> 'q)
function operator <--> (p, q) = (p --> q) & (q --> p)

/* Useful functions */

/*!
 * THIS is a helper function to compress and then decompress a Capability.
 * The [Capability] struct can hold non-encodable values therefore some
 * properties encode then decode a Capability to check the effect that
 * compression / decompression has. In general the bounds, address and tag
 * should be unaffected but the permissions and otype might change.
 */
function encodeDecode(c : Capability) -> Capability =  capBitsToCapability(c.tag, capToBits(c))

/*!
 * THIS is a helper to check that the given Capability is unaffected by
 * compression / decompression.
 */
function capEncodable(c : Capability) -> bool = c == encodeDecode(c)
