open Sail_lib
module BI = Nat_big_num

let gen_sailbits n =
  QCheck.Gen.(list_repeat n (map Sail_lib.bit_of_bool bool))

(* Generate bitvectors of n bits biased towards smaller values *)
let gen_sailbits_geom n s =
  let zeros = Random.State.int s (n-1) in
  let lowerBits = gen_sailbits (n - zeros) s in
  Sail_lib.zeros (BI.of_int zeros) @ lowerBits

let test_cap_decode capbits =
  let cap = Cheri_cc.zcapBitsToCapability(false, capbits) in
  let (bot, top)= Cheri_cc.zgetCapBounds(cap) in
  begin
    print (Cheri_cc.string_of_zbits capbits);
    print (",0x");
    print (Z.format "08x" bot);
    print (",0x");
    print (Z.format "09x" top);
    print ",";
    print (Cheri_cc.string_of_zbits (Cheri_cc.zgetCapPerms cap));
    print (",");
    print_endline (Cheri_cc.string_of_zbits (cap.zotype));
    true
  end

let arbitrary_cap_bits = QCheck.make ~print:Sail_lib.string_of_bits (gen_sailbits 64)

let testsuite = [
  QCheck.Test.make ~count:10000 ~long_factor:1000 ~name:"capDecode"  arbitrary_cap_bits test_cap_decode;
]

let () = (
    print_endline "bits, bottom, top, perms, type";
    QCheck_runner.run_tests_main testsuite
  )
