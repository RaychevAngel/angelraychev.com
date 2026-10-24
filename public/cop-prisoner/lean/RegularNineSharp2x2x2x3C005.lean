import RegularNineSharp2x2x2x3Base
import RegularNineSharp2x2x2x3C001
import RegularNineSharp2x2x2x3C002
import RegularNineSharp2x2x2x3C003
import RegularNineSharp2x2x2x3C004
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x2x3
open Bounds BoundTreeRows Extremal
theorem node320 : UpperPrefix a [4,6,7,8,3] 30 :=
  branch_upper a [4,6,7,8,3] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut69 [4,6,7,8,3,0] [2,4,1,6,8,7] 30 (by decide +kernel) node86)
  (PrefixConjugacy.upper aut93 [4,6,7,8,3,1] [2,4,6,1,8,7] 30 (by decide +kernel) node144)
  (PrefixConjugacy.upper aut113 [4,6,7,8,3,2] [2,3,6,7,1,8] 30 (by decide +kernel) node220)
  (invalid_upper a [4,6,7,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,3,8] 30 (by decide +kernel)))

theorem node321 : UpperPrefix a [4,6,7,8] 30 :=
  branch_upper a [4,6,7,8] 30 (by decide) (fin9_cases _
  node316
  node318
  node319
  node320
  (invalid_upper a [4,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,8] 30 (by decide +kernel)))

theorem node322 : UpperPrefix a [6,7,4] 30 :=
  branch_upper a [6,7,4] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut54 [6,7,4,0] [2,4,6,7] 30 (by decide +kernel) node174)
  (PrefixConjugacy.upper aut80 [6,7,4,1] [2,4,6,8] 30 (by decide +kernel) node181)
  (invalid_upper a [6,7,4,2] 30 (by decide +kernel))
  (invalid_upper a [6,7,4,3] 30 (by decide +kernel))
  (invalid_upper a [6,7,4,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut48 [6,7,4,5] [4,5,6,7] 30 (by decide +kernel) node314)
  (invalid_upper a [6,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [6,7,4,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut49 [6,7,4,8] [4,6,7,8] 30 (by decide +kernel) node321))

theorem node323 : UpperPrefix a [6,7,8] 30 :=
  branch_upper a [6,7,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut55 [6,7,8,0] [2,6,7,8] 30 (by decide +kernel) node287)
  (PrefixConjugacy.upper aut79 [6,7,8,1] [2,6,8,7] 30 (by decide +kernel) node308)
  (invalid_upper a [6,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [6,7,8,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut55 [6,7,8,4] [4,6,7,8] 30 (by decide +kernel) node321)
  (PrefixConjugacy.upper aut58 [6,7,8,5] [4,6,7,8] 30 (by decide +kernel) node321)
  (invalid_upper a [6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [6,7,8,8] 30 (by decide +kernel)))

theorem node324 : UpperPrefix a [6,7] 30 :=
  branch_upper a [6,7] 30 (by decide) (fin9_cases _
  node312
  node313
  (invalid_upper a [6,7,2] 30 (by decide +kernel))
  (invalid_upper a [6,7,3] 30 (by decide +kernel))
  node322
  (PrefixConjugacy.upper aut3 [6,7,5] [6,7,4] 30 (by decide +kernel) node322)
  (invalid_upper a [6,7,6] 30 (by decide +kernel))
  (invalid_upper a [6,7,7] 30 (by decide +kernel))
  node323)

theorem node325 : UpperPrefix a [6] 30 :=
  branch_upper a [6] 30 (by decide) (fin9_cases _
  (invalid_upper a [6,0] 30 (by decide +kernel))
  (invalid_upper a [6,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut24 [6,2] [2,6] 30 (by decide +kernel) node310)
  (PrefixConjugacy.upper aut30 [6,3] [2,6] 30 (by decide +kernel) node310)
  (PrefixConjugacy.upper aut36 [6,4] [2,6] 30 (by decide +kernel) node310)
  (PrefixConjugacy.upper aut39 [6,5] [2,6] 30 (by decide +kernel) node310)
  (invalid_upper a [6,6] 30 (by decide +kernel))
  node324
  (PrefixConjugacy.upper aut25 [6,8] [6,7] 30 (by decide +kernel) node324))

theorem node326 : UpperPrefix a [] 30 :=
  branch_upper a [] 30 (by decide) (fin9_cases _
  (invalid_upper a [0] 30 (by decide +kernel))
  (invalid_upper a [1] 30 (by decide +kernel))
  node311
  (PrefixConjugacy.upper aut6 [3] [2] 30 (by decide +kernel) node311)
  (PrefixConjugacy.upper aut12 [4] [2] 30 (by decide +kernel) node311)
  (PrefixConjugacy.upper aut15 [5] [2] 30 (by decide +kernel) node311)
  node325
  (PrefixConjugacy.upper aut2 [7] [6] 30 (by decide +kernel) node325)
  (PrefixConjugacy.upper aut1 [8] [6] 30 (by decide +kernel) node325))

#print axioms node326
end Delivery.FiniteExclusion.Sharp2x2x2x3
