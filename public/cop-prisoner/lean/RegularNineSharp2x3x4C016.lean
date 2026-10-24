import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C011
import RegularNineSharp2x3x4C013
import RegularNineSharp2x3x4C014
import RegularNineSharp2x3x4C015
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
theorem node1024 : UpperPrefix a [5,7,4,6,8,3] 30 :=
  branch_upper a [5,7,4,6,8,3] 30 (by decide) (fin9_cases _
  node1021
  node1022
  node1023
  (invalid_upper a [5,7,4,6,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,3,8] 30 (by decide +kernel)))

theorem node1025 : UpperPrefix a [5,7,4,6,8] 30 :=
  branch_upper a [5,7,4,6,8] 30 (by decide) (fin9_cases _
  node1015
  node1016
  node1020
  node1024
  (invalid_upper a [5,7,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,8] 30 (by decide +kernel)))

theorem node1026 : UpperPrefix a [5,7,4,6] 30 :=
  branch_upper a [5,7,4,6] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,7,4,6,0] [5,7,0,2,6] 30 (by decide +kernel) node933)
  (PrefixConjugacy.upper aut18 [5,7,4,6,1] [5,7,0,2,8] 30 (by decide +kernel) node943)
  (invalid_upper a [5,7,4,6,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut4 [5,7,4,6,3] [5,7,4,2,6] 30 (by decide +kernel) node1013)
  (invalid_upper a [5,7,4,6,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,7] 30 (by decide +kernel))
  node1025)

theorem node1027 : UpperPrefix a [5,7,4] 30 :=
  branch_upper a [5,7,4] 30 (by decide) (fin9_cases _
  node1011
  (PrefixConjugacy.upper aut14 [5,7,4,1] [5,7,4,0] 30 (by decide +kernel) node1011)
  node1014
  (invalid_upper a [5,7,4,3] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,5] 30 (by decide +kernel))
  node1026
  (invalid_upper a [5,7,4,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [5,7,4,8] [5,7,4,6] 30 (by decide +kernel) node1026))

theorem node1028 : UpperPrefix a [5,7,6,0] 30 :=
  branch_upper a [5,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,6,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,7,6,0,1] [5,7,0,1,6] 30 (by decide +kernel) node897)
  (invalid_upper a [5,7,6,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,7,6,0,3] [5,7,0,2,6] 30 (by decide +kernel) node933)
  (invalid_upper a [5,7,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,0,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,7,6,0,8] [5,7,0,8,6] 30 (by decide +kernel) node1008))

theorem node1029 : UpperPrefix a [5,7,6,1] 30 :=
  branch_upper a [5,7,6,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut22 [5,7,6,1,0] [5,7,0,1,8] 30 (by decide +kernel) node915)
  (invalid_upper a [5,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut22 [5,7,6,1,3] [5,7,0,2,8] 30 (by decide +kernel) node943)
  (invalid_upper a [5,7,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,1,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut22 [5,7,6,1,8] [5,7,0,6,8] 30 (by decide +kernel) node972))

theorem node1030 : UpperPrefix a [5,7,6,2] 30 :=
  branch_upper a [5,7,6,2] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,7,6,2,0] [5,7,0,6,3] 30 (by decide +kernel) node952)
  (PrefixConjugacy.upper aut18 [5,7,6,2,1] [5,7,0,8,3] 30 (by decide +kernel) node983)
  (invalid_upper a [5,7,6,2,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,7,6,2,3] [5,7,4,2,6] 30 (by decide +kernel) node1013)
  (invalid_upper a [5,7,6,2,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,2,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut22 [5,7,6,2,8] [5,7,4,6,8] 30 (by decide +kernel) node1025))

theorem node1031 : UpperPrefix a [5,7,6,8] 30 :=
  branch_upper a [5,7,6,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,7,6,8,0] [5,7,0,6,8] 30 (by decide +kernel) node972)
  (PrefixConjugacy.upper aut18 [5,7,6,8,1] [5,7,0,8,6] 30 (by decide +kernel) node1008)
  (invalid_upper a [5,7,6,8,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut4 [5,7,6,8,3] [5,7,4,6,8] 30 (by decide +kernel) node1025)
  (invalid_upper a [5,7,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,8,8] 30 (by decide +kernel)))

theorem node1032 : UpperPrefix a [5,7,6] 30 :=
  branch_upper a [5,7,6] 30 (by decide) (fin9_cases _
  node1028
  node1029
  node1030
  (invalid_upper a [5,7,6,3] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,6,7] 30 (by decide +kernel))
  node1031)

theorem node1033 : UpperPrefix a [5,7] 30 :=
  branch_upper a [5,7] 30 (by decide) (fin9_cases _
  node1010
  (PrefixConjugacy.upper aut14 [5,7,1] [5,7,0] 30 (by decide +kernel) node1010)
  (invalid_upper a [5,7,2] 30 (by decide +kernel))
  (invalid_upper a [5,7,3] 30 (by decide +kernel))
  node1027
  (invalid_upper a [5,7,5] 30 (by decide +kernel))
  node1032
  (invalid_upper a [5,7,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [5,7,8] [5,7,6] 30 (by decide +kernel) node1032))

theorem node1034 : UpperPrefix a [5] 30 :=
  branch_upper a [5] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,0] 30 (by decide +kernel))
  (invalid_upper a [5,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut12 [5,2] [2,5] 30 (by decide +kernel) node739)
  (PrefixConjugacy.upper aut20 [5,3] [2,5] 30 (by decide +kernel) node739)
  (PrefixConjugacy.upper aut16 [5,4] [2,5] 30 (by decide +kernel) node739)
  (invalid_upper a [5,5] 30 (by decide +kernel))
  node881
  node1033
  (PrefixConjugacy.upper aut13 [5,8] [5,6] 30 (by decide +kernel) node881))

theorem node1035 : UpperPrefix a [] 30 :=
  branch_upper a [] 30 (by decide) (fin9_cases _
  (invalid_upper a [0] 30 (by decide +kernel))
  (invalid_upper a [1] 30 (by decide +kernel))
  node740
  (PrefixConjugacy.upper aut8 [3] [2] 30 (by decide +kernel) node740)
  (PrefixConjugacy.upper aut4 [4] [2] 30 (by decide +kernel) node740)
  node1034
  (PrefixConjugacy.upper aut3 [6] [5] 30 (by decide +kernel) node1034)
  (PrefixConjugacy.upper aut2 [7] [5] 30 (by decide +kernel) node1034)
  (PrefixConjugacy.upper aut1 [8] [5] 30 (by decide +kernel) node1034))

#print axioms node1035
end Delivery.FiniteExclusion.Sharp2x3x4
