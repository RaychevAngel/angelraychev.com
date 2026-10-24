import RegularNineSharp4x5Base
import RegularNineSharp4x5C000
import RegularNineSharp4x5C001
import RegularNineSharp4x5C003
import RegularNineSharp4x5C005
import RegularNineSharp4x5C006
import RegularNineSharp4x5C007
import RegularNineSharp4x5C010
import RegularNineSharp4x5C013
import RegularNineSharp4x5C014
import RegularNineSharp4x5C015
import RegularNineSharp4x5C016
import RegularNineSharp4x5C017
import RegularNineSharp4x5C018
import RegularNineSharp4x5C019
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert1280 : Leaf := ⟨⟨332,328,0,326,78,0,270,78,78⟩,[(2,5),(5,2)],[(0,6,2),(0,6,5)],⟨19,134,76,41,304,104,193,390,278⟩,⟨19,134,76,41,304,104,193,384,272⟩,[⟨5,1285820225610258091877649,⟨467,198,76,77,471,76,193,449,467⟩⟩,⟨4,1210255159958945762944513,⟨239,166,110,111,422,110,239,384,386⟩⟩,⟨7,1218371709021557189772291,⟨283,319,108,45,308,108,109,256,272⟩⟩]⟩
theorem node1280 : UpperPrefix a [4,7,6,5,8,3,0] 30 :=
  Boolean.leaf_sound a [4,7,6,5,8,3,0] 30 cert1280 (by decide +kernel)

def cert1281 : Leaf := ⟨⟨332,345,0,342,79,0,0,95,79⟩,[(2,5),(5,2),(6,1)],[(7,1,6)],⟨19,134,76,41,304,104,194,389,277⟩,⟨19,134,76,41,304,104,194,384,272⟩,[⟨5,1285817955796045897147665,⟨467,198,76,77,471,76,194,449,467⟩⟩]⟩
theorem node1281 : UpperPrefix a [4,7,6,5,8,3,1] 30 :=
  Boolean.leaf_sound a [4,7,6,5,8,3,1] 30 cert1281 (by decide +kernel)

def cert1282 : Leaf := ⟨⟨488,0,0,466,203,0,0,123,235⟩,[(1,6),(2,5),(5,2),(6,1)],[],⟨19,134,76,41,304,104,196,387,275⟩,⟨19,134,76,41,304,104,196,384,272⟩,[⟨2,1224302334989996136596483,⟨411,443,120,441,304,120,224,384,272⟩⟩]⟩
theorem node1282 : UpperPrefix a [4,7,6,5,8,3,2] 30 :=
  Boolean.leaf_sound a [4,7,6,5,8,3,2] 30 cert1282 (by decide +kernel)

theorem node1283 : UpperPrefix a [4,7,6,5,8,3] 30 :=
  branch_upper a [4,7,6,5,8,3] 30 (by decide) (fin9_cases _
  node1280
  node1281
  node1282
  (invalid_upper a [4,7,6,5,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,3,8] 30 (by decide +kernel)))

theorem node1284 : UpperPrefix a [4,7,6,5,8] 30 :=
  branch_upper a [4,7,6,5,8] 30 (by decide) (fin9_cases _
  node1269
  node1275
  node1279
  node1283
  (invalid_upper a [4,7,6,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,8] 30 (by decide +kernel)))

theorem node1285 : UpperPrefix a [4,7,6,5] 30 :=
  branch_upper a [4,7,6,5] 30 (by decide) (fin9_cases _
  node1230
  node1240
  node1255
  node1265
  (invalid_upper a [4,7,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,7] 30 (by decide +kernel))
  node1284)

theorem node1286 : UpperPrefix a [4,7,6] 30 :=
  branch_upper a [4,7,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,7,6,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,7,6,1] [2,4,7,6] 30 (by decide +kernel) node336)
  (PrefixConjugacy.upper aut5 [4,7,6,2] [3,4,7,6] 30 (by decide +kernel) node842)
  (invalid_upper a [4,7,6,3] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,4] 30 (by decide +kernel))
  node1285
  (invalid_upper a [4,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut6 [4,7,6,8] [4,5,8,7] 30 (by decide +kernel) node1162))

theorem node1287 : UpperPrefix a [4,7,8] 30 :=
  branch_upper a [4,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,7,8,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,7,8,1] [2,4,7,8] 30 (by decide +kernel) node370)
  (PrefixConjugacy.upper aut5 [4,7,8,2] [3,4,7,8] 30 (by decide +kernel) node873)
  (invalid_upper a [4,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,7,8,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut17 [4,7,8,5] [4,5,7,6] 30 (by decide +kernel) node1083)
  (PrefixConjugacy.upper aut17 [4,7,8,6] [4,5,8,6] 30 (by decide +kernel) node1129)
  (invalid_upper a [4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,8,8] 30 (by decide +kernel)))

theorem node1288 : UpperPrefix a [4,7] 30 :=
  branch_upper a [4,7] 30 (by decide) (fin9_cases _
  node1220
  node1221
  (invalid_upper a [4,7,2] 30 (by decide +kernel))
  (invalid_upper a [4,7,3] 30 (by decide +kernel))
  (invalid_upper a [4,7,4] 30 (by decide +kernel))
  node1222
  node1286
  (invalid_upper a [4,7,7] 30 (by decide +kernel))
  node1287)

theorem node1289 : UpperPrefix a [4,8,0] 30 :=
  branch_upper a [4,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,8,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut10 [4,8,0,1] [2,3,4,8] 30 (by decide +kernel) node81)
  (PrefixConjugacy.upper aut10 [4,8,0,2] [2,0,4,8] 30 (by decide +kernel) node44)
  (invalid_upper a [4,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [4,8,0,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [4,8,0,5] [2,4,8,7] 30 (by decide +kernel) node454)
  (PrefixConjugacy.upper aut13 [4,8,0,6] [2,4,7,6] 30 (by decide +kernel) node336)
  (PrefixConjugacy.upper aut12 [4,8,0,7] [2,4,6,5] 30 (by decide +kernel) node212)
  (invalid_upper a [4,8,0,8] 30 (by decide +kernel)))

theorem node1290 : UpperPrefix a [4,8,1] 30 :=
  branch_upper a [4,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [4,8,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut10 [4,8,1,2] [3,0,4,8] 30 (by decide +kernel) node494)
  (invalid_upper a [4,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [4,8,1,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [4,8,1,5] [3,4,8,7] 30 (by decide +kernel) node989)
  (PrefixConjugacy.upper aut13 [4,8,1,6] [3,4,7,6] 30 (by decide +kernel) node842)
  (PrefixConjugacy.upper aut12 [4,8,1,7] [3,4,6,5] 30 (by decide +kernel) node671)
  (invalid_upper a [4,8,1,8] 30 (by decide +kernel)))

theorem node1291 : UpperPrefix a [4,8,5] 30 :=
  branch_upper a [4,8,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,8,5,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,8,5,1] [2,4,8,5] 30 (by decide +kernel) node391)
  (PrefixConjugacy.upper aut5 [4,8,5,2] [3,4,8,5] 30 (by decide +kernel) node908)
  (invalid_upper a [4,8,5,3] 30 (by decide +kernel))
  (invalid_upper a [4,8,5,4] 30 (by decide +kernel))
  (invalid_upper a [4,8,5,5] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [4,8,5,6] [4,5,8,7] 30 (by decide +kernel) node1162)
  (PrefixConjugacy.upper aut7 [4,8,5,7] [4,6,5,7] 30 (by decide +kernel) node1215)
  (invalid_upper a [4,8,5,8] 30 (by decide +kernel)))

theorem node1292 : UpperPrefix a [4,8,6] 30 :=
  branch_upper a [4,8,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,8,6,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,8,6,1] [2,4,8,6] 30 (by decide +kernel) node420)
  (PrefixConjugacy.upper aut5 [4,8,6,2] [3,4,8,6] 30 (by decide +kernel) node946)
  (invalid_upper a [4,8,6,3] 30 (by decide +kernel))
  (invalid_upper a [4,8,6,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut16 [4,8,6,5] [4,7,6,5] 30 (by decide +kernel) node1285)
  (invalid_upper a [4,8,6,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut13 [4,8,6,7] [4,5,7,6] 30 (by decide +kernel) node1083)
  (invalid_upper a [4,8,6,8] 30 (by decide +kernel)))

theorem node1293 : UpperPrefix a [4,8,7] 30 :=
  branch_upper a [4,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,8,7,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,8,7,1] [2,4,8,7] 30 (by decide +kernel) node454)
  (PrefixConjugacy.upper aut5 [4,8,7,2] [3,4,8,7] 30 (by decide +kernel) node989)
  (invalid_upper a [4,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [4,8,7,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut12 [4,8,7,5] [4,7,6,5] 30 (by decide +kernel) node1285)
  (PrefixConjugacy.upper aut8 [4,8,7,6] [4,7,6,5] 30 (by decide +kernel) node1285)
  (invalid_upper a [4,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [4,8,7,8] 30 (by decide +kernel)))

theorem node1294 : UpperPrefix a [4,8] 30 :=
  branch_upper a [4,8] 30 (by decide) (fin9_cases _
  node1289
  node1290
  (invalid_upper a [4,8,2] 30 (by decide +kernel))
  (invalid_upper a [4,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,8,4] 30 (by decide +kernel))
  node1291
  node1292
  node1293
  (invalid_upper a [4,8,8] 30 (by decide +kernel)))

theorem node1295 : UpperPrefix a [4] 30 :=
  branch_upper a [4] 30 (by decide) (fin9_cases _
  node998
  (invalid_upper a [4,1] 30 (by decide +kernel))
  (invalid_upper a [4,2] 30 (by decide +kernel))
  node1005
  (invalid_upper a [4,4] 30 (by decide +kernel))
  node1164
  node1219
  node1288
  node1294)

theorem node1296 : UpperPrefix a [] 30 :=
  branch_upper a [] 30 (by decide) (fin9_cases _
  (invalid_upper a [0] 30 (by decide +kernel))
  (invalid_upper a [1] 30 (by decide +kernel))
  node457
  node992
  node1295
  (PrefixConjugacy.upper aut4 [5] [4] 30 (by decide +kernel) node1295)
  (PrefixConjugacy.upper aut3 [6] [4] 30 (by decide +kernel) node1295)
  (PrefixConjugacy.upper aut2 [7] [4] 30 (by decide +kernel) node1295)
  (PrefixConjugacy.upper aut1 [8] [4] 30 (by decide +kernel) node1295))

#print axioms node1296
end Delivery.FiniteExclusion.Sharp4x5
