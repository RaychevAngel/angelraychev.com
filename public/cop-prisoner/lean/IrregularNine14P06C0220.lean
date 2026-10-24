import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0043
import IrregularNine14P06C0044

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13200 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 70 137 276 33 112 240 368), lower := (rows 11 38 70 137 276 33 64 128 256), losses := [] }

theorem u13200 : Upper (D 6) (R 6) [10,36,66,129,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13201 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 201, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 70 137 276 48 97 225 353), lower := (rows 11 38 70 137 276 48 64 128 256), losses := [] }

theorem u13201 : Upper (D 6) (R 6) [10,36,66,129,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13201 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13202 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 137 276 96 113 177 305), lower := (rows 11 38 70 137 276 96 64 128 256), losses := [] }

theorem u13202 : Upper (D 6) (R 6) [10,36,66,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13203 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 70 137 304 33 84 212 340), lower := (rows 11 38 70 137 304 33 64 128 256), losses := [] }

theorem u13203 : Upper (D 6) (R 6) [10,36,66,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13204 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 137 304 36 81 209 337), lower := (rows 11 38 70 137 304 36 64 128 256), losses := [] }

theorem u13204 : Upper (D 6) (R 6) [10,36,66,129,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13205 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 70 137 304 48 69 197 325), lower := (rows 11 38 70 137 304 48 64 128 256), losses := [] }

theorem u13205 : Upper (D 6) (R 6) [10,36,66,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13205 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13206 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 137 304 96 85 149 277), lower := (rows 11 38 70 137 304 96 64 128 256), losses := [] }

theorem u13206 : Upper (D 6) (R 6) [10,36,66,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13207 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 70 137 336 33 116 180 308), lower := (rows 11 38 70 137 336 33 64 128 256), losses := [] }

theorem u13207 : Upper (D 6) (R 6) [10,36,66,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13208 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 137 336 36 113 177 305), lower := (rows 11 38 70 137 336 36 64 128 256), losses := [] }

theorem u13208 : Upper (D 6) (R 6) [10,36,66,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13209 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 137, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 38 70 137 336 48 101 165 293), lower := (rows 11 38 70 137 336 48 64 128 256), losses := [] }

theorem u13209 : Upper (D 6) (R 6) [10,36,66,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13209 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13210 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 38 70 140 49 33 336 464 336), lower := (rows 11 38 70 140 49 33 64 128 256), losses := [] }

theorem u13210 : Upper (D 6) (R 6) [10,36,66,132,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13211 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 70 140 49 48 321 449 321), lower := (rows 11 38 70 140 49 48 64 128 256), losses := [] }

theorem u13211 : Upper (D 6) (R 6) [10,36,66,132,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13211 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13212 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 140 49 96 337 401 273), lower := (rows 11 38 70 140 49 96 64 128 256), losses := [] }

theorem u13212 : Upper (D 6) (R 6) [10,36,66,132,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13213 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 140 49 288 81 209 337), lower := (rows 11 38 70 140 49 288 64 128 256), losses := [] }

theorem u13213 : Upper (D 6) (R 6) [10,36,66,132,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13213 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13214 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 70 140 81 33 368 432 304), lower := (rows 11 38 70 140 81 33 64 128 256), losses := [] }

theorem u13214 : Upper (D 6) (R 6) [10,36,66,132,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13215 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 140 81 48 353 417 289), lower := (rows 11 38 70 140 81 48 64 128 256), losses := [] }

theorem u13215 : Upper (D 6) (R 6) [10,36,66,132,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13215 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13216 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 140 81 288 113 177 305), lower := (rows 11 38 70 140 81 288 64 128 256), losses := [] }

theorem u13216 : Upper (D 6) (R 6) [10,36,66,132,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13216 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13217 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 70 140 273 33 112 240 368), lower := (rows 11 38 70 140 273 33 64 128 256), losses := [] }

theorem u13217 : Upper (D 6) (R 6) [10,36,66,132,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13218 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 140 273 48 97 225 353), lower := (rows 11 38 70 140 273 48 64 128 256), losses := [] }

theorem u13218 : Upper (D 6) (R 6) [10,36,66,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13218 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13219 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 140 273 96 113 177 305), lower := (rows 11 38 70 140 273 96 64 128 256), losses := [] }

theorem u13219 : Upper (D 6) (R 6) [10,36,66,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13220 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 70 140 304 33 81 209 337), lower := (rows 11 38 70 140 304 33 64 128 256), losses := [] }

theorem u13220 : Upper (D 6) (R 6) [10,36,66,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13221 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 70 140 304 48 65 193 321), lower := (rows 11 38 70 140 304 48 64 128 256), losses := [] }

theorem u13221 : Upper (D 6) (R 6) [10,36,66,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13221 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13222 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 140 304 96 81 145 273), lower := (rows 11 38 70 140 304 96 64 128 256), losses := [] }

theorem u13222 : Upper (D 6) (R 6) [10,36,66,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13223 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 70 140 336 33 113 177 305), lower := (rows 11 38 70 140 336 33 64 128 256), losses := [] }

theorem u13223 : Upper (D 6) (R 6) [10,36,66,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13224 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 140 336 48 97 161 289), lower := (rows 11 38 70 140 336 48 64 128 256), losses := [] }

theorem u13224 : Upper (D 6) (R 6) [10,36,66,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13224 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13225 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 488, targets := 6 },{ cop := 5, region := 326, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 38 70 152 21 33 352 480 352), lower := (rows 11 38 70 152 21 33 64 128 256), losses := [] }

theorem u13225 : Upper (D 6) (R 6) [10,36,66,144,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13226 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 152 21 96 353 417 289), lower := (rows 11 38 70 152 21 96 64 128 256), losses := [] }

theorem u13226 : Upper (D 6) (R 6) [10,36,66,144,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13227 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 488, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 38 70 152 21 288 97 225 353), lower := (rows 11 38 70 152 21 288 64 128 256), losses := [] }

theorem u13227 : Upper (D 6) (R 6) [10,36,66,144,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13227 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13228 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 70 152 49 33 324 452 324), lower := (rows 11 38 70 152 49 33 64 128 256), losses := [] }

theorem u13228 : Upper (D 6) (R 6) [10,36,66,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13229 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 152 49 36 321 449 321), lower := (rows 11 38 70 152 49 36 64 128 256), losses := [] }

theorem u13229 : Upper (D 6) (R 6) [10,36,66,144,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13230 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 152 49 96 325 389 261), lower := (rows 11 38 70 152 49 96 64 128 256), losses := [] }

theorem u13230 : Upper (D 6) (R 6) [10,36,66,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13231 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 11 38 70 152 49 288 69 197 325), lower := (rows 11 38 70 152 49 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 24 16 0 81 145 273), good := (rows 463 6 70 472 477 256 64 128 256) }] }

theorem u13231 : Upper (D 6) (R 6) [10,36,66,144,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13231 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13232 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 326, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 70 152 81 33 356 420 292), lower := (rows 11 38 70 152 81 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 49 66 130 258), good := (rows 505 484 452 184 121 57 64 128 256) }] }

theorem u13232 : Upper (D 6) (R 6) [10,36,66,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13233 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 152 81 36 353 417 289), lower := (rows 11 38 70 152 81 36 64 128 256), losses := [] }

theorem u13233 : Upper (D 6) (R 6) [10,36,66,144,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13234 : Route 9 := (fun mask => (mask,id))

def c13234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13234 : Upper (D 6) (R 6) [10,36,66,144,65,256] 13 := by
  apply FastRouting.sound _ _ [10,36,66,144,65,256] 13 (by decide) (choices 1) [1,4,32] r13234 c13234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2639
  · exact u2640
  · exact u2641

def b13235 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 70, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 70 152 273 33 100 228 356), lower := (rows 11 38 70 152 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 49 66 130 258), good := (rows 505 484 452 184 313 57 64 128 256) }] }

theorem u13235 : Upper (D 6) (R 6) [10,36,66,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13236 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 152 273 36 97 225 353), lower := (rows 11 38 70 152 273 36 64 128 256), losses := [] }

theorem u13236 : Upper (D 6) (R 6) [10,36,66,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13237 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 152 273 96 101 165 293), lower := (rows 11 38 70 152 273 96 64 128 256), losses := [] }

theorem u13237 : Upper (D 6) (R 6) [10,36,66,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13238 : Route 9 := (fun mask => (mask,id))

def c13238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13238 : Upper (D 6) (R 6) [10,36,66,144,260,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,144,260,1] 13 (by decide) (choices 1) [1,32] r13238 c13238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2642
  · exact u2643

def b13239 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 152 276 96 97 161 289), lower := (rows 11 38 70 152 276 96 64 128 256), losses := [] }

theorem u13239 : Upper (D 6) (R 6) [10,36,66,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13240 : Route 9 := (fun mask => (mask,id))

def c13240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13240 : Upper (D 6) (R 6) [10,36,66,144,288,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,144,288,1] 13 (by decide) (choices 1) [1,4] r13240 c13240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2644
  · exact u2645

def b13241 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 152 304 36 65 193 321), lower := (rows 11 38 70 152 304 36 64 128 256), losses := [] }

theorem u13241 : Upper (D 6) (R 6) [10,36,66,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13242 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 152 304 96 69 133 261), lower := (rows 11 38 70 152 304 96 64 128 256), losses := [] }

theorem u13242 : Upper (D 6) (R 6) [10,36,66,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13243 : Route 9 := (fun mask => (mask,id))

def c13243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13243 : Upper (D 6) (R 6) [10,36,66,144,320,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,144,320,1] 13 (by decide) (choices 1) [1,4,32] r13243 c13243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2646
  · exact u2647
  · exact u2648

def b13244 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 152 336 36 97 161 289), lower := (rows 11 38 70 152 336 36 64 128 256), losses := [] }

theorem u13244 : Upper (D 6) (R 6) [10,36,66,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13245 : Route 9 := (fun mask => (mask,id))

def c13245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u13245 : Upper (D 6) (R 6) [10,36,66,160,65,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,160,65,1] 13 (by decide) (choices 1) [4,16,256] r13245 c13245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2649
  · exact u2650
  · exact u2651

def b13246 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 168 81 36 337 401 273), lower := (rows 11 38 70 168 81 36 64 128 256), losses := [] }

theorem u13246 : Upper (D 6) (R 6) [10,36,66,160,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13247 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 70 168 81 48 325 389 261), lower := (rows 11 38 70 168 81 48 64 128 256), losses := [] }

theorem u13247 : Upper (D 6) (R 6) [10,36,66,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13247 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13248 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 70 168 81 288 85 149 277), lower := (rows 11 38 70 168 81 288 64 128 256), losses := [] }

theorem u13248 : Upper (D 6) (R 6) [10,36,66,160,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13248 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13249 : Route 9 := (fun mask => (mask,id))

def c13249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13249 : Upper (D 6) (R 6) [10,36,66,160,257,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,160,257,1] 13 (by decide) (choices 1) [4,16] r13249 c13249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2652
  · exact u2653

def b13250 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 168 273 36 81 209 337), lower := (rows 11 38 70 168 273 36 64 128 256), losses := [] }

theorem u13250 : Upper (D 6) (R 6) [10,36,66,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13251 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 70 168 273 48 69 197 325), lower := (rows 11 38 70 168 273 48 64 128 256), losses := [] }

theorem u13251 : Upper (D 6) (R 6) [10,36,66,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13251 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13252 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 168 273 96 85 149 277), lower := (rows 11 38 70 168 273 96 64 128 256), losses := [] }

theorem u13252 : Upper (D 6) (R 6) [10,36,66,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13253 : Route 9 := (fun mask => (mask,id))

def c13253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13253 : Upper (D 6) (R 6) [10,36,66,160,260,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,160,260,1] 13 (by decide) (choices 1) [1,16] r13253 c13253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2654
  · exact u2655

def b13254 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 70 168 276 48 65 193 321), lower := (rows 11 38 70 168 276 48 64 128 256), losses := [] }

theorem u13254 : Upper (D 6) (R 6) [10,36,66,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13254 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13255 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 168 276 96 81 145 273), lower := (rows 11 38 70 168 276 96 64 128 256), losses := [] }

theorem u13255 : Upper (D 6) (R 6) [10,36,66,160,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13256 : Route 9 := (fun mask => (mask,id))

def c13256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13256 : Upper (D 6) (R 6) [10,36,66,160,320,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,160,320,1] 13 (by decide) (choices 1) [1,4,16] r13256 c13256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2656
  · exact u2657
  · exact u2658

def b13257 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 168 336 36 81 145 273), lower := (rows 11 38 70 168 336 36 64 128 256), losses := [] }

theorem u13257 : Upper (D 6) (R 6) [10,36,66,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13258 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 70 168 336 48 69 133 261), lower := (rows 11 38 70 168 336 48 64 128 256), losses := [] }

theorem u13258 : Upper (D 6) (R 6) [10,36,66,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13258 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13259 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 70 200 49 33 340 404 276), lower := (rows 11 38 70 200 49 33 64 128 256), losses := [] }

theorem u13259 : Upper (D 6) (R 6) [10,36,66,192,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13259
end Delivery.IrregularNine14.P06
