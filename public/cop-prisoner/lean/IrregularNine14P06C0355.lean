import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0104
import IrregularNine14P06C0105

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21300 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 148 44 336 33 71 135 263), lower := (rows 35 74 148 44 336 33 64 128 256), losses := [] }

theorem u21300 : Upper (D 6) (R 6) [34,72,144,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21301 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 44 336 34 69 133 261), lower := (rows 35 74 148 44 336 34 64 128 256), losses := [] }

theorem u21301 : Upper (D 6) (R 6) [34,72,144,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21302 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 148 44 336 36 67 131 259), lower := (rows 35 74 148 44 336 36 64 128 256), losses := [] }

theorem u21302 : Upper (D 6) (R 6) [34,72,144,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21303 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 265 21 34 100 228 356), lower := (rows 35 74 148 265 21 34 64 128 256), losses := [] }

theorem u21303 : Upper (D 6) (R 6) [34,72,144,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21304 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 148 265 21 36 98 226 354), lower := (rows 35 74 148 265 21 36 64 128 256), losses := [] }

theorem u21304 : Upper (D 6) (R 6) [34,72,144,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21305 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 265 21 96 102 166 294), lower := (rows 35 74 148 265 21 96 64 128 256), losses := [] }

theorem u21305 : Upper (D 6) (R 6) [34,72,144,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21306 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 212, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 148 265 22 33 100 228 356), lower := (rows 35 74 148 265 22 33 64 128 256), losses := [] }

theorem u21306 : Upper (D 6) (R 6) [34,72,144,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21307 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 148 265 22 36 97 225 353), lower := (rows 35 74 148 265 22 36 64 128 256), losses := [] }

theorem u21307 : Upper (D 6) (R 6) [34,72,144,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21308 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 265 22 96 101 165 293), lower := (rows 35 74 148 265 22 96 64 128 256), losses := [] }

theorem u21308 : Upper (D 6) (R 6) [34,72,144,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21309 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 212, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 148 265 52 33 70 198 326), lower := (rows 35 74 148 265 52 33 64 128 256), losses := [] }

theorem u21309 : Upper (D 6) (R 6) [34,72,144,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21310 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 265 52 34 69 197 325), lower := (rows 35 74 148 265 52 34 64 128 256), losses := [] }

theorem u21310 : Upper (D 6) (R 6) [34,72,144,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21311 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 148 265 52 36 67 195 323), lower := (rows 35 74 148 265 52 36 64 128 256), losses := [] }

theorem u21311 : Upper (D 6) (R 6) [34,72,144,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21312 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 265 52 96 71 135 263), lower := (rows 35 74 148 265 52 96 64 128 256), losses := [] }

theorem u21312 : Upper (D 6) (R 6) [34,72,144,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21313 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 265 81 34 100 164 292), lower := (rows 35 74 148 265 81 34 64 128 256), losses := [] }

theorem u21313 : Upper (D 6) (R 6) [34,72,144,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21314 : Route 9 := (fun mask => (mask,id))

def c21314 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21314 : Upper (D 6) (R 6) [34,72,144,257,65,4] 13 := by
  apply FastRouting.sound _ _ [34,72,144,257,65,4] 13 (by decide) (choices 1) [2,4,32] r21314 c21314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6293
  · exact u6294
  · exact u6295

def b21315 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 212, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 148 265 84 33 102 166 294), lower := (rows 35 74 148 265 84 33 64 128 256), losses := [] }

theorem u21315 : Upper (D 6) (R 6) [34,72,144,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21316 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 265 84 34 101 165 293), lower := (rows 35 74 148 265 84 34 64 128 256), losses := [] }

theorem u21316 : Upper (D 6) (R 6) [34,72,144,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21317 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 148 265 84 36 99 163 291), lower := (rows 35 74 148 265 84 36 64 128 256), losses := [] }

theorem u21317 : Upper (D 6) (R 6) [34,72,144,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21318 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 212, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 148 265 112 33 70 134 262), lower := (rows 35 74 148 265 112 33 64 128 256), losses := [] }

theorem u21318 : Upper (D 6) (R 6) [34,72,144,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21319 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 265 112 34 69 133 261), lower := (rows 35 74 148 265 112 34 64 128 256), losses := [] }

theorem u21319 : Upper (D 6) (R 6) [34,72,144,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21320 : Route 9 := (fun mask => (mask,id))

def c21320 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21320 : Upper (D 6) (R 6) [34,72,144,257,96,4] 13 := by
  apply FastRouting.sound _ _ [34,72,144,257,96,4] 13 (by decide) (choices 1) [1,2,4] r21320 c21320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6296
  · exact u6297
  · exact u6298

def b21321 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 148 266 21 33 100 228 356), lower := (rows 35 74 148 266 21 33 64 128 256), losses := [] }

theorem u21321 : Upper (D 6) (R 6) [34,72,144,258,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21322 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 148 266 21 36 97 225 353), lower := (rows 35 74 148 266 21 36 64 128 256), losses := [] }

theorem u21322 : Upper (D 6) (R 6) [34,72,144,258,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21323 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 266 21 96 101 165 293), lower := (rows 35 74 148 266 21 96 64 128 256), losses := [] }

theorem u21323 : Upper (D 6) (R 6) [34,72,144,258,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21324 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 148 266 52 33 69 197 325), lower := (rows 35 74 148 266 52 33 64 128 256), losses := [] }

theorem u21324 : Upper (D 6) (R 6) [34,72,144,258,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21325 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 148 266 52 36 65 193 321), lower := (rows 35 74 148 266 52 36 64 128 256), losses := [] }

theorem u21325 : Upper (D 6) (R 6) [34,72,144,258,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21326 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 266 52 96 69 133 261), lower := (rows 35 74 148 266 52 96 64 128 256), losses := [] }

theorem u21326 : Upper (D 6) (R 6) [34,72,144,258,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21327 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 148 266 84 33 101 165 293), lower := (rows 35 74 148 266 84 33 64 128 256), losses := [] }

theorem u21327 : Upper (D 6) (R 6) [34,72,144,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21328 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 148 266 84 36 97 161 289), lower := (rows 35 74 148 266 84 36 64 128 256), losses := [] }

theorem u21328 : Upper (D 6) (R 6) [34,72,144,258,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21329 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 148 266 112 33 69 133 261), lower := (rows 35 74 148 266 112 33 64 128 256), losses := [] }

theorem u21329 : Upper (D 6) (R 6) [34,72,144,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21330 : Route 9 := (fun mask => (mask,id))

def c21330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21330 : Upper (D 6) (R 6) [34,72,144,258,96,4] 13 := by
  apply FastRouting.sound _ _ [34,72,144,258,96,4] 13 (by decide) (choices 1) [1,4] r21330 c21330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6299
  · exact u6300

def b21331 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 148 268 21 33 98 226 354), lower := (rows 35 74 148 268 21 33 64 128 256), losses := [] }

theorem u21331 : Upper (D 6) (R 6) [34,72,144,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21332 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 268 21 34 97 225 353), lower := (rows 35 74 148 268 21 34 64 128 256), losses := [] }

theorem u21332 : Upper (D 6) (R 6) [34,72,144,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21333 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 268 21 96 99 163 291), lower := (rows 35 74 148 268 21 96 64 128 256), losses := [] }

theorem u21333 : Upper (D 6) (R 6) [34,72,144,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21334 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 148 268 22 33 97 225 353), lower := (rows 35 74 148 268 22 33 64 128 256), losses := [] }

theorem u21334 : Upper (D 6) (R 6) [34,72,144,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21335 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 268 22 96 97 161 289), lower := (rows 35 74 148 268 22 96 64 128 256), losses := [] }

theorem u21335 : Upper (D 6) (R 6) [34,72,144,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21336 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 148 268 52 33 67 195 323), lower := (rows 35 74 148 268 52 33 64 128 256), losses := [] }

theorem u21336 : Upper (D 6) (R 6) [34,72,144,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21337 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 268 52 34 65 193 321), lower := (rows 35 74 148 268 52 34 64 128 256), losses := [] }

theorem u21337 : Upper (D 6) (R 6) [34,72,144,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21338 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 268 52 96 67 131 259), lower := (rows 35 74 148 268 52 96 64 128 256), losses := [] }

theorem u21338 : Upper (D 6) (R 6) [34,72,144,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21339 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 74 148 268 81 33 102 166 294), lower := (rows 35 74 148 268 81 33 64 128 256), losses := [] }

theorem u21339 : Upper (D 6) (R 6) [34,72,144,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21340 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 268 81 34 101 165 293), lower := (rows 35 74 148 268 81 34 64 128 256), losses := [] }

theorem u21340 : Upper (D 6) (R 6) [34,72,144,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21341 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 80, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 35 74 148 268 81 36 99 163 291), lower := (rows 35 74 148 268 81 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 20 24 16 60 0 131 259), good := (rows 419 427 188 300 445 36 0 128 256) }] }

theorem u21341 : Upper (D 6) (R 6) [34,72,144,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21342 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 74 148 268 112 33 71 135 263), lower := (rows 35 74 148 268 112 33 64 128 256), losses := [] }

theorem u21342 : Upper (D 6) (R 6) [34,72,144,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21343 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 268 112 34 69 133 261), lower := (rows 35 74 148 268 112 34 64 128 256), losses := [] }

theorem u21343 : Upper (D 6) (R 6) [34,72,144,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21344 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 80, targets := 4 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 74 148 268 112 36 67 131 259), lower := (rows 35 74 148 268 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 44 64 128 256), good := (rows 50 122 180 300 112 36 64 128 256) },{ target := 1, region := (rows 1 0 4 8 18 44 64 128 256), good := (rows 49 120 180 300 112 36 64 128 256) }] }

theorem u21344 : Upper (D 6) (R 6) [34,72,144,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21345 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 148 296 21 33 70 198 326), lower := (rows 35 74 148 296 21 33 64 128 256), losses := [] }

theorem u21345 : Upper (D 6) (R 6) [34,72,144,288,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21346 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 296 21 34 69 197 325), lower := (rows 35 74 148 296 21 34 64 128 256), losses := [] }

theorem u21346 : Upper (D 6) (R 6) [34,72,144,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21347 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 148 296 21 36 67 195 323), lower := (rows 35 74 148 296 21 36 64 128 256), losses := [] }

theorem u21347 : Upper (D 6) (R 6) [34,72,144,288,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21348 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 296 21 96 71 135 263), lower := (rows 35 74 148 296 21 96 64 128 256), losses := [] }

theorem u21348 : Upper (D 6) (R 6) [34,72,144,288,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21349 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 148 296 22 33 69 197 325), lower := (rows 35 74 148 296 22 33 64 128 256), losses := [] }

theorem u21349 : Upper (D 6) (R 6) [34,72,144,288,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21350 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 148 296 22 36 65 193 321), lower := (rows 35 74 148 296 22 36 64 128 256), losses := [] }

theorem u21350 : Upper (D 6) (R 6) [34,72,144,288,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21351 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 296 22 96 69 133 261), lower := (rows 35 74 148 296 22 96 64 128 256), losses := [] }

theorem u21351 : Upper (D 6) (R 6) [34,72,144,288,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21352 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 148 296 81 33 70 134 262), lower := (rows 35 74 148 296 81 33 64 128 256), losses := [] }

theorem u21352 : Upper (D 6) (R 6) [34,72,144,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21353 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 296 81 34 69 133 261), lower := (rows 35 74 148 296 81 34 64 128 256), losses := [] }

theorem u21353 : Upper (D 6) (R 6) [34,72,144,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21354 : Route 9 := (fun mask => (mask,id))

def c21354 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21354 : Upper (D 6) (R 6) [34,72,144,288,65,4] 13 := by
  apply FastRouting.sound _ _ [34,72,144,288,65,4] 13 (by decide) (choices 1) [1,2,4] r21354 c21354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6301
  · exact u6302
  · exact u6303

def b21355 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 148 296 84 33 71 135 263), lower := (rows 35 74 148 296 84 33 64 128 256), losses := [] }

theorem u21355 : Upper (D 6) (R 6) [34,72,144,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21356 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 296 84 34 69 133 261), lower := (rows 35 74 148 296 84 34 64 128 256), losses := [] }

theorem u21356 : Upper (D 6) (R 6) [34,72,144,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21357 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 148 296 84 36 67 131 259), lower := (rows 35 74 148 296 84 36 64 128 256), losses := [] }

theorem u21357 : Upper (D 6) (R 6) [34,72,144,288,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21358 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 13 81 34 340 404 276), lower := (rows 35 74 164 13 81 34 64 128 256), losses := [] }

theorem u21358 : Upper (D 6) (R 6) [34,72,160,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21359 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 164 13 81 36 338 402 274), lower := (rows 35 74 164 13 81 36 64 128 256), losses := [] }

theorem u21359 : Upper (D 6) (R 6) [34,72,160,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21359
end Delivery.IrregularNine14.P06
