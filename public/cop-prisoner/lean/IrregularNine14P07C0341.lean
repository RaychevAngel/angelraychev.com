import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0095

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20460 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 44 336 34 193 129 385), lower := (rows 35 194 28 44 336 34 64 128 256), losses := [] }

theorem u20460 : Upper (D 7) (R 7) [34,192,24,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20461 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 44 336 160 67 131 259), lower := (rows 35 194 28 44 336 160 64 128 256), losses := [] }

theorem u20461 : Upper (D 7) (R 7) [34,192,24,36,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20462 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 73 145 34 356 420 292), lower := (rows 35 194 28 73 145 34 64 128 256), losses := [] }

theorem u20462 : Upper (D 7) (R 7) [34,192,24,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20463 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 0, region := 400, targets := 64 },{ cop := 0, region := 328, targets := 128 }], pairs := [(1,0),(3,7),(4,6)], upper := (rows 35 194 28 73 145 36 354 418 290), lower := (rows 35 194 28 73 145 36 64 128 256), losses := [] }

theorem u20463 : Upper (D 7) (R 7) [34,192,24,65,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20463 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20464 : Route 9 := (fun mask => (mask,id))

def c20464 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20464 : Upper (D 7) (R 7) [34,192,24,65,129,256] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,129,256] 13 (by decide) (choices 1) [2,4,32] r20464 c20464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5700
  · exact u5701
  · exact u5702

def b20465 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 194 28 73 176 33 326 390 262), lower := (rows 35 194 28 73 176 33 64 128 256), losses := [] }

theorem u20465 : Upper (D 7) (R 7) [34,192,24,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20466 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 73 176 34 325 389 261), lower := (rows 35 194 28 73 176 34 64 128 256), losses := [] }

theorem u20466 : Upper (D 7) (R 7) [34,192,24,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20467 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,5),(3,5),(4,6)], upper := (rows 35 194 28 73 176 36 323 387 259), lower := (rows 35 194 28 73 176 36 64 128 256), losses := [] }

theorem u20467 : Upper (D 7) (R 7) [34,192,24,65,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20467 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20468 : Route 9 := (fun mask => (mask,id))

def c20468 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20468 : Upper (D 7) (R 7) [34,192,24,65,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,160,256] 13 (by decide) (choices 1) [1,2,4] r20468 c20468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5703
  · exact u5704
  · exact u5705

def b20469 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 73 273 34 228 164 420), lower := (rows 35 194 28 73 273 34 64 128 256), losses := [] }

theorem u20469 : Upper (D 7) (R 7) [34,192,24,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20470 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 1 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 35 194 28 73 273 36 226 162 418), lower := (rows 35 194 28 73 273 36 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 25 44 0 129 257), good := (rows 435 130 60 445 401 36 0 128 256) }] }

theorem u20470 : Upper (D 7) (R 7) [34,192,24,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20470 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20471 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 73 273 160 102 166 294), lower := (rows 35 194 28 73 273 160 64 128 256), losses := [] }

theorem u20471 : Upper (D 7) (R 7) [34,192,24,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20472 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 28 73 274 33 228 164 420), lower := (rows 35 194 28 73 274 33 64 128 256), losses := [{ target := 7, region := (rows 19 2 20 10 16 63 64 0 256), good := (rows 43 107 61 105 319 33 64 0 256) }] }

theorem u20472 : Upper (D 7) (R 7) [34,192,24,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20473 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 200, targets := 2 },{ cop := 0, region := 400, targets := 64 }], pairs := [(2,6),(3,1),(4,6)], upper := (rows 35 194 28 73 274 36 225 161 417), lower := (rows 35 194 28 73 274 36 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 17 44 0 137 265), good := (rows 435 130 444 445 274 36 0 128 256) }] }

theorem u20473 : Upper (D 7) (R 7) [34,192,24,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20473 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20474 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 73 274 160 101 165 293), lower := (rows 35 194 28 73 274 160 64 128 256), losses := [] }

theorem u20474 : Upper (D 7) (R 7) [34,192,24,65,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20475 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 0, region := 194, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(3,7)], upper := (rows 35 194 28 73 276 33 226 162 418), lower := (rows 35 194 28 73 276 33 64 128 256), losses := [] }

theorem u20475 : Upper (D 7) (R 7) [34,192,24,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20476 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 73 276 34 225 161 417), lower := (rows 35 194 28 73 276 34 64 128 256), losses := [] }

theorem u20476 : Upper (D 7) (R 7) [34,192,24,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20477 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 73 276 160 99 163 291), lower := (rows 35 194 28 73 276 160 64 128 256), losses := [] }

theorem u20477 : Upper (D 7) (R 7) [34,192,24,65,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20478 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 2, region := 194, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7)], upper := (rows 35 194 28 73 304 33 198 134 390), lower := (rows 35 194 28 73 304 33 64 128 256), losses := [] }

theorem u20478 : Upper (D 7) (R 7) [34,192,24,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20479 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 73 304 34 197 133 389), lower := (rows 35 194 28 73 304 34 64 128 256), losses := [] }

theorem u20479 : Upper (D 7) (R 7) [34,192,24,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20480 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,5),(3,5),(4,6)], upper := (rows 35 194 28 73 304 36 195 131 387), lower := (rows 35 194 28 73 304 36 64 128 256), losses := [] }

theorem u20480 : Upper (D 7) (R 7) [34,192,24,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20480 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20481 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 73 304 160 71 135 263), lower := (rows 35 194 28 73 304 160 64 128 256), losses := [] }

theorem u20481 : Upper (D 7) (R 7) [34,192,24,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20482 : Route 9 := (fun mask => (mask,id))

def c20482 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20482 : Upper (D 7) (R 7) [34,192,24,65,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,384,1] 13 (by decide) (choices 1) [2,4,32] r20482 c20482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5706
  · exact u5707
  · exact u5708

def b20483 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 73 400 34 101 165 293), lower := (rows 35 194 28 73 400 34 64 128 256), losses := [] }

theorem u20483 : Upper (D 7) (R 7) [34,192,24,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20484 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 400, targets := 64 },{ cop := 0, region := 72, targets := 128 }], pairs := [(2,6),(3,7),(4,6)], upper := (rows 35 194 28 73 400 36 99 163 291), lower := (rows 35 194 28 73 400 36 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 25 44 0 129 257), good := (rows 435 130 60 445 400 36 0 128 256) }] }

theorem u20484 : Upper (D 7) (R 7) [34,192,24,65,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20484 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20485 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 194, targets := 1 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,6)], upper := (rows 35 194 28 76 273 33 226 162 418), lower := (rows 35 194 28 76 273 33 64 128 256), losses := [] }

theorem u20485 : Upper (D 7) (R 7) [34,192,24,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20486 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 76 273 34 225 161 417), lower := (rows 35 194 28 76 273 34 64 128 256), losses := [] }

theorem u20486 : Upper (D 7) (R 7) [34,192,24,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20487 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 76 273 160 99 163 291), lower := (rows 35 194 28 76 273 160 64 128 256), losses := [] }

theorem u20487 : Upper (D 7) (R 7) [34,192,24,68,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20488 : Route 9 := (fun mask => (mask,id))

def c20488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20488 : Upper (D 7) (R 7) [34,192,24,68,258,1] 13 := by
  apply FastRouting.sound _ _ [34,192,24,68,258,1] 13 (by decide) (choices 1) [1,32,128] r20488 c20488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5709
  · exact u5710
  · exact u5711

def b20489 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 76 274 160 97 161 289), lower := (rows 35 194 28 76 274 160 64 128 256), losses := [] }

theorem u20489 : Upper (D 7) (R 7) [34,192,24,68,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20490 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(4,6)], upper := (rows 35 194 28 76 304 33 195 131 387), lower := (rows 35 194 28 76 304 33 64 128 256), losses := [] }

theorem u20490 : Upper (D 7) (R 7) [34,192,24,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20491 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 76 304 34 193 129 385), lower := (rows 35 194 28 76 304 34 64 128 256), losses := [] }

theorem u20491 : Upper (D 7) (R 7) [34,192,24,68,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20492 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 76 304 160 67 131 259), lower := (rows 35 194 28 76 304 160 64 128 256), losses := [] }

theorem u20492 : Upper (D 7) (R 7) [34,192,24,68,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20493 : Route 9 := (fun mask => (mask,id))

def c20493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20493 : Upper (D 7) (R 7) [34,192,24,68,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,24,68,384,1] 13 (by decide) (choices 1) [1,2,32] r20493 c20493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5712
  · exact u5713
  · exact u5714

def b20494 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 76 400 34 97 161 289), lower := (rows 35 194 28 76 400 34 64 128 256), losses := [] }

theorem u20494 : Upper (D 7) (R 7) [34,192,24,68,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20495 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 2, region := 194, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7)], upper := (rows 35 194 28 104 273 33 198 134 390), lower := (rows 35 194 28 104 273 33 64 128 256), losses := [] }

theorem u20495 : Upper (D 7) (R 7) [34,192,24,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20496 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 104 273 34 197 133 389), lower := (rows 35 194 28 104 273 34 64 128 256), losses := [] }

theorem u20496 : Upper (D 7) (R 7) [34,192,24,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20497 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,5),(4,5),(4,6)], upper := (rows 35 194 28 104 273 36 195 131 387), lower := (rows 35 194 28 104 273 36 64 128 256), losses := [] }

theorem u20497 : Upper (D 7) (R 7) [34,192,24,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20497 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20498 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(2,7),(3,0),(3,7),(4,7)], upper := (rows 35 194 28 104 273 160 71 135 263), lower := (rows 35 194 28 104 273 160 64 128 256), losses := [] }

theorem u20498 : Upper (D 7) (R 7) [34,192,24,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20499 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 28 104 274 33 197 133 389), lower := (rows 35 194 28 104 274 33 64 128 256), losses := [{ target := 7, region := (rows 19 2 20 10 16 55 64 0 256), good := (rows 43 107 61 104 319 33 64 0 256) }] }

theorem u20499 : Upper (D 7) (R 7) [34,192,24,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20500 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,5),(3,1),(4,5)], upper := (rows 35 194 28 104 274 36 193 129 385), lower := (rows 35 194 28 104 274 36 64 128 256), losses := [] }

theorem u20500 : Upper (D 7) (R 7) [34,192,24,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20500 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20501 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(2,7),(3,0),(3,7),(4,7)], upper := (rows 35 194 28 104 274 160 69 133 261), lower := (rows 35 194 28 104 274 160 64 128 256), losses := [] }

theorem u20501 : Upper (D 7) (R 7) [34,192,24,96,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20502 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(3,7)], upper := (rows 35 194 28 104 276 33 195 131 387), lower := (rows 35 194 28 104 276 33 64 128 256), losses := [] }

theorem u20502 : Upper (D 7) (R 7) [34,192,24,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20503 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 104 276 34 193 129 385), lower := (rows 35 194 28 104 276 34 64 128 256), losses := [] }

theorem u20503 : Upper (D 7) (R 7) [34,192,24,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20504 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 104 276 160 67 131 259), lower := (rows 35 194 28 104 276 160 64 128 256), losses := [] }

theorem u20504 : Upper (D 7) (R 7) [34,192,24,96,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20505 : Route 9 := (fun mask => (mask,id))

def c20505 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20505 : Upper (D 7) (R 7) [34,192,24,96,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,384,1] 13 (by decide) (choices 1) [1,2,4] r20505 c20505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5715
  · exact u5716
  · exact u5717

def b20506 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 104 400 34 69 133 261), lower := (rows 35 194 28 104 400 34 64 128 256), losses := [] }

theorem u20506 : Upper (D 7) (R 7) [34,192,24,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20507 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,5),(4,5),(4,6)], upper := (rows 35 194 28 104 400 36 67 131 259), lower := (rows 35 194 28 104 400 36 64 128 256), losses := [] }

theorem u20507 : Upper (D 7) (R 7) [34,192,24,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20507 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20508 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 73 145 34 340 404 276), lower := (rows 35 194 44 73 145 34 64 128 256), losses := [] }

theorem u20508 : Upper (D 7) (R 7) [34,192,40,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20509 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 73 145 36 338 402 274), lower := (rows 35 194 44 73 145 36 64 128 256), losses := [] }

theorem u20509 : Upper (D 7) (R 7) [34,192,40,65,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20509 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20510 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 44 73 145 48 326 390 262), lower := (rows 35 194 44 73 145 48 64 128 256), losses := [] }

theorem u20510 : Upper (D 7) (R 7) [34,192,40,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20510 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20511 : Route 9 := (fun mask => (mask,id))

def c20511 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20511 : Upper (D 7) (R 7) [34,192,40,65,129,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,129,256] 13 (by decide) (choices 1) [2,4,16] r20511 c20511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5718
  · exact u5719
  · exact u5720

def b20512 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 44 73 148 33 338 402 274), lower := (rows 35 194 44 73 148 33 64 128 256), losses := [] }

theorem u20512 : Upper (D 7) (R 7) [34,192,40,65,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20513 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 73 148 34 337 401 273), lower := (rows 35 194 44 73 148 34 64 128 256), losses := [] }

theorem u20513 : Upper (D 7) (R 7) [34,192,40,65,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20514 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 332, targets := 128 }], pairs := [(1,5),(2,7),(3,5)], upper := (rows 35 194 44 73 148 48 323 387 259), lower := (rows 35 194 44 73 148 48 64 128 256), losses := [] }

theorem u20514 : Upper (D 7) (R 7) [34,192,40,65,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20514 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20515 : Route 9 := (fun mask => (mask,id))

def c20515 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20515 : Upper (D 7) (R 7) [34,192,40,65,132,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,132,256] 13 (by decide) (choices 1) [1,2,16] r20515 c20515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5721
  · exact u5722
  · exact u5723

def b20516 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 73 273 34 212 148 404), lower := (rows 35 194 44 73 273 34 64 128 256), losses := [] }

theorem u20516 : Upper (D 7) (R 7) [34,192,40,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20517 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 73 273 36 210 146 402), lower := (rows 35 194 44 73 273 36 64 128 256), losses := [] }

theorem u20517 : Upper (D 7) (R 7) [34,192,40,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20517 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20518 : Route 9 := (fun mask => (mask,id))

def c20518 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20518 : Upper (D 7) (R 7) [34,192,40,65,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,257,16] 13 (by decide) (choices 1) [2,4,128] r20518 c20518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5724
  · exact u5725
  · exact u5726

def b20519 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 73 273 160 86 150 278), lower := (rows 35 194 44 73 273 160 64 128 256), losses := [] }

theorem u20519 : Upper (D 7) (R 7) [34,192,40,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20519
end Delivery.IrregularNine14.P07
