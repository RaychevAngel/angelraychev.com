import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0101

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20460 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(3,2),(4,2)], upper := (rows 35 70 140 25 304 36 67 195 323), lower := (rows 35 70 140 25 304 36 64 128 256), losses := [] }

theorem u20460 : Upper (D 6) (R 6) [34,68,136,17,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20461 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 25 304 96 71 135 263), lower := (rows 35 70 140 25 304 96 64 128 256), losses := [] }

theorem u20461 : Upper (D 6) (R 6) [34,68,136,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20462 : Route 9 := (fun mask => (mask,id))

def c20462 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20462 : Upper (D 6) (R 6) [34,68,136,17,320,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,320,1] 13 (by decide) (choices 1) [2,4,32] r20462 c20462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6072
  · exact u6073
  · exact u6074

def b20463 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 25 336 34 101 165 293), lower := (rows 35 70 140 25 336 34 64 128 256), losses := [] }

theorem u20463 : Upper (D 6) (R 6) [34,68,136,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20464 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 140 25 336 36 99 163 291), lower := (rows 35 70 140 25 336 36 64 128 256), losses := [] }

theorem u20464 : Upper (D 6) (R 6) [34,68,136,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20465 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 70 140 26 21 33 352 480 352), lower := (rows 35 70 140 26 21 33 64 128 256), losses := [] }

theorem u20465 : Upper (D 6) (R 6) [34,68,136,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20466 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 26 21 96 353 417 289), lower := (rows 35 70 140 26 21 96 64 128 256), losses := [] }

theorem u20466 : Upper (D 6) (R 6) [34,68,136,18,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20467 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(2,1)], upper := (rows 35 70 140 26 21 288 97 225 353), lower := (rows 35 70 140 26 21 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 313 81 145 273), good := (rows 481 68 172 508 501 288 64 128 288) }] }

theorem u20467 : Upper (D 6) (R 6) [34,68,136,18,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20467 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20468 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 70 140 26 52 33 321 449 321), lower := (rows 35 70 140 26 52 33 64 128 256), losses := [] }

theorem u20468 : Upper (D 6) (R 6) [34,68,136,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20469 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 26 52 96 321 385 257), lower := (rows 35 70 140 26 52 96 64 128 256), losses := [] }

theorem u20469 : Upper (D 6) (R 6) [34,68,136,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20470 : Route 9 := (fun mask => (mask,id))

def c20470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20470 : Upper (D 6) (R 6) [34,68,136,18,36,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,36,256] 13 (by decide) (choices 1) [1] r20470 c20470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u6075

def b20471 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 140 26 81 33 356 420 292), lower := (rows 35 70 140 26 81 33 64 128 256), losses := [] }

theorem u20471 : Upper (D 6) (R 6) [34,68,136,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20472 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 140 26 81 36 353 417 289), lower := (rows 35 70 140 26 81 36 64 128 256), losses := [] }

theorem u20472 : Upper (D 6) (R 6) [34,68,136,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20473 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 140 26 81 288 101 165 293), lower := (rows 35 70 140 26 81 288 64 128 256), losses := [] }

theorem u20473 : Upper (D 6) (R 6) [34,68,136,18,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20473 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20474 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 140 26 112 33 325 389 261), lower := (rows 35 70 140 26 112 33 64 128 256), losses := [] }

theorem u20474 : Upper (D 6) (R 6) [34,68,136,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20475 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 56, targets := 1 }], pairs := [(3,0),(3,2),(4,2)], upper := (rows 35 70 140 26 112 36 321 385 257), lower := (rows 35 70 140 26 112 36 64 128 256), losses := [] }

theorem u20475 : Upper (D 6) (R 6) [34,68,136,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20476 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 140 26 112 288 69 133 261), lower := (rows 35 70 140 26 112 288 64 128 256), losses := [] }

theorem u20476 : Upper (D 6) (R 6) [34,68,136,18,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20476 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20477 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 70 140 26 273 33 100 228 356), lower := (rows 35 70 140 26 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 72 136 264), good := (rows 33 68 460 508 305 33 64 128 256) }] }

theorem u20477 : Upper (D 6) (R 6) [34,68,136,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20478 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 336, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 35 70 140 26 273 36 97 225 353), lower := (rows 35 70 140 26 273 36 64 128 256), losses := [] }

theorem u20478 : Upper (D 6) (R 6) [34,68,136,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20479 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 26 273 96 101 165 293), lower := (rows 35 70 140 26 273 96 64 128 256), losses := [] }

theorem u20479 : Upper (D 6) (R 6) [34,68,136,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20480 : Route 9 := (fun mask => (mask,id))

def c20480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20480 : Upper (D 6) (R 6) [34,68,136,18,260,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,260,1] 13 (by decide) (choices 1) [1,32] r20480 c20480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6076
  · exact u6077

def b20481 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 26 276 96 97 161 289), lower := (rows 35 70 140 26 276 96 64 128 256), losses := [] }

theorem u20481 : Upper (D 6) (R 6) [34,68,136,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20482 : Route 9 := (fun mask => (mask,id))

def c20482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20482 : Upper (D 6) (R 6) [34,68,136,18,288,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,288,1] 13 (by decide) (choices 1) [1,4] r20482 c20482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6078
  · exact u6079

def b20483 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 336, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 35 70 140 26 304 36 65 193 321), lower := (rows 35 70 140 26 304 36 64 128 256), losses := [] }

theorem u20483 : Upper (D 6) (R 6) [34,68,136,18,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20484 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 26 304 96 69 133 261), lower := (rows 35 70 140 26 304 96 64 128 256), losses := [] }

theorem u20484 : Upper (D 6) (R 6) [34,68,136,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20485 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 140 26 336 33 101 165 293), lower := (rows 35 70 140 26 336 33 64 128 256), losses := [] }

theorem u20485 : Upper (D 6) (R 6) [34,68,136,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20486 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 140 26 336 36 97 161 289), lower := (rows 35 70 140 26 336 36 64 128 256), losses := [] }

theorem u20486 : Upper (D 6) (R 6) [34,68,136,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20487 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 28 273 33 98 226 354), lower := (rows 35 70 140 28 273 33 64 128 256), losses := [] }

theorem u20487 : Upper (D 6) (R 6) [34,68,136,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20488 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 28 273 34 97 225 353), lower := (rows 35 70 140 28 273 34 64 128 256), losses := [] }

theorem u20488 : Upper (D 6) (R 6) [34,68,136,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20489 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 28 273 96 99 163 291), lower := (rows 35 70 140 28 273 96 64 128 256), losses := [] }

theorem u20489 : Upper (D 6) (R 6) [34,68,136,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20490 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 28 274 33 97 225 353), lower := (rows 35 70 140 28 274 33 64 128 256), losses := [] }

theorem u20490 : Upper (D 6) (R 6) [34,68,136,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20491 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 28 274 96 97 161 289), lower := (rows 35 70 140 28 274 96 64 128 256), losses := [] }

theorem u20491 : Upper (D 6) (R 6) [34,68,136,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20492 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 28 304 33 67 195 323), lower := (rows 35 70 140 28 304 33 64 128 256), losses := [] }

theorem u20492 : Upper (D 6) (R 6) [34,68,136,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20493 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 28 304 34 65 193 321), lower := (rows 35 70 140 28 304 34 64 128 256), losses := [] }

theorem u20493 : Upper (D 6) (R 6) [34,68,136,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20494 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 28 304 96 67 131 259), lower := (rows 35 70 140 28 304 96 64 128 256), losses := [] }

theorem u20494 : Upper (D 6) (R 6) [34,68,136,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20495 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 140 56 81 33 326 390 262), lower := (rows 35 70 140 56 81 33 64 128 256), losses := [] }

theorem u20495 : Upper (D 6) (R 6) [34,68,136,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20496 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 56 81 34 325 389 261), lower := (rows 35 70 140 56 81 34 64 128 256), losses := [] }

theorem u20496 : Upper (D 6) (R 6) [34,68,136,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20497 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 70 140 56 81 36 323 387 259), lower := (rows 35 70 140 56 81 36 64 128 256), losses := [] }

theorem u20497 : Upper (D 6) (R 6) [34,68,136,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20498 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 140 56 81 288 71 135 263), lower := (rows 35 70 140 56 81 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 24 16 291 0 130 258), good := (rows 419 423 140 56 57 288 0 128 288) }] }

theorem u20498 : Upper (D 6) (R 6) [34,68,136,48,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20498 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20499 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 140 56 273 33 70 198 326), lower := (rows 35 70 140 56 273 33 64 128 256), losses := [] }

theorem u20499 : Upper (D 6) (R 6) [34,68,136,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20500 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 56 273 34 69 197 325), lower := (rows 35 70 140 56 273 34 64 128 256), losses := [] }

theorem u20500 : Upper (D 6) (R 6) [34,68,136,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20501 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 70 140 56 273 36 67 195 323), lower := (rows 35 70 140 56 273 36 64 128 256), losses := [] }

theorem u20501 : Upper (D 6) (R 6) [34,68,136,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20502 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 56 273 96 71 135 263), lower := (rows 35 70 140 56 273 96 64 128 256), losses := [] }

theorem u20502 : Upper (D 6) (R 6) [34,68,136,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20503 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 140 56 274 33 69 197 325), lower := (rows 35 70 140 56 274 33 64 128 256), losses := [] }

theorem u20503 : Upper (D 6) (R 6) [34,68,136,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20504 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 70 140 56 274 36 65 193 321), lower := (rows 35 70 140 56 274 36 64 128 256), losses := [] }

theorem u20504 : Upper (D 6) (R 6) [34,68,136,48,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20505 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 56 274 96 69 133 261), lower := (rows 35 70 140 56 274 96 64 128 256), losses := [] }

theorem u20505 : Upper (D 6) (R 6) [34,68,136,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20506 : Route 9 := (fun mask => (mask,id))

def c20506 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20506 : Upper (D 6) (R 6) [34,68,136,48,260,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,260,1] 13 (by decide) (choices 1) [1,2] r20506 c20506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6080
  · exact u6081

def b20507 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 56 276 34 65 193 321), lower := (rows 35 70 140 56 276 34 64 128 256), losses := [] }

theorem u20507 : Upper (D 6) (R 6) [34,68,136,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20508 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 56 276 96 67 131 259), lower := (rows 35 70 140 56 276 96 64 128 256), losses := [] }

theorem u20508 : Upper (D 6) (R 6) [34,68,136,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20509 : Route 9 := (fun mask => (mask,id))

def c20509 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20509 : Upper (D 6) (R 6) [34,68,136,48,320,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,320,1] 13 (by decide) (choices 1) [1,2,4] r20509 c20509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6082
  · exact u6083
  · exact u6084

def b20510 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 56 336 34 69 133 261), lower := (rows 35 70 140 56 336 34 64 128 256), losses := [] }

theorem u20510 : Upper (D 6) (R 6) [34,68,136,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20511 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 70 140 56 336 36 67 131 259), lower := (rows 35 70 140 56 336 36 64 128 256), losses := [] }

theorem u20511 : Upper (D 6) (R 6) [34,68,136,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20512 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 73 273 34 116 180 308), lower := (rows 35 70 140 73 273 34 64 128 256), losses := [] }

theorem u20512 : Upper (D 6) (R 6) [34,68,136,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20513 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 140 73 273 36 114 178 306), lower := (rows 35 70 140 73 273 36 64 128 256), losses := [] }

theorem u20513 : Upper (D 6) (R 6) [34,68,136,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20514 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 73 273 48 102 166 294), lower := (rows 35 70 140 73 273 48 64 128 256), losses := [] }

theorem u20514 : Upper (D 6) (R 6) [34,68,136,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20514 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20515 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 140 73 304 33 86 150 278), lower := (rows 35 70 140 73 304 33 64 128 256), losses := [] }

theorem u20515 : Upper (D 6) (R 6) [34,68,136,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20516 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 73 304 34 85 149 277), lower := (rows 35 70 140 73 304 34 64 128 256), losses := [] }

theorem u20516 : Upper (D 6) (R 6) [34,68,136,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20517 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 140 73 304 36 83 147 275), lower := (rows 35 70 140 73 304 36 64 128 256), losses := [] }

theorem u20517 : Upper (D 6) (R 6) [34,68,136,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20518 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 140 73 304 48 71 135 263), lower := (rows 35 70 140 73 304 48 64 128 256), losses := [] }

theorem u20518 : Upper (D 6) (R 6) [34,68,136,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20518 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20519 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 140 88 273 33 102 166 294), lower := (rows 35 70 140 88 273 33 64 128 256), losses := [] }

theorem u20519 : Upper (D 6) (R 6) [34,68,136,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20519
end Delivery.IrregularNine14.P06
