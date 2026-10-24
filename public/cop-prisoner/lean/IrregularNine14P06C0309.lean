import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0089
import IrregularNine14P06C0090

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18540 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 14 82 33 356 420 292), lower := (rows 25 35 196 14 82 33 64 128 256), losses := [] }

theorem u18540 : Upper (D 6) (R 6) [24,33,192,6,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18541 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 1, region := 336, targets := 4 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 25 35 196 14 82 36 353 417 289), lower := (rows 25 35 196 14 82 36 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 26 32 66 130 258), good := (rows 25 499 192 475 466 32 64 128 256) }] }

theorem u18541 : Upper (D 6) (R 6) [24,33,192,6,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18542 : Route 9 := (fun mask => (mask,id))

def c18542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18542 : Upper (D 6) (R 6) [24,33,192,6,66,256] 13 := by
  apply FastRouting.sound _ _ [24,33,192,6,66,256] 13 (by decide) (choices 1) [1,4,32] r18542 c18542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5390
  · exact u5391
  · exact u5392

def b18543 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 14 112 33 326 390 262), lower := (rows 25 35 196 14 112 33 64 128 256), losses := [] }

theorem u18543 : Upper (D 6) (R 6) [24,33,192,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18544 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 196 14 112 34 325 389 261), lower := (rows 25 35 196 14 112 34 64 128 256), losses := [] }

theorem u18544 : Upper (D 6) (R 6) [24,33,192,6,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18545 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 460, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(2,5),(3,5),(4,0)], upper := (rows 25 35 196 14 112 36 323 387 259), lower := (rows 25 35 196 14 112 36 64 128 256), losses := [] }

theorem u18545 : Upper (D 6) (R 6) [24,33,192,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18546 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 204, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 25 35 196 14 112 288 71 135 263), lower := (rows 25 35 196 14 112 288 64 128 256), losses := [] }

theorem u18546 : Upper (D 6) (R 6) [24,33,192,6,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18546 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18547 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 196 14 273 34 100 228 356), lower := (rows 25 35 196 14 273 34 64 128 256), losses := [] }

theorem u18547 : Upper (D 6) (R 6) [24,33,192,6,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18548 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 336, targets := 4 }], pairs := [(2,0),(3,0),(4,2)], upper := (rows 25 35 196 14 273 36 98 226 354), lower := (rows 25 35 196 14 273 36 64 128 256), losses := [] }

theorem u18548 : Upper (D 6) (R 6) [24,33,192,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18549 : Route 9 := (fun mask => (mask,id))

def c18549 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18549 : Upper (D 6) (R 6) [24,33,192,6,257,64] 13 := by
  apply FastRouting.sound _ _ [24,33,192,6,257,64] 13 (by decide) (choices 1) [2,4,32] r18549 c18549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5393
  · exact u5394
  · exact u5395

def b18550 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 14 274 33 100 228 356), lower := (rows 25 35 196 14 274 33 64 128 256), losses := [] }

theorem u18550 : Upper (D 6) (R 6) [24,33,192,6,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18551 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 1, region := 336, targets := 4 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 25 35 196 14 274 36 97 225 353), lower := (rows 25 35 196 14 274 36 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 26 32 66 130 258), good := (rows 25 499 192 475 466 32 64 128 256) }] }

theorem u18551 : Upper (D 6) (R 6) [24,33,192,6,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18552 : Route 9 := (fun mask => (mask,id))

def c18552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18552 : Upper (D 6) (R 6) [24,33,192,6,258,64] 13 := by
  apply FastRouting.sound _ _ [24,33,192,6,258,64] 13 (by decide) (choices 1) [1,4,32] r18552 c18552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5396
  · exact u5397
  · exact u5398

def b18553 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 14 276 33 98 226 354), lower := (rows 25 35 196 14 276 33 64 128 256), losses := [] }

theorem u18553 : Upper (D 6) (R 6) [24,33,192,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18554 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 196 14 276 34 97 225 353), lower := (rows 25 35 196 14 276 34 64 128 256), losses := [] }

theorem u18554 : Upper (D 6) (R 6) [24,33,192,6,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18555 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 98, targets := 4 }], pairs := [(0,6),(1,2),(4,6)], upper := (rows 25 35 196 14 276 96 99 163 291), lower := (rows 25 35 196 14 276 96 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 24 32 0 130 258), good := (rows 25 419 132 415 276 32 0 128 256) }] }

theorem u18555 : Upper (D 6) (R 6) [24,33,192,6,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18556 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 14 304 33 70 198 326), lower := (rows 25 35 196 14 304 33 64 128 256), losses := [] }

theorem u18556 : Upper (D 6) (R 6) [24,33,192,6,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18557 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 196 14 304 34 69 197 325), lower := (rows 25 35 196 14 304 34 64 128 256), losses := [] }

theorem u18557 : Upper (D 6) (R 6) [24,33,192,6,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18558 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 1, region := 336, targets := 4 }], pairs := [(2,5),(3,5),(4,2)], upper := (rows 25 35 196 14 304 36 67 195 323), lower := (rows 25 35 196 14 304 36 64 128 256), losses := [] }

theorem u18558 : Upper (D 6) (R 6) [24,33,192,6,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18559 : Route 9 := (fun mask => (mask,id))

def c18559 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18559 : Upper (D 6) (R 6) [24,33,192,6,288,64] 13 := by
  apply FastRouting.sound _ _ [24,33,192,6,288,64] 13 (by decide) (choices 1) [1,2,4] r18559 c18559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5399
  · exact u5400
  · exact u5401

def b18560 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 14 336 33 102 166 294), lower := (rows 25 35 196 14 336 33 64 128 256), losses := [] }

theorem u18560 : Upper (D 6) (R 6) [24,33,192,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18561 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 196 14 336 34 101 165 293), lower := (rows 25 35 196 14 336 34 64 128 256), losses := [] }

theorem u18561 : Upper (D 6) (R 6) [24,33,192,6,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18562 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 336, targets := 4 }], pairs := [(0,2),(1,6),(4,2)], upper := (rows 25 35 196 14 336 36 99 163 291), lower := (rows 25 35 196 14 336 36 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 26 32 66 130 258), good := (rows 25 499 192 475 336 32 64 128 256) },{ target := 6, region := (rows 1 3 4 8 16 44 0 131 259), good := (rows 443 419 164 430 272 36 0 128 256) }] }

theorem u18562 : Upper (D 6) (R 6) [24,33,192,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18563 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 44 82 33 326 390 262), lower := (rows 25 35 196 44 82 33 64 128 256), losses := [] }

theorem u18563 : Upper (D 6) (R 6) [24,33,192,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18564 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 196 44 82 34 325 389 261), lower := (rows 25 35 196 44 82 34 64 128 256), losses := [] }

theorem u18564 : Upper (D 6) (R 6) [24,33,192,36,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18565 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 35 196 44 82 36 323 387 259), lower := (rows 25 35 196 44 82 36 64 128 256), losses := [] }

theorem u18565 : Upper (D 6) (R 6) [24,33,192,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18566 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 25 35 196 44 82 288 71 135 263), lower := (rows 25 35 196 44 82 288 64 128 256), losses := [] }

theorem u18566 : Upper (D 6) (R 6) [24,33,192,36,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18566 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18567 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 44 274 33 70 198 326), lower := (rows 25 35 196 44 274 33 64 128 256), losses := [] }

theorem u18567 : Upper (D 6) (R 6) [24,33,192,36,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18568 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 196 44 274 34 69 197 325), lower := (rows 25 35 196 44 274 34 64 128 256), losses := [] }

theorem u18568 : Upper (D 6) (R 6) [24,33,192,36,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18569 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 35 196 44 274 36 67 195 323), lower := (rows 25 35 196 44 274 36 64 128 256), losses := [] }

theorem u18569 : Upper (D 6) (R 6) [24,33,192,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18570 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 275, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 25 35 196 44 274 96 71 135 263), lower := (rows 25 35 196 44 274 96 64 128 256), losses := [] }

theorem u18570 : Upper (D 6) (R 6) [24,33,192,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18571 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 44 336 33 70 134 262), lower := (rows 25 35 196 44 336 33 64 128 256), losses := [] }

theorem u18571 : Upper (D 6) (R 6) [24,33,192,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18572 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,2),(1,6),(2,5)], upper := (rows 25 35 196 44 336 34 71 135 263), lower := (rows 25 35 196 44 336 34 64 128 256), losses := [] }

theorem u18572 : Upper (D 6) (R 6) [24,33,192,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18573 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 35 196 44 336 36 67 131 259), lower := (rows 25 35 196 44 336 36 64 128 256), losses := [] }

theorem u18573 : Upper (D 6) (R 6) [24,33,192,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18574 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 196 73 274 34 100 164 292), lower := (rows 25 35 196 73 274 34 64 128 256), losses := [] }

theorem u18574 : Upper (D 6) (R 6) [24,33,192,65,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18575 : Route 9 := (fun mask => (mask,id))

def c18575 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18575 : Upper (D 6) (R 6) [24,33,192,65,258,4] 13 := by
  apply FastRouting.sound _ _ [24,33,192,65,258,4] 13 (by decide) (choices 1) [2,4,32] r18575 c18575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5402
  · exact u5403
  · exact u5404

def b18576 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 196 73 276 34 102 166 294), lower := (rows 25 35 196 73 276 34 64 128 256), losses := [] }

theorem u18576 : Upper (D 6) (R 6) [24,33,192,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18577 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 72, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 196 73 276 36 98 162 290), lower := (rows 25 35 196 73 276 36 64 128 256), losses := [] }

theorem u18577 : Upper (D 6) (R 6) [24,33,192,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18578 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 196 74 273 34 100 164 292), lower := (rows 25 35 196 74 273 34 64 128 256), losses := [] }

theorem u18578 : Upper (D 6) (R 6) [24,33,192,66,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18579 : Route 9 := (fun mask => (mask,id))

def c18579 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18579 : Upper (D 6) (R 6) [24,33,192,66,257,4] 13 := by
  apply FastRouting.sound _ _ [24,33,192,66,257,4] 13 (by decide) (choices 1) [2,4,32] r18579 c18579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5405
  · exact u5406
  · exact u5407

def b18580 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 74 274 33 100 164 292), lower := (rows 25 35 196 74 274 33 64 128 256), losses := [] }

theorem u18580 : Upper (D 6) (R 6) [24,33,192,66,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18581 : Route 9 := (fun mask => (mask,id))

def c18581 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18581 : Upper (D 6) (R 6) [24,33,192,66,258,4] 13 := by
  apply FastRouting.sound _ _ [24,33,192,66,258,4] 13 (by decide) (choices 1) [1,4,32] r18581 c18581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5408
  · exact u5409
  · exact u5410

def b18582 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 74 276 33 102 166 294), lower := (rows 25 35 196 74 276 33 64 128 256), losses := [] }

theorem u18582 : Upper (D 6) (R 6) [24,33,192,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18583 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 196 74 276 34 101 165 293), lower := (rows 25 35 196 74 276 34 64 128 256), losses := [] }

theorem u18583 : Upper (D 6) (R 6) [24,33,192,66,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18584 : Route 9 := (fun mask => (mask,id))

def c18584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18584 : Upper (D 6) (R 6) [24,33,192,66,260,4] 13 := by
  apply FastRouting.sound _ _ [24,33,192,66,260,4] 13 (by decide) (choices 1) [1,2,32] r18584 c18584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5411
  · exact u5412
  · exact u5413

def b18585 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 74 304 33 70 134 262), lower := (rows 25 35 196 74 304 33 64 128 256), losses := [] }

theorem u18585 : Upper (D 6) (R 6) [24,33,192,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18586 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 196 74 304 34 69 133 261), lower := (rows 25 35 196 74 304 34 64 128 256), losses := [] }

theorem u18586 : Upper (D 6) (R 6) [24,33,192,66,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18587 : Route 9 := (fun mask => (mask,id))

def c18587 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18587 : Upper (D 6) (R 6) [24,33,192,66,288,4] 13 := by
  apply FastRouting.sound _ _ [24,33,192,66,288,4] 13 (by decide) (choices 1) [1,2,4] r18587 c18587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5414
  · exact u5415
  · exact u5416

def b18588 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 104 274 33 70 134 262), lower := (rows 25 35 196 104 274 33 64 128 256), losses := [] }

theorem u18588 : Upper (D 6) (R 6) [24,33,192,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18589 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 196 104 274 34 69 133 261), lower := (rows 25 35 196 104 274 34 64 128 256), losses := [] }

theorem u18589 : Upper (D 6) (R 6) [24,33,192,96,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18590 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 25 35 196 104 274 36 71 135 263), lower := (rows 25 35 196 104 274 36 64 128 256), losses := [] }

theorem u18590 : Upper (D 6) (R 6) [24,33,192,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18591 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 196 104 276 33 70 134 262), lower := (rows 25 35 196 104 276 33 64 128 256), losses := [] }

theorem u18591 : Upper (D 6) (R 6) [24,33,192,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18592 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,2),(1,6),(2,5)], upper := (rows 25 35 196 104 276 34 71 135 263), lower := (rows 25 35 196 104 276 34 64 128 256), losses := [] }

theorem u18592 : Upper (D 6) (R 6) [24,33,192,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18593 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 25 35 196 104 276 36 67 131 259), lower := (rows 25 35 196 104 276 36 64 128 256), losses := [] }

theorem u18593 : Upper (D 6) (R 6) [24,33,192,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18594 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 388 13 82 34 100 228 356), lower := (rows 25 35 388 13 82 34 64 128 256), losses := [] }

theorem u18594 : Upper (D 6) (R 6) [24,33,384,5,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18595 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 80, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 35 388 13 82 36 98 226 354), lower := (rows 25 35 388 13 82 36 64 128 256), losses := [] }

theorem u18595 : Upper (D 6) (R 6) [24,33,384,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18596 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 388, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 25 35 388 13 82 96 102 166 294), lower := (rows 25 35 388 13 82 96 64 128 256), losses := [] }

theorem u18596 : Upper (D 6) (R 6) [24,33,384,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18597 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 388 14 81 34 100 228 356), lower := (rows 25 35 388 14 81 34 64 128 256), losses := [] }

theorem u18597 : Upper (D 6) (R 6) [24,33,384,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18598 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 1, region := 80, targets := 4 }], pairs := [(2,0),(3,0),(4,2)], upper := (rows 25 35 388 14 81 36 98 226 354), lower := (rows 25 35 388 14 81 36 64 128 256), losses := [] }

theorem u18598 : Upper (D 6) (R 6) [24,33,384,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18599 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 396, targets := 1 },{ cop := 1, region := 388, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 25 35 388 14 81 96 102 166 294), lower := (rows 25 35 388 14 81 96 64 128 256), losses := [] }

theorem u18599 : Upper (D 6) (R 6) [24,33,384,6,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u18599
end Delivery.IrregularNine14.P06
