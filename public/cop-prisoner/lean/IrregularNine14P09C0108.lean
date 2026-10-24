import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0046

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m6480_1 : Upper (D 9) (R 9) [96,36,136,80,130,256,1] 13 :=
  permutation_upper _ _ _ [96,36,136,80,130,1,256] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2781

def r6480 : Route 9 := (fun mask => (mask,id))

def c6480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6480 : Upper (D 9) (R 9) [96,36,136,80,130,256] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,130,256] 13 (by decide) (choices 1) [1,256] r6480 c6480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6480_1
  · exact u2782

def b6481 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 140 88 274 33 449 385 385), lower := (rows 97 38 140 88 274 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 97 161 289), good := (rows 449 478 140 88 286 449 64 128 256) }] }

theorem u6481 : Upper (D 9) (R 9) [96,36,136,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6481 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6482 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 140 88 274 160 321 385 257), lower := (rows 97 38 140 88 274 160 64 128 256), losses := [] }

theorem u6482 : Upper (D 9) (R 9) [96,36,136,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6482 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6483_1 : Upper (D 9) (R 9) [96,36,136,80,258,256,1] 13 :=
  permutation_upper _ _ _ [96,36,136,80,258,1,128] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2783

def r6483 : Route 9 := (fun mask => (mask,id))

def c6483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6483 : Upper (D 9) (R 9) [96,36,136,80,258,256] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,258,256] 13 (by decide) (choices 1) [1,128] r6483 c6483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6483_1
  · exact u2784

def r6484 : Route 9 := (fun mask => (mask,id))

def c6484 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6484 : Upper (D 9) (R 9) [96,36,136,80,384,1] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,384,1] 13 (by decide) (choices 1) [1,2,256] r6484 c6484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2785
  · exact u2786
  · exact u2787

def b6485 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,5),(3,5),(4,5)], upper := (rows 97 38 140 88 400 34 321 385 257), lower := (rows 97 38 140 88 400 34 64 128 256), losses := [] }

theorem u6485 : Upper (D 9) (R 9) [96,36,136,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6485 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6486 : Route 9 := (fun mask => (mask,id))

def c6486 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6486 : Upper (D 9) (R 9) [96,36,136,80,384,256] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,384,256] 13 (by decide) (choices 1) [1,2] r6486 c6486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2788
  · exact u2789

def b6487 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 140 265 145 34 336 464 336), lower := (rows 97 38 140 265 145 34 64 128 256), losses := [] }

theorem u6487 : Upper (D 9) (R 9) [96,36,136,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6487 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6488 : Route 9 := (fun mask => (mask,id))

def c6488 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6488 : Upper (D 9) (R 9) [96,36,136,257,129,16] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,129,16] 13 (by decide) (choices 1) [2,256] r6488 c6488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2790
  · exact u2791

def b6489 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 140 265 145 96 338 402 274), lower := (rows 97 38 140 265 145 96 64 128 256), losses := [] }

theorem u6489 : Upper (D 9) (R 9) [96,36,136,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6489 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6490 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 209, targets := 256 }], pairs := [(0,8),(1,0),(1,6),(1,7),(4,8)], upper := (rows 97 38 140 265 145 288 82 210 338), lower := (rows 97 38 140 265 145 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 296 64 128 256), good := (rows 96 38 174 296 144 288 64 128 288) },{ target := 6, region := (rows 1 6 4 8 16 296 0 128 256), good := (rows 33 38 174 297 145 288 0 128 288) },{ target := 7, region := (rows 1 6 4 8 16 296 64 0 256), good := (rows 97 38 46 297 17 288 64 0 288) }] }

theorem u6490 : Upper (D 9) (R 9) [96,36,136,257,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6490 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6491 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 361, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(3,7),(4,0),(4,5)], upper := (rows 97 38 140 265 146 33 336 464 336), lower := (rows 97 38 140 265 146 33 64 128 256), losses := [] }

theorem u6491 : Upper (D 9) (R 9) [96,36,136,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6491 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6492 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 50, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(4,0)], upper := (rows 97 38 140 265 146 48 321 449 321), lower := (rows 97 38 140 265 146 48 64 128 256), losses := [] }

theorem u6492 : Upper (D 9) (R 9) [96,36,136,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6492 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6493 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 140 265 146 96 337 401 273), lower := (rows 97 38 140 265 146 96 64 128 256), losses := [] }

theorem u6493 : Upper (D 9) (R 9) [96,36,136,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6493 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6494 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 209, targets := 256 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(3,7),(4,8)], upper := (rows 97 38 140 265 146 288 81 209 337), lower := (rows 97 38 140 265 146 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 20 296 64 128 256), good := (rows 96 54 190 296 146 288 64 128 288) }] }

theorem u6494 : Upper (D 9) (R 9) [96,36,136,257,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6494 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6495 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(1,6),(4,0),(4,5)], upper := (rows 97 38 140 265 208 33 338 402 274), lower := (rows 97 38 140 265 208 33 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 41 0 128 256), good := (rows 33 38 174 297 144 33 0 128 256) }] }

theorem u6495 : Upper (D 9) (R 9) [96,36,136,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6495 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6496 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 140 265 208 34 337 401 273), lower := (rows 97 38 140 265 208 34 64 128 256), losses := [] }

theorem u6496 : Upper (D 9) (R 9) [96,36,136,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6496 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6497 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 38 140 265 208 48 323 387 259), lower := (rows 97 38 140 265 208 48 64 128 256), losses := [] }

theorem u6497 : Upper (D 9) (R 9) [96,36,136,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6497 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6498 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 209, targets := 256 }], pairs := [(0,8),(1,0),(1,6),(1,7),(4,8)], upper := (rows 97 38 140 265 208 288 83 147 275), lower := (rows 97 38 140 265 208 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 296 64 128 256), good := (rows 96 38 174 296 208 288 64 128 288) },{ target := 6, region := (rows 1 6 4 8 16 296 0 128 256), good := (rows 33 38 174 297 144 288 0 128 288) },{ target := 7, region := (rows 1 6 4 8 16 296 64 0 256), good := (rows 97 38 46 297 80 288 64 0 288) }] }

theorem u6498 : Upper (D 9) (R 9) [96,36,136,257,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6498 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6499 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 6, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(1,6),(4,0),(4,5)], upper := (rows 97 38 140 265 274 33 208 208 464), lower := (rows 97 38 140 265 274 33 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 41 0 128 256), good := (rows 33 38 174 297 274 33 0 128 256) }] }

theorem u6499 : Upper (D 9) (R 9) [96,36,136,257,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6499 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6500 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 1, region := 193, targets := 256 },{ cop := 3, region := 196, targets := 256 }], pairs := [(0,8),(2,5),(2,8),(3,5)], upper := (rows 97 38 140 265 274 48 193 193 449), lower := (rows 97 38 140 265 274 48 64 128 256), losses := [] }

theorem u6500 : Upper (D 9) (R 9) [96,36,136,257,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6500 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6501 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 140 265 274 96 209 145 401), lower := (rows 97 38 140 265 274 96 64 128 256), losses := [] }

theorem u6501 : Upper (D 9) (R 9) [96,36,136,257,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6501 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6502 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 140 265 274 160 81 209 337), lower := (rows 97 38 140 265 274 160 64 128 256), losses := [] }

theorem u6502 : Upper (D 9) (R 9) [96,36,136,257,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6502 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6503 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 41, targets := 128 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(3,7),(4,0),(4,5)], upper := (rows 97 38 140 265 336 33 210 146 402), lower := (rows 97 38 140 265 336 33 64 128 256), losses := [] }

theorem u6503 : Upper (D 9) (R 9) [96,36,136,257,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6503 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6504 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 140 265 336 34 209 145 401), lower := (rows 97 38 140 265 336 34 64 128 256), losses := [] }

theorem u6504 : Upper (D 9) (R 9) [96,36,136,257,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6504 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6505 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 38 140 265 336 48 195 131 387), lower := (rows 97 38 140 265 336 48 64 128 256), losses := [] }

theorem u6505 : Upper (D 9) (R 9) [96,36,136,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6505 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6506 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 140 265 336 160 83 147 275), lower := (rows 97 38 140 265 336 160 64 128 256), losses := [] }

theorem u6506 : Upper (D 9) (R 9) [96,36,136,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6506 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6507 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 6, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(1,6),(4,0),(4,5)], upper := (rows 97 38 140 265 400 33 82 210 338), lower := (rows 97 38 140 265 400 33 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 41 0 128 256), good := (rows 33 38 174 297 400 33 0 128 256) }] }

theorem u6507 : Upper (D 9) (R 9) [96,36,136,257,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6507 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6508 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 140 265 400 34 81 209 337), lower := (rows 97 38 140 265 400 34 64 128 256), losses := [] }

theorem u6508 : Upper (D 9) (R 9) [96,36,136,257,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6508 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6509 : Route 9 := (fun mask => (mask,id))

def c6509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6509 : Upper (D 9) (R 9) [96,36,136,257,384,16] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,384,16] 13 (by decide) (choices 1) [1,2] r6509 c6509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2792
  · exact u2793

def b6510 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 140 265 400 96 83 147 275), lower := (rows 97 38 140 265 400 96 64 128 256), losses := [] }

theorem u6510 : Upper (D 9) (R 9) [96,36,136,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6510 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6511 : PairBound 9 := { available := 336, camps := [{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 140 266 145 33 336 464 336), lower := (rows 97 38 140 266 145 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 14 10 49 0 115 179 307), good := (rows 465 478 140 462 465 465 64 128 256) }] }

theorem u6511 : Upper (D 9) (R 9) [96,36,136,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6511 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6512 : Route 9 := (fun mask => (mask,id))

def c6512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6512 : Upper (D 9) (R 9) [96,36,136,258,129,16] 13 := by
  apply FastRouting.sound _ _ [96,36,136,258,129,16] 13 (by decide) (choices 1) [1,256] r6512 c6512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2794
  · exact u2795

def b6513 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 140 266 145 96 337 401 273), lower := (rows 97 38 140 266 145 96 64 128 256), losses := [] }

theorem u6513 : Upper (D 9) (R 9) [96,36,136,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6513 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6514 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 209, targets := 256 },{ cop := 0, region := 144, targets := 32 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(4,5),(4,8)], upper := (rows 97 38 140 266 145 288 81 209 337), lower := (rows 97 38 140 266 145 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 296 64 128 256), good := (rows 96 38 174 298 144 288 64 128 288) }] }

theorem u6514 : Upper (D 9) (R 9) [96,36,136,258,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6514 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6515 : PairBound 9 := { available := 273, camps := [{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 140 266 208 33 337 401 273), lower := (rows 97 38 140 266 208 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 10 51 0 97 161 289), good := (rows 465 478 140 286 208 465 64 128 256) }] }

theorem u6515 : Upper (D 9) (R 9) [96,36,136,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6515 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6516 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 38 140 266 208 48 321 385 257), lower := (rows 97 38 140 266 208 48 64 128 256), losses := [] }

theorem u6516 : Upper (D 9) (R 9) [96,36,136,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6516 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6517 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 209, targets := 256 },{ cop := 0, region := 144, targets := 32 },{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(4,5),(4,8)], upper := (rows 97 38 140 266 208 288 81 145 273), lower := (rows 97 38 140 266 208 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 296 64 128 256), good := (rows 96 38 174 298 208 288 64 128 288) }] }

theorem u6517 : Upper (D 9) (R 9) [96,36,136,258,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6517 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6518 : PairBound 9 := { available := 208, camps := [{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 140 266 273 33 208 208 464), lower := (rows 97 38 140 266 273 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 14 10 49 0 115 179 307), good := (rows 465 478 140 462 465 465 64 128 256) }] }

theorem u6518 : Upper (D 9) (R 9) [96,36,136,258,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6518 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6519 : Route 9 := (fun mask => (mask,id))

def c6519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6519 : Upper (D 9) (R 9) [96,36,136,258,257,16] 13 := by
  apply FastRouting.sound _ _ [96,36,136,258,257,16] 13 (by decide) (choices 1) [1,128] r6519 c6519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2796
  · exact u2797

def b6520 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 140 266 273 96 209 145 401), lower := (rows 97 38 140 266 273 96 64 128 256), losses := [] }

theorem u6520 : Upper (D 9) (R 9) [96,36,136,258,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6520 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6521 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 140 266 273 160 81 209 337), lower := (rows 97 38 140 266 273 160 64 128 256), losses := [] }

theorem u6521 : Upper (D 9) (R 9) [96,36,136,258,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6521 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6522 : PairBound 9 := { available := 145, camps := [{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 140 266 336 33 209 145 401), lower := (rows 97 38 140 266 336 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 10 51 0 97 161 289), good := (rows 465 478 140 286 336 465 64 128 256) }] }

theorem u6522 : Upper (D 9) (R 9) [96,36,136,258,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6522 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6523 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(1,6),(2,6),(3,6),(4,5)], upper := (rows 97 38 140 266 336 48 193 129 385), lower := (rows 97 38 140 266 336 48 64 128 256), losses := [] }

theorem u6523 : Upper (D 9) (R 9) [96,36,136,258,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6523 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6524 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 140 266 336 160 81 145 273), lower := (rows 97 38 140 266 336 160 64 128 256), losses := [] }

theorem u6524 : Upper (D 9) (R 9) [96,36,136,258,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6524 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6525 : PairBound 9 := { available := 81, camps := [{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 140 266 400 33 81 209 337), lower := (rows 97 38 140 266 400 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 10 51 0 97 161 289), good := (rows 465 478 140 286 400 465 64 128 256) }] }

theorem u6525 : Upper (D 9) (R 9) [96,36,136,258,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6525 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6526 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 46, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 38 140 266 400 48 65 193 321), lower := (rows 97 38 140 266 400 48 64 128 256), losses := [] }

theorem u6526 : Upper (D 9) (R 9) [96,36,136,258,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6526 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6527 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 140 266 400 96 81 145 273), lower := (rows 97 38 140 266 400 96 64 128 256), losses := [] }

theorem u6527 : Upper (D 9) (R 9) [96,36,136,258,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6527 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6528 : Route 9 := (fun mask => (mask,id))

def c6528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6528 : Upper (D 9) (R 9) [96,36,136,272,129,1] 13 := by
  apply FastRouting.sound _ _ [96,36,136,272,129,1] 13 (by decide) (choices 1) [2,256] r6528 c6528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2798
  · exact u2799

def b6529 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,5),(3,5),(4,5)], upper := (rows 97 38 140 280 145 34 321 449 321), lower := (rows 97 38 140 280 145 34 64 128 256), losses := [] }

theorem u6529 : Upper (D 9) (R 9) [96,36,136,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6529 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6530 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 140 280 145 96 323 387 259), lower := (rows 97 38 140 280 145 96 64 128 256), losses := [] }

theorem u6530 : Upper (D 9) (R 9) [96,36,136,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6530 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6531 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 209, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(1,7),(4,8)], upper := (rows 97 38 140 280 145 288 67 195 323), lower := (rows 97 38 140 280 145 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 296 64 128 256), good := (rows 96 38 174 312 144 288 64 128 288) }] }

theorem u6531 : Upper (D 9) (R 9) [96,36,136,272,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6531 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6532 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 361, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(2,5),(3,7)], upper := (rows 97 38 140 280 146 33 321 449 321), lower := (rows 97 38 140 280 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 22 10 18 0 97 161 289), good := (rows 449 478 140 284 158 449 64 128 256) }] }

theorem u6532 : Upper (D 9) (R 9) [96,36,136,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6532 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6533 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 140 280 146 96 321 385 257), lower := (rows 97 38 140 280 146 96 64 128 256), losses := [] }

theorem u6533 : Upper (D 9) (R 9) [96,36,136,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6533 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6534 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 209, targets := 256 },{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(3,7),(4,8)], upper := (rows 97 38 140 280 146 288 65 193 321), lower := (rows 97 38 140 280 146 288 64 128 256), losses := [] }

theorem u6534 : Upper (D 9) (R 9) [96,36,136,272,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6534 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6535 : Route 9 := (fun mask => (mask,id))

def c6535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6535 : Upper (D 9) (R 9) [96,36,136,272,192,1] 13 := by
  apply FastRouting.sound _ _ [96,36,136,272,192,1] 13 (by decide) (choices 1) [1,2,256] r6535 c6535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2800
  · exact u2801
  · exact u2802

def b6536 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,5),(3,5),(4,5)], upper := (rows 97 38 140 280 208 34 321 385 257), lower := (rows 97 38 140 280 208 34 64 128 256), losses := [] }

theorem u6536 : Upper (D 9) (R 9) [96,36,136,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6536 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6537 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 209, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(1,7),(4,8)], upper := (rows 97 38 140 280 208 288 67 131 259), lower := (rows 97 38 140 280 208 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 296 64 128 256), good := (rows 96 38 174 312 208 288 64 128 288) }] }

theorem u6537 : Upper (D 9) (R 9) [96,36,136,272,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6537 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6538 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,8)], upper := (rows 97 38 140 328 145 33 338 402 274), lower := (rows 97 38 140 328 145 33 64 128 256), losses := [{ target := 7, region := (rows 73 6 4 8 16 125 64 0 256), good := (rows 97 38 47 361 49 33 97 0 256) },{ target := 8, region := (rows 73 6 4 8 20 125 64 128 0), good := (rows 97 54 191 105 177 33 97 128 0) }] }

theorem u6538 : Upper (D 9) (R 9) [96,36,136,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6538 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6539 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 140 328 145 34 337 401 273), lower := (rows 97 38 140 328 145 34 64 128 256), losses := [] }

theorem u6539 : Upper (D 9) (R 9) [96,36,136,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6539 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u6539
end Delivery.IrregularNine14.P09
