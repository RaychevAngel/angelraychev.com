import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0324
import IrregularNine14P07C0325

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34620 : Route 9 := (fun mask => (mask,id))

def c34620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34620 : Upper (D 7) (R 7) [34,68,130,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,144,257] 13 (by decide) (choices 1) [1,8,64] r34620 c34620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19449
  · exact u19450
  · exact u19451

def b34621 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,1),(4,1)], upper := (rows 35 70 134 152 280 97 97 225 353), lower := (rows 35 70 134 152 280 32 64 128 256), losses := [] }

theorem u34621 : Upper (D 7) (R 7) [34,68,130,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34622 : Route 9 := (fun mask => (mask,id))

def c34622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34622 : Upper (D 7) (R 7) [34,68,130,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,130,144,288] 13 (by decide) (choices 1) [1,8,64] r34622 c34622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19452
  · exact u19453
  · exact u19454

def r34623 : Route 9 := (fun mask => (mask,id))

def c34623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34623 : Upper (D 7) (R 7) [34,68,130,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,130,144,320] 13 (by decide) (choices 1) [1,8] r34623 c34623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19455
  · exact u19456

def r34624 : Route 9 := (fun mask => (mask,id))

def c34624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34624 : Upper (D 7) (R 7) [34,68,130,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,160,257] 13 (by decide) (choices 1) [1,8,16,64] r34624 c34624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19457
  · exact u19458
  · exact u19459
  · exact u19460

def r34625 : Route 9 := (fun mask => (mask,id))

def c34625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34625 : Upper (D 7) (R 7) [34,68,130,160,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,160,264] 13 (by decide) (choices 1) [1,16,64] r34625 c34625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19461
  · exact u19462
  · exact u19463

def r34626 : Route 9 := (fun mask => (mask,id))

def c34626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34626 : Upper (D 7) (R 7) [34,68,130,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,130,160,320] 13 (by decide) (choices 1) [1,8,16] r34626 c34626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19464
  · exact u19465
  · exact u19466

def b34627 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 6, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 134 200 273 57 121 185 313), lower := (rows 35 70 134 200 273 32 64 128 256), losses := [] }

theorem u34627 : Upper (D 7) (R 7) [34,68,130,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34628 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 134 200 280 49 113 177 305), lower := (rows 35 70 134 200 280 32 64 128 256), losses := [] }

theorem u34628 : Upper (D 7) (R 7) [34,68,130,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34629 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 6, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 134 200 304 57 89 153 281), lower := (rows 35 70 134 200 304 32 64 128 256), losses := [] }

theorem u34629 : Upper (D 7) (R 7) [34,68,130,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34630 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 140 25 19 480 480 480 480), lower := (rows 35 70 140 25 19 32 64 128 256), losses := [] }

theorem u34630 : Upper (D 7) (R 7) [34,68,136,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34631 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 70 140 25 49 482 450 450 450), lower := (rows 35 70 140 25 49 32 64 128 256), losses := [] }

theorem u34631 : Upper (D 7) (R 7) [34,68,136,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34632 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 25 50 481 449 449 449), lower := (rows 35 70 140 25 50 32 64 128 256), losses := [] }

theorem u34632 : Upper (D 7) (R 7) [34,68,136,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34633 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 140 25 81 418 482 418 418), lower := (rows 35 70 140 25 81 32 64 128 256), losses := [] }

theorem u34633 : Upper (D 7) (R 7) [34,68,136,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34634 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 140 25 82 417 481 417 417), lower := (rows 35 70 140 25 82 32 64 128 256), losses := [] }

theorem u34634 : Upper (D 7) (R 7) [34,68,136,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34635 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(2,6)], upper := (rows 35 70 140 25 112 419 451 387 387), lower := (rows 35 70 140 25 112 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 35 0 131 259), good := (rows 419 423 140 445 48 32 0 128 256) }] }

theorem u34635 : Upper (D 7) (R 7) [34,68,136,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34636 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 35 70 140 25 145 354 354 482 354), lower := (rows 35 70 140 25 145 32 64 128 256), losses := [] }

theorem u34636 : Upper (D 7) (R 7) [34,68,136,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34637 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 484, targets := 2 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 35 70 140 25 146 353 353 481 353), lower := (rows 35 70 140 25 146 32 64 128 256), losses := [] }

theorem u34637 : Upper (D 7) (R 7) [34,68,136,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34638 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,5)], upper := (rows 35 70 140 25 176 355 323 451 323), lower := (rows 35 70 140 25 176 32 64 128 256), losses := [] }

theorem u34638 : Upper (D 7) (R 7) [34,68,136,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34639 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 35 70 140 25 208 291 355 419 291), lower := (rows 35 70 140 25 208 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 35 0 131 259), good := (rows 419 423 140 445 144 32 0 128 256) }] }

theorem u34639 : Upper (D 7) (R 7) [34,68,136,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34640 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 140 25 273 226 226 226 482), lower := (rows 35 70 140 25 273 32 64 128 256), losses := [] }

theorem u34640 : Upper (D 7) (R 7) [34,68,136,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34641 : Route 9 := (fun mask => (mask,id))

def c34641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34641 : Upper (D 7) (R 7) [34,68,136,17,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,258] 13 (by decide) (choices 1) [1,64,128] r34641 c34641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19467
  · exact u19468
  · exact u19469

def r34642 : Route 9 := (fun mask => (mask,id))

def c34642 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34642 : Upper (D 7) (R 7) [34,68,136,17,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,288] 13 (by decide) (choices 1) [1,2,64,128] r34642 c34642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19470
  · exact u19471
  · exact u19472
  · exact u19473

def r34643 : Route 9 := (fun mask => (mask,id))

def c34643 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34643 : Upper (D 7) (R 7) [34,68,136,17,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,320] 13 (by decide) (choices 1) [1,2,128] r34643 c34643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19474
  · exact u19475
  · exact u19476

def r34644 : Route 9 := (fun mask => (mask,id))

def c34644 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34644 : Upper (D 7) (R 7) [34,68,136,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,384] 13 (by decide) (choices 1) [1,2,64] r34644 c34644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19477
  · exact u19478
  · exact u19479

def b34645 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 26 49 481 449 449 449), lower := (rows 35 70 140 26 49 32 64 128 256), losses := [] }

theorem u34645 : Upper (D 7) (R 7) [34,68,136,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34646 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(2,1),(2,6),(4,1)], upper := (rows 35 70 140 26 81 417 481 417 417), lower := (rows 35 70 140 26 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 497 68 140 508 497 32 64 128 256) }] }

theorem u34646 : Upper (D 7) (R 7) [34,68,136,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34647 : Route 9 := (fun mask => (mask,id))

def c34647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34647 : Upper (D 7) (R 7) [34,68,136,18,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,96] 13 (by decide) (choices 1) [1,128,256] r34647 c34647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19480
  · exact u19481
  · exact u19482

def b34648 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(4,1)], upper := (rows 35 70 140 26 145 353 353 481 353), lower := (rows 35 70 140 26 145 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 497 68 140 508 497 32 64 128 256) }] }

theorem u34648 : Upper (D 7) (R 7) [34,68,136,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34649 : Route 9 := (fun mask => (mask,id))

def c34649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34649 : Upper (D 7) (R 7) [34,68,136,18,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,160] 13 (by decide) (choices 1) [1,64,256] r34649 c34649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19483
  · exact u19484
  · exact u19485

def b34650 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 14, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 140 26 208 289 353 417 289), lower := (rows 35 70 140 26 208 32 64 128 256), losses := [] }

theorem u34650 : Upper (D 7) (R 7) [34,68,136,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34651 : Route 9 := (fun mask => (mask,id))

def c34651 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34651 : Upper (D 7) (R 7) [34,68,136,18,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,257] 13 (by decide) (choices 1) [1,64,128] r34651 c34651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19486
  · exact u19487
  · exact u19488

def r34652 : Route 9 := (fun mask => (mask,id))

def c34652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34652 : Upper (D 7) (R 7) [34,68,136,18,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,288] 13 (by decide) (choices 1) [1,64,128] r34652 c34652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19489
  · exact u19490
  · exact u19491

def r34653 : Route 9 := (fun mask => (mask,id))

def c34653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34653 : Upper (D 7) (R 7) [34,68,136,18,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,320] 13 (by decide) (choices 1) [1,128] r34653 c34653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19492
  · exact u19493

def r34654 : Route 9 := (fun mask => (mask,id))

def c34654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34654 : Upper (D 7) (R 7) [34,68,136,18,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,384] 13 (by decide) (choices 1) [1,64] r34654 c34654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19494
  · exact u19495

def b34655 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 56 19 481 449 449 449), lower := (rows 35 70 140 56 19 32 64 128 256), losses := [] }

theorem u34655 : Upper (D 7) (R 7) [34,68,136,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34656 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,5)], upper := (rows 35 70 140 56 81 419 451 387 387), lower := (rows 35 70 140 56 81 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 20 24 16 35 0 131 259), good := (rows 419 423 140 60 445 32 0 128 256) }] }

theorem u34656 : Upper (D 7) (R 7) [34,68,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34657 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 140 56 82 417 449 385 385), lower := (rows 35 70 140 56 82 32 64 128 256), losses := [] }

theorem u34657 : Upper (D 7) (R 7) [34,68,136,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34658 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(3,7),(4,5)], upper := (rows 35 70 140 56 145 355 323 451 323), lower := (rows 35 70 140 56 145 32 64 128 256), losses := [{ target := 7, region := (rows 7 6 4 24 16 39 71 0 263), good := (rows 355 359 367 56 377 32 64 0 256) }] }

theorem u34658 : Upper (D 7) (R 7) [34,68,136,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34659 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,5)], upper := (rows 35 70 140 56 146 353 321 449 321), lower := (rows 35 70 140 56 146 32 64 128 256), losses := [] }

theorem u34659 : Upper (D 7) (R 7) [34,68,136,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34660 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,5)], upper := (rows 35 70 140 56 208 291 323 387 259), lower := (rows 35 70 140 56 208 32 64 128 256), losses := [] }

theorem u34660 : Upper (D 7) (R 7) [34,68,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34661 : Route 9 := (fun mask => (mask,id))

def c34661 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34661 : Upper (D 7) (R 7) [34,68,136,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,257] 13 (by decide) (choices 1) [1,2,64,128] r34661 c34661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19496
  · exact u19497
  · exact u19498
  · exact u19499

def r34662 : Route 9 := (fun mask => (mask,id))

def c34662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34662 : Upper (D 7) (R 7) [34,68,136,48,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,258] 13 (by decide) (choices 1) [1,64,128] r34662 c34662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19500
  · exact u19501
  · exact u19502

def r34663 : Route 9 := (fun mask => (mask,id))

def c34663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34663 : Upper (D 7) (R 7) [34,68,136,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,320] 13 (by decide) (choices 1) [1,2,128] r34663 c34663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19503
  · exact u19504
  · exact u19505

def r34664 : Route 9 := (fun mask => (mask,id))

def c34664 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34664 : Upper (D 7) (R 7) [34,68,136,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,384] 13 (by decide) (choices 1) [1,2,64] r34664 c34664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19506
  · exact u19507
  · exact u19508

def b34665 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,5),(4,6),(4,7)], upper := (rows 35 70 140 73 19 432 496 432 432), lower := (rows 35 70 140 73 19 32 64 128 256), losses := [] }

theorem u34665 : Upper (D 7) (R 7) [34,68,136,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34666 : PairBound 9 := { available := 402, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 140 73 49 434 466 402 402), lower := (rows 35 70 140 73 49 32 64 128 256), losses := [] }

theorem u34666 : Upper (D 7) (R 7) [34,68,136,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34667 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 128 }], pairs := [(0,6),(4,0),(4,6),(4,7)], upper := (rows 35 70 140 73 50 433 465 401 401), lower := (rows 35 70 140 73 50 32 64 128 256), losses := [] }

theorem u34667 : Upper (D 7) (R 7) [34,68,136,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34668 : Route 9 := (fun mask => (mask,id))

def c34668 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34668 : Upper (D 7) (R 7) [34,68,136,65,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,129] 13 (by decide) (choices 1) [2,16,256] r34668 c34668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19509
  · exact u19510
  · exact u19511

def b34669 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 73 146 305 369 433 305), lower := (rows 35 70 140 73 146 32 64 128 256), losses := [] }

theorem u34669 : Upper (D 7) (R 7) [34,68,136,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34670 : Route 9 := (fun mask => (mask,id))

def c34670 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34670 : Upper (D 7) (R 7) [34,68,136,65,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,160] 13 (by decide) (choices 1) [1,2,16,256] r34670 c34670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19512
  · exact u19513
  · exact u19514
  · exact u19515

def r34671 : Route 9 := (fun mask => (mask,id))

def c34671 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34671 : Upper (D 7) (R 7) [34,68,136,65,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,257] 13 (by decide) (choices 1) [2,16,128] r34671 c34671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19516
  · exact u19517
  · exact u19518

def r34672 : Route 9 := (fun mask => (mask,id))

def c34672 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34672 : Upper (D 7) (R 7) [34,68,136,65,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,258] 13 (by decide) (choices 1) [1,16,128] r34672 c34672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19519
  · exact u19520
  · exact u19521

def r34673 : Route 9 := (fun mask => (mask,id))

def c34673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34673 : Upper (D 7) (R 7) [34,68,136,65,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,288] 13 (by decide) (choices 1) [1,2,16,128] r34673 c34673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19522
  · exact u19523
  · exact u19524
  · exact u19525

def r34674 : Route 9 := (fun mask => (mask,id))

def c34674 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34674 : Upper (D 7) (R 7) [34,68,136,65,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,384] 13 (by decide) (choices 1) [1,2,16] r34674 c34674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19526
  · exact u19527
  · exact u19528

def b34675 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,5),(4,6),(4,7)], upper := (rows 35 70 140 88 19 417 481 417 417), lower := (rows 35 70 140 88 19 32 64 128 256), losses := [] }

theorem u34675 : Upper (D 7) (R 7) [34,68,136,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34676 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 140 88 49 419 451 387 387), lower := (rows 35 70 140 88 49 32 64 128 256), losses := [] }

theorem u34676 : Upper (D 7) (R 7) [34,68,136,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34677 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 128 }], pairs := [(0,6),(4,0),(4,6),(4,7)], upper := (rows 35 70 140 88 50 417 449 385 385), lower := (rows 35 70 140 88 50 32 64 128 256), losses := [] }

theorem u34677 : Upper (D 7) (R 7) [34,68,136,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34678 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 70 140 88 145 291 355 419 291), lower := (rows 35 70 140 88 145 32 64 128 256), losses := [] }

theorem u34678 : Upper (D 7) (R 7) [34,68,136,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34679 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 70 140 88 146 289 353 417 289), lower := (rows 35 70 140 88 146 32 64 128 256), losses := [] }

theorem u34679 : Upper (D 7) (R 7) [34,68,136,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u34679
end Delivery.IrregularNine14.P07
