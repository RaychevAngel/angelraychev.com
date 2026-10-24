import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0491
import IrregularNine14P07C0492

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40620 : Route 9 := (fun mask => (mask,id))

def c40620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40620 : Upper (D 7) (R 7) [96,288,3,130,132] 13 := by
  apply FastRouting.sound _ _ [96,288,3,130,132] 13 (by decide) (choices 1) [1,8,16,64] r40620 c40620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29475
  · exact u29476
  · exact u29477
  · exact u29478

def b40621 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 97 290 7 138 152 117 85 213 341), lower := (rows 97 290 7 138 152 32 64 128 256), losses := [] }

theorem u40621 : Upper (D 7) (R 7) [96,288,3,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40622 : Route 9 := (fun mask => (mask,id))

def c40622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40622 : Upper (D 7) (R 7) [96,288,3,130,192] 13 := by
  apply FastRouting.sound _ _ [96,288,3,130,192] 13 (by decide) (choices 1) [1,4,8,16] r40622 c40622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29479
  · exact u29480
  · exact u29481
  · exact u29482

def b40623 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 97 290 7 140 152 115 83 211 339), lower := (rows 97 290 7 140 152 32 64 128 256), losses := [] }

theorem u40623 : Upper (D 7) (R 7) [96,288,3,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40624 : Route 9 := (fun mask => (mask,id))

def c40624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40624 : Upper (D 7) (R 7) [96,288,3,132,192] 13 := by
  apply FastRouting.sound _ _ [96,288,3,132,192] 13 (by decide) (choices 1) [1,2,8,16] r40624 c40624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29483
  · exact u29484
  · exact u29485
  · exact u29486

def b40625 : PairBound 9 := { available := 71, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 290 7 152 152 103 71 199 327), lower := (rows 97 290 7 152 152 32 64 128 256), losses := [] }

theorem u40625 : Upper (D 7) (R 7) [96,288,3,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40626 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 290 7 152 208 47 79 143 271), lower := (rows 97 290 7 152 208 32 64 128 256), losses := [] }

theorem u40626 : Upper (D 7) (R 7) [96,288,3,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40627 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 13 82 178 210 146 402), lower := (rows 97 290 13 13 82 32 64 128 256), losses := [] }

theorem u40627 : Upper (D 7) (R 7) [96,288,9,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40628 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 13 146 242 210 210 466), lower := (rows 97 290 13 13 146 32 64 128 256), losses := [] }

theorem u40628 : Upper (D 7) (R 7) [96,288,9,5,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40629 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 13 208 178 210 146 402), lower := (rows 97 290 13 13 208 32 64 128 256), losses := [] }

theorem u40629 : Upper (D 7) (R 7) [96,288,9,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40630 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 290 13 14 81 178 210 146 402), lower := (rows 97 290 13 14 81 32 64 128 256), losses := [] }

theorem u40630 : Upper (D 7) (R 7) [96,288,9,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40631 : Route 9 := (fun mask => (mask,id))

def c40631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40631 : Upper (D 7) (R 7) [96,288,9,6,66] 13 := by
  apply FastRouting.sound _ _ [96,288,9,6,66] 13 (by decide) (choices 1) [1,16,128] r40631 c40631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29487
  · exact u29488
  · exact u29489

def r40632 : Route 9 := (fun mask => (mask,id))

def c40632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40632 : Upper (D 7) (R 7) [96,288,9,6,129] 13 := by
  apply FastRouting.sound _ _ [96,288,9,6,129] 13 (by decide) (choices 1) [2,16,64,128] r40632 c40632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29490
  · exact u29491
  · exact u29492
  · exact u29493

def r40633 : Route 9 := (fun mask => (mask,id))

def c40633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40633 : Upper (D 7) (R 7) [96,288,9,6,130] 13 := by
  apply FastRouting.sound _ _ [96,288,9,6,130] 13 (by decide) (choices 1) [1,16,64,128] r40633 c40633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29494
  · exact u29495
  · exact u29496
  · exact u29497

def r40634 : Route 9 := (fun mask => (mask,id))

def c40634 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40634 : Upper (D 7) (R 7) [96,288,9,6,192] 13 := by
  apply FastRouting.sound _ _ [96,288,9,6,192] 13 (by decide) (choices 1) [1,2,16,128] r40634 c40634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29498
  · exact u29499
  · exact u29500
  · exact u29501

def b40635 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 25 22 226 194 194 450), lower := (rows 97 290 13 25 22 32 64 128 256), losses := [] }

theorem u40635 : Upper (D 7) (R 7) [96,288,9,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40636 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 4, targets := 162 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 97 290 13 25 82 166 198 134 390), lower := (rows 97 290 13 25 82 32 64 128 256), losses := [] }

theorem u40636 : Upper (D 7) (R 7) [96,288,9,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40637 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 28, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 290 13 25 84 162 194 130 386), lower := (rows 97 290 13 25 84 32 64 128 256), losses := [] }

theorem u40637 : Upper (D 7) (R 7) [96,288,9,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40638 : PairBound 9 := { available := 198, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 25 146 230 198 198 454), lower := (rows 97 290 13 25 146 32 64 128 256), losses := [] }

theorem u40638 : Upper (D 7) (R 7) [96,288,9,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40639 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 25 148 226 194 194 450), lower := (rows 97 290 13 25 148 32 64 128 256), losses := [] }

theorem u40639 : Upper (D 7) (R 7) [96,288,9,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40640 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 4, targets := 162 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 97 290 13 25 208 166 198 134 390), lower := (rows 97 290 13 25 208 32 64 128 256), losses := [] }

theorem u40640 : Upper (D 7) (R 7) [96,288,9,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40641 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 290 13 26 22 225 193 193 449), lower := (rows 97 290 13 26 22 32 64 128 256), losses := [] }

theorem u40641 : Upper (D 7) (R 7) [96,288,9,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40642 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 290 13 26 81 166 198 134 390), lower := (rows 97 290 13 26 81 32 64 128 256), losses := [] }

theorem u40642 : Upper (D 7) (R 7) [96,288,9,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40643 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 290 13 26 82 165 197 133 389), lower := (rows 97 290 13 26 82 32 64 128 256), losses := [] }

theorem u40643 : Upper (D 7) (R 7) [96,288,9,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40644 : Route 9 := (fun mask => (mask,id))

def c40644 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40644 : Upper (D 7) (R 7) [96,288,9,18,68] 13 := by
  apply FastRouting.sound _ _ [96,288,9,18,68] 13 (by decide) (choices 1) [1,2,128] r40644 c40644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29502
  · exact u29503
  · exact u29504

def r40645 : Route 9 := (fun mask => (mask,id))

def c40645 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40645 : Upper (D 7) (R 7) [96,288,9,18,129] 13 := by
  apply FastRouting.sound _ _ [96,288,9,18,129] 13 (by decide) (choices 1) [2,4,64,128] r40645 c40645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29505
  · exact u29506
  · exact u29507
  · exact u29508

def b40646 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 290 13 26 146 229 197 197 453), lower := (rows 97 290 13 26 146 32 64 128 256), losses := [] }

theorem u40646 : Upper (D 7) (R 7) [96,288,9,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40647 : Route 9 := (fun mask => (mask,id))

def c40647 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40647 : Upper (D 7) (R 7) [96,288,9,18,132] 13 := by
  apply FastRouting.sound _ _ [96,288,9,18,132] 13 (by decide) (choices 1) [1,2,64,128] r40647 c40647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29509
  · exact u29510
  · exact u29511
  · exact u29512

def r40648 : Route 9 := (fun mask => (mask,id))

def c40648 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40648 : Upper (D 7) (R 7) [96,288,9,18,192] 13 := by
  apply FastRouting.sound _ _ [96,288,9,18,192] 13 (by decide) (choices 1) [1,2,4,128] r40648 c40648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29513
  · exact u29514
  · exact u29515
  · exact u29516

def b40649 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 28, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 290 13 28 81 162 194 130 386), lower := (rows 97 290 13 28 81 32 64 128 256), losses := [] }

theorem u40649 : Upper (D 7) (R 7) [96,288,9,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40650 : Route 9 := (fun mask => (mask,id))

def c40650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40650 : Upper (D 7) (R 7) [96,288,9,20,66] 13 := by
  apply FastRouting.sound _ _ [96,288,9,20,66] 13 (by decide) (choices 1) [1,2,128] r40650 c40650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29517
  · exact u29518
  · exact u29519

def b40651 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 28 145 226 194 194 450), lower := (rows 97 290 13 28 145 32 64 128 256), losses := [] }

theorem u40651 : Upper (D 7) (R 7) [96,288,9,20,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40652 : Route 9 := (fun mask => (mask,id))

def c40652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40652 : Upper (D 7) (R 7) [96,288,9,20,130] 13 := by
  apply FastRouting.sound _ _ [96,288,9,20,130] 13 (by decide) (choices 1) [1,2,64,128] r40652 c40652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29520
  · exact u29521
  · exact u29522
  · exact u29523

def r40653 : Route 9 := (fun mask => (mask,id))

def c40653 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40653 : Upper (D 7) (R 7) [96,288,9,20,192] 13 := by
  apply FastRouting.sound _ _ [96,288,9,20,192] 13 (by decide) (choices 1) [1,2,128] r40653 c40653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29524
  · exact u29525
  · exact u29526

def b40654 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 290 13 73 22 178 210 146 402), lower := (rows 97 290 13 73 22 32 64 128 256), losses := [] }

theorem u40654 : Upper (D 7) (R 7) [96,288,9,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40655 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 290 13 73 146 182 214 150 406), lower := (rows 97 290 13 73 146 32 64 128 256), losses := [] }

theorem u40655 : Upper (D 7) (R 7) [96,288,9,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40656 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 290 13 73 148 178 210 146 402), lower := (rows 97 290 13 73 148 32 64 128 256), losses := [] }

theorem u40656 : Upper (D 7) (R 7) [96,288,9,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40657 : Route 9 := (fun mask => (mask,id))

def c40657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40657 : Upper (D 7) (R 7) [96,288,9,66,6] 13 := by
  apply FastRouting.sound _ _ [96,288,9,66,6] 13 (by decide) (choices 1) [1,16,128] r40657 c40657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29527
  · exact u29528
  · exact u29529

def r40658 : Route 9 := (fun mask => (mask,id))

def c40658 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40658 : Upper (D 7) (R 7) [96,288,9,66,129] 13 := by
  apply FastRouting.sound _ _ [96,288,9,66,129] 13 (by decide) (choices 1) [2,4,16,128] r40658 c40658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29530
  · exact u29531
  · exact u29532
  · exact u29533

def r40659 : Route 9 := (fun mask => (mask,id))

def c40659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40659 : Upper (D 7) (R 7) [96,288,9,66,130] 13 := by
  apply FastRouting.sound _ _ [96,288,9,66,130] 13 (by decide) (choices 1) [1,4,16,128] r40659 c40659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29534
  · exact u29535
  · exact u29536
  · exact u29537

def r40660 : Route 9 := (fun mask => (mask,id))

def c40660 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40660 : Upper (D 7) (R 7) [96,288,9,66,132] 13 := by
  apply FastRouting.sound _ _ [96,288,9,66,132] 13 (by decide) (choices 1) [1,2,16,128] r40660 c40660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29538
  · exact u29539
  · exact u29540
  · exact u29541

def b40661 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 290 13 76 145 178 210 146 402), lower := (rows 97 290 13 76 145 32 64 128 256), losses := [] }

theorem u40661 : Upper (D 7) (R 7) [96,288,9,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40662 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 290 13 76 146 179 211 147 403), lower := (rows 97 290 13 76 146 32 64 128 256), losses := [] }

theorem u40662 : Upper (D 7) (R 7) [96,288,9,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40663 : Route 9 := (fun mask => (mask,id))

def c40663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40663 : Upper (D 7) (R 7) [96,288,9,80,6] 13 := by
  apply FastRouting.sound _ _ [96,288,9,80,6] 13 (by decide) (choices 1) [1,2,128] r40663 c40663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29542
  · exact u29543
  · exact u29544

def r40664 : Route 9 := (fun mask => (mask,id))

def c40664 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40664 : Upper (D 7) (R 7) [96,288,9,80,129] 13 := by
  apply FastRouting.sound _ _ [96,288,9,80,129] 13 (by decide) (choices 1) [2,4,128] r40664 c40664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29545
  · exact u29546
  · exact u29547

def r40665 : Route 9 := (fun mask => (mask,id))

def c40665 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40665 : Upper (D 7) (R 7) [96,288,9,80,130] 13 := by
  apply FastRouting.sound _ _ [96,288,9,80,130] 13 (by decide) (choices 1) [1,2,4,128] r40665 c40665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29548
  · exact u29549
  · exact u29550
  · exact u29551

def r40666 : Route 9 := (fun mask => (mask,id))

def c40666 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40666 : Upper (D 7) (R 7) [96,288,9,80,132] 13 := by
  apply FastRouting.sound _ _ [96,288,9,80,132] 13 (by decide) (choices 1) [1,2,128] r40666 c40666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29552
  · exact u29553
  · exact u29554

def b40667 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 137 22 242 210 210 466), lower := (rows 97 290 13 137 22 32 64 128 256), losses := [] }

theorem u40667 : Upper (D 7) (R 7) [96,288,9,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40668 : PairBound 9 := { available := 150, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 137 82 182 214 150 406), lower := (rows 97 290 13 137 82 32 64 128 256), losses := [] }

theorem u40668 : Upper (D 7) (R 7) [96,288,9,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40669 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 137 84 178 210 146 402), lower := (rows 97 290 13 137 84 32 64 128 256), losses := [] }

theorem u40669 : Upper (D 7) (R 7) [96,288,9,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40670 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 137 146 118 86 214 342), lower := (rows 97 290 13 137 146 32 64 128 256), losses := [] }

theorem u40670 : Upper (D 7) (R 7) [96,288,9,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40671 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 20, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 97 290 13 137 148 114 82 210 338), lower := (rows 97 290 13 137 148 32 64 128 256), losses := [] }

theorem u40671 : Upper (D 7) (R 7) [96,288,9,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40672 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 137 208 54 86 150 278), lower := (rows 97 290 13 137 208 32 64 128 256), losses := [] }

theorem u40672 : Upper (D 7) (R 7) [96,288,9,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40673 : Route 9 := (fun mask => (mask,id))

def c40673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40673 : Upper (D 7) (R 7) [96,288,9,130,6] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,6] 13 (by decide) (choices 1) [1,16,64,128] r40673 c40673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29555
  · exact u29556
  · exact u29557
  · exact u29558

def b40674 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 290 13 138 81 182 214 150 406), lower := (rows 97 290 13 138 81 32 64 128 256), losses := [] }

theorem u40674 : Upper (D 7) (R 7) [96,288,9,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40675 : Route 9 := (fun mask => (mask,id))

def c40675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40675 : Upper (D 7) (R 7) [96,288,9,130,66] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,66] 13 (by decide) (choices 1) [1,4,16,128] r40675 c40675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29559
  · exact u29560
  · exact u29561
  · exact u29562

def r40676 : Route 9 := (fun mask => (mask,id))

def c40676 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40676 : Upper (D 7) (R 7) [96,288,9,130,68] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,68] 13 (by decide) (choices 1) [1,2,16,128] r40676 c40676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29563
  · exact u29564
  · exact u29565
  · exact u29566

def r40677 : Route 9 := (fun mask => (mask,id))

def c40677 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40677 : Upper (D 7) (R 7) [96,288,9,130,129] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,129] 13 (by decide) (choices 1) [2,4,16,64] r40677 c40677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29567
  · exact u29568
  · exact u29569
  · exact u29570

def b40678 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 97 290 13 138 146 117 85 213 341), lower := (rows 97 290 13 138 146 32 64 128 256), losses := [] }

theorem u40678 : Upper (D 7) (R 7) [96,288,9,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40679 : Route 9 := (fun mask => (mask,id))

def c40679 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40679 : Upper (D 7) (R 7) [96,288,9,130,132] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,132] 13 (by decide) (choices 1) [1,2,16,64] r40679 c40679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29571
  · exact u29572
  · exact u29573
  · exact u29574

#print axioms u40679
end Delivery.IrregularNine14.P07
