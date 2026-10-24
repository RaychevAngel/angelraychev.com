import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0043

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14700 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 259 44 88 176 96 195 131 387), lower := (rows 7 259 44 88 176 96 64 128 256), losses := [] }

theorem u14700 : Upper (D 7) (R 7) [6,257,40,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14701 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 44 88 176 160 67 195 323), lower := (rows 7 259 44 88 176 160 64 128 256), losses := [] }

theorem u14701 : Upper (D 7) (R 7) [6,257,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14702 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 204, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 259 44 200 49 34 208 208 464), lower := (rows 7 259 44 200 49 34 64 128 256), losses := [] }

theorem u14702 : Upper (D 7) (R 7) [6,257,40,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14703 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 7 259 44 200 49 48 194 194 450), lower := (rows 7 259 44 200 49 48 64 128 256), losses := [] }

theorem u14703 : Upper (D 7) (R 7) [6,257,40,192,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14703 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14704 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 259 44 200 49 96 210 146 402), lower := (rows 7 259 44 200 49 96 64 128 256), losses := [] }

theorem u14704 : Upper (D 7) (R 7) [6,257,40,192,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14705 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 204, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 259 44 200 50 33 208 208 464), lower := (rows 7 259 44 200 50 33 64 128 256), losses := [] }

theorem u14705 : Upper (D 7) (R 7) [6,257,40,192,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14706 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 }], pairs := [(4,0),(4,6),(4,7)], upper := (rows 7 259 44 200 50 48 193 193 449), lower := (rows 7 259 44 200 50 48 64 128 256), losses := [] }

theorem u14706 : Upper (D 7) (R 7) [6,257,40,192,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14706 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14707 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 259 44 200 50 96 209 145 401), lower := (rows 7 259 44 200 50 96 64 128 256), losses := [] }

theorem u14707 : Upper (D 7) (R 7) [6,257,40,192,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14708 : Route 9 := (fun mask => (mask,id))

def c14708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u14708 : Upper (D 7) (R 7) [6,257,40,192,65,2] 13 := by
  apply FastRouting.sound _ _ [6,257,40,192,65,2] 13 (by decide) (choices 1) [16,32,128] r14708 c14708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2599
  · exact u2600
  · exact u2601

def r14709 : Route 9 := (fun mask => (mask,id))

def c14709 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14709 : Upper (D 7) (R 7) [6,257,40,192,65,16] 13 := by
  apply FastRouting.sound _ _ [6,257,40,192,65,16] 13 (by decide) (choices 1) [2,32,128] r14709 c14709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2602
  · exact u2603
  · exact u2604

def b14710 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 259 44 200 81 160 114 178 306), lower := (rows 7 259 44 200 81 160 64 128 256), losses := [] }

theorem u14710 : Upper (D 7) (R 7) [6,257,40,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14711 : Route 9 := (fun mask => (mask,id))

def c14711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u14711 : Upper (D 7) (R 7) [6,257,40,192,66,1] 13 := by
  apply FastRouting.sound _ _ [6,257,40,192,66,1] 13 (by decide) (choices 1) [16,32,128] r14711 c14711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2605
  · exact u2606
  · exact u2607

def r14712 : Route 9 := (fun mask => (mask,id))

def c14712 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14712 : Upper (D 7) (R 7) [6,257,40,192,66,16] 13 := by
  apply FastRouting.sound _ _ [6,257,40,192,66,16] 13 (by decide) (choices 1) [1,32,128] r14712 c14712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2608
  · exact u2609
  · exact u2610

def b14713 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 259 44 200 82 160 113 177 305), lower := (rows 7 259 44 200 82 160 64 128 256), losses := [] }

theorem u14713 : Upper (D 7) (R 7) [6,257,40,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14714 : Route 9 := (fun mask => (mask,id))

def c14714 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14714 : Upper (D 7) (R 7) [6,257,40,192,96,1] 13 := by
  apply FastRouting.sound _ _ [6,257,40,192,96,1] 13 (by decide) (choices 1) [2,16,128] r14714 c14714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2611
  · exact u2612
  · exact u2613

def r14715 : Route 9 := (fun mask => (mask,id))

def c14715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14715 : Upper (D 7) (R 7) [6,257,40,192,96,2] 13 := by
  apply FastRouting.sound _ _ [6,257,40,192,96,2] 13 (by decide) (choices 1) [1,16,128] r14715 c14715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2614
  · exact u2615
  · exact u2616

def b14716 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 52, targets := 131 }], pairs := [(2,0),(2,1),(2,7)], upper := (rows 7 259 44 200 112 48 195 131 387), lower := (rows 7 259 44 200 112 48 64 128 256), losses := [] }

theorem u14716 : Upper (D 7) (R 7) [6,257,40,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14716 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14717 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 44 200 112 160 83 147 275), lower := (rows 7 259 44 200 112 160 64 128 256), losses := [] }

theorem u14717 : Upper (D 7) (R 7) [6,257,40,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14718 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6)], upper := (rows 7 259 100 25 50 40 192 192 448), lower := (rows 7 259 100 25 50 40 64 128 256), losses := [] }

theorem u14718 : Upper (D 7) (R 7) [6,257,96,17,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14718 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14719 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 25 50 96 200 136 392), lower := (rows 7 259 100 25 50 96 64 128 256), losses := [] }

theorem u14719 : Upper (D 7) (R 7) [6,257,96,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14720 : Route 9 := (fun mask => (mask,id))

def c14720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14720 : Upper (D 7) (R 7) [6,257,96,17,34,128] 13 := by
  apply FastRouting.sound _ _ [6,257,96,17,34,128] 13 (by decide) (choices 1) [8,128] r14720 c14720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2617
  · exact u2618

def b14721 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 259 100 25 146 40 224 224 480), lower := (rows 7 259 100 25 146 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 8 17 40 108 172 300), good := (rows 470 274 484 508 146 492 64 128 256) }] }

theorem u14721 : Upper (D 7) (R 7) [6,257,96,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14721 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14722 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 25 146 96 232 168 424), lower := (rows 7 259 100 25 146 96 64 128 256), losses := [] }

theorem u14722 : Upper (D 7) (R 7) [6,257,96,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14723_8 : Upper (D 7) (R 7) [6,257,96,17,130,128,8] 13 :=
  permutation_upper _ _ _ [6,257,96,17,130,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2619

theorem m14723_32 : Upper (D 7) (R 7) [6,257,96,17,130,128,32] 13 :=
  permutation_upper _ _ _ [6,257,96,17,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2620

def r14723 : Route 9 := (fun mask => (mask,id))

def c14723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14723 : Upper (D 7) (R 7) [6,257,96,17,130,128] 13 := by
  apply FastRouting.sound _ _ [6,257,96,17,130,128] 13 (by decide) (choices 1) [8,32] r14723 c14723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14723_8
  · exact m14723_32

def b14724 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,1),(4,0)], upper := (rows 7 259 100 25 152 34 224 224 480), lower := (rows 7 259 100 25 152 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 47 8 24 35 111 175 303), good := (rows 486 486 484 508 476 486 64 128 256) },{ target := 1, region := (rows 1 0 36 11 49 32 100 164 292), good := (rows 477 281 500 25 152 508 64 128 256) }] }

theorem u14724 : Upper (D 7) (R 7) [6,257,96,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14725 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 25 152 96 226 162 418), lower := (rows 7 259 100 25 152 96 64 128 256), losses := [] }

theorem u14725 : Upper (D 7) (R 7) [6,257,96,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14726 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 228, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 7 259 100 25 152 160 98 226 354), lower := (rows 7 259 100 25 152 160 64 128 256), losses := [] }

theorem u14726 : Upper (D 7) (R 7) [6,257,96,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14727 : Route 9 := (fun mask => (mask,id))

def c14727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14727 : Upper (D 7) (R 7) [6,257,96,17,160,2] 13 := by
  apply FastRouting.sound _ _ [6,257,96,17,160,2] 13 (by decide) (choices 1) [8,128] r14727 c14727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2621
  · exact u2622

def b14728 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 387, targets := 32 }], pairs := [(0,5),(1,5),(2,0)], upper := (rows 7 259 100 25 176 40 194 194 450), lower := (rows 7 259 100 25 176 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 40 67 131 259), good := (rows 454 450 100 508 176 60 64 128 256) }] }

theorem u14728 : Upper (D 7) (R 7) [6,257,96,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14728 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14729 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 25 176 96 202 138 394), lower := (rows 7 259 100 25 176 96 64 128 256), losses := [] }

theorem u14729 : Upper (D 7) (R 7) [6,257,96,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14730 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 100 25 176 160 74 202 330), lower := (rows 7 259 100 25 176 160 64 128 256), losses := [] }

theorem u14730 : Upper (D 7) (R 7) [6,257,96,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14731 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 259 100 26 145 40 224 224 480), lower := (rows 7 259 100 26 145 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 44 8 17 40 108 172 300), good := (rows 469 273 484 508 145 492 64 128 256) }] }

theorem u14731 : Upper (D 7) (R 7) [6,257,96,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14731 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14732 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 26 145 96 232 168 424), lower := (rows 7 259 100 26 145 96 64 128 256), losses := [] }

theorem u14732 : Upper (D 7) (R 7) [6,257,96,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14733_8 : Upper (D 7) (R 7) [6,257,96,18,129,128,8] 13 :=
  permutation_upper _ _ _ [6,257,96,18,129,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2623

theorem m14733_32 : Upper (D 7) (R 7) [6,257,96,18,129,128,32] 13 :=
  permutation_upper _ _ _ [6,257,96,18,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2624

def r14733 : Route 9 := (fun mask => (mask,id))

def c14733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14733 : Upper (D 7) (R 7) [6,257,96,18,129,128] 13 := by
  apply FastRouting.sound _ _ [6,257,96,18,129,128] 13 (by decide) (choices 1) [8,32] r14733 c14733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14733_8
  · exact m14733_32

def b14734 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 259 100 26 152 33 224 224 480), lower := (rows 7 259 100 26 152 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 11 49 32 100 164 292), good := (rows 478 282 500 26 152 508 64 128 256) }] }

theorem u14734 : Upper (D 7) (R 7) [6,257,96,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14735 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 26 152 96 225 161 417), lower := (rows 7 259 100 26 152 96 64 128 256), losses := [] }

theorem u14735 : Upper (D 7) (R 7) [6,257,96,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14736 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(2,7)], upper := (rows 7 259 100 26 152 160 97 225 353), lower := (rows 7 259 100 26 152 160 64 128 256), losses := [] }

theorem u14736 : Upper (D 7) (R 7) [6,257,96,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14737 : PairBound 9 := { available := 200, camps := [], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 259 100 26 176 33 200 200 456), lower := (rows 7 259 100 26 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 52 9 52 32 107 171 299), good := (rows 478 458 500 478 500 508 64 128 256) },{ target := 1, region := (rows 1 0 12 8 24 35 72 136 264), good := (rows 37 289 100 508 176 33 64 128 256) }] }

theorem u14737 : Upper (D 7) (R 7) [6,257,96,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14738 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 387, targets := 32 }], pairs := [(0,5),(1,5),(2,1)], upper := (rows 7 259 100 26 176 40 193 193 449), lower := (rows 7 259 100 26 176 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 40 67 131 259), good := (rows 453 449 100 508 176 60 64 128 256) }] }

theorem u14738 : Upper (D 7) (R 7) [6,257,96,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14738 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14739 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 26 176 96 201 137 393), lower := (rows 7 259 100 26 176 96 64 128 256), losses := [] }

theorem u14739 : Upper (D 7) (R 7) [6,257,96,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14740 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 100 26 176 160 73 201 329), lower := (rows 7 259 100 26 176 160 64 128 256), losses := [] }

theorem u14740 : Upper (D 7) (R 7) [6,257,96,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14741 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 259 100 41 82 40 208 144 400), lower := (rows 7 259 100 41 82 40 64 128 256), losses := [] }

theorem u14741 : Upper (D 7) (R 7) [6,257,96,33,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14741 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14742 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 259 100 41 82 48 200 136 392), lower := (rows 7 259 100 41 82 48 64 128 256), losses := [] }

theorem u14742 : Upper (D 7) (R 7) [6,257,96,33,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14742 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14743 : Route 9 := (fun mask => (mask,id))

def c14743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14743 : Upper (D 7) (R 7) [6,257,96,33,66,128] 13 := by
  apply FastRouting.sound _ _ [6,257,96,33,66,128] 13 (by decide) (choices 1) [8,16,128] r14743 c14743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2625
  · exact u2626
  · exact u2627

def b14744 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 100 41 88 34 208 144 400), lower := (rows 7 259 100 41 88 34 64 128 256), losses := [] }

theorem u14744 : Upper (D 7) (R 7) [6,257,96,33,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14745 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 259 100 41 88 48 194 130 386), lower := (rows 7 259 100 41 88 48 64 128 256), losses := [] }

theorem u14745 : Upper (D 7) (R 7) [6,257,96,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14745 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14746 : Route 9 := (fun mask => (mask,id))

def c14746 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14746 : Upper (D 7) (R 7) [6,257,96,33,72,128] 13 := by
  apply FastRouting.sound _ _ [6,257,96,33,72,128] 13 (by decide) (choices 1) [2,16,128] r14746 c14746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2628
  · exact u2629
  · exact u2630

def b14747 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 259 100 41 146 40 208 208 464), lower := (rows 7 259 100 41 146 40 64 128 256), losses := [] }

theorem u14747 : Upper (D 7) (R 7) [6,257,96,33,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14747 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14748 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 196, targets := 3 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(2,0),(2,1)], upper := (rows 7 259 100 41 146 48 200 200 456), lower := (rows 7 259 100 41 146 48 64 128 256), losses := [] }

theorem u14748 : Upper (D 7) (R 7) [6,257,96,33,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14748 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14749 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 41 146 96 216 152 408), lower := (rows 7 259 100 41 146 96 64 128 256), losses := [] }

theorem u14749 : Upper (D 7) (R 7) [6,257,96,33,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14750 : Route 9 := (fun mask => (mask,id))

def c14750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14750 : Upper (D 7) (R 7) [6,257,96,33,130,128] 13 := by
  apply FastRouting.sound _ _ [6,257,96,33,130,128] 13 (by decide) (choices 1) [8,16] r14750 c14750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2631
  · exact u2632

def b14751 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 100 41 152 34 208 208 464), lower := (rows 7 259 100 41 152 34 64 128 256), losses := [] }

theorem u14751 : Upper (D 7) (R 7) [6,257,96,33,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14752 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 387, targets := 32 },{ cop := 3, region := 466, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 259 100 41 152 48 194 194 450), lower := (rows 7 259 100 41 152 48 64 128 256), losses := [] }

theorem u14752 : Upper (D 7) (R 7) [6,257,96,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14752 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14753 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 41 152 96 210 146 402), lower := (rows 7 259 100 41 152 96 64 128 256), losses := [] }

theorem u14753 : Upper (D 7) (R 7) [6,257,96,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14754 : Route 9 := (fun mask => (mask,id))

def c14754 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14754 : Upper (D 7) (R 7) [6,257,96,33,136,128] 13 := by
  apply FastRouting.sound _ _ [6,257,96,33,136,128] 13 (by decide) (choices 1) [2,16] r14754 c14754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2633
  · exact u2634

def b14755 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 100 41 208 34 216 152 408), lower := (rows 7 259 100 41 208 34 64 128 256), losses := [] }

theorem u14755 : Upper (D 7) (R 7) [6,257,96,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14756 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 259 100 41 208 40 210 146 402), lower := (rows 7 259 100 41 208 40 64 128 256), losses := [] }

theorem u14756 : Upper (D 7) (R 7) [6,257,96,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14756 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14757 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 259 100 41 208 48 202 138 394), lower := (rows 7 259 100 41 208 48 64 128 256), losses := [] }

theorem u14757 : Upper (D 7) (R 7) [6,257,96,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14757 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14758 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 4, region := 36, targets := 3 }], pairs := [(1,5),(2,0),(2,1),(4,5)], upper := (rows 7 259 100 41 208 160 90 154 282), lower := (rows 7 259 100 41 208 160 64 128 256), losses := [] }

theorem u14758 : Upper (D 7) (R 7) [6,257,96,33,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14759 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 100 42 88 33 208 144 400), lower := (rows 7 259 100 42 88 33 64 128 256), losses := [] }

theorem u14759 : Upper (D 7) (R 7) [6,257,96,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14759
end Delivery.IrregularNine14.P07
