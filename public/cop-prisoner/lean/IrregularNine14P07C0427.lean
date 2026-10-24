import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0149
import IrregularNine14P07C0150

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25620 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 259 13 26 208 34 224 224 480), lower := (rows 37 259 13 26 208 34 64 128 256), losses := [] }

theorem u25620 : Upper (D 7) (R 7) [36,257,9,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25621 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,1),(1,6),(3,0),(4,0)], upper := (rows 37 259 13 26 208 96 226 162 418), lower := (rows 37 259 13 26 208 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 112 64 128 256), good := (rows 37 257 13 61 240 96 96 128 256) }] }

theorem u25621 : Upper (D 7) (R 7) [36,257,9,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25622 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 259 13 74 50 48 192 192 448), lower := (rows 37 259 13 74 50 48 64 128 256), losses := [] }

theorem u25622 : Upper (D 7) (R 7) [36,257,9,66,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25622 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25623 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 0, region := 402, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(4,7)], upper := (rows 37 259 13 74 50 96 208 144 400), lower := (rows 37 259 13 74 50 96 64 128 256), losses := [] }

theorem u25623 : Upper (D 7) (R 7) [36,257,9,66,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25624 : Route 9 := (fun mask => (mask,id))

def c25624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25624 : Upper (D 7) (R 7) [36,257,9,66,34,128] 13 := by
  apply FastRouting.sound _ _ [36,257,9,66,34,128] 13 (by decide) (choices 1) [16,128] r25624 c25624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8980
  · exact u8981

def b25625 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 37 259 13 74 112 34 208 144 400), lower := (rows 37 259 13 74 112 34 64 128 256), losses := [] }

theorem u25625 : Upper (D 7) (R 7) [36,257,9,66,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25626 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 53, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 13 74 112 48 194 130 386), lower := (rows 37 259 13 74 112 48 64 128 256), losses := [] }

theorem u25626 : Upper (D 7) (R 7) [36,257,9,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25626 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25627 : Route 9 := (fun mask => (mask,id))

def c25627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25627 : Upper (D 7) (R 7) [36,257,9,66,96,128] 13 := by
  apply FastRouting.sound _ _ [36,257,9,66,96,128] 13 (by decide) (choices 1) [2,16,128] r25627 c25627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8982
  · exact u8983
  · exact u8984

def r25628 : Route 9 := (fun mask => (mask,id))

def c25628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25628 : Upper (D 7) (R 7) [36,257,9,66,130,16] 13 := by
  apply FastRouting.sound _ _ [36,257,9,66,130,16] 13 (by decide) (choices 1) [32,128] r25628 c25628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8985
  · exact u8986

def b25629 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 13 74 146 96 240 176 432), lower := (rows 37 259 13 74 146 96 64 128 256), losses := [] }

theorem u25629 : Upper (D 7) (R 7) [36,257,9,66,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25630 : Route 9 := (fun mask => (mask,id))

def c25630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25630 : Upper (D 7) (R 7) [36,257,9,66,130,128] 13 := by
  apply FastRouting.sound _ _ [36,257,9,66,130,128] 13 (by decide) (choices 1) [16,32] r25630 c25630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8987
  · exact u8988

def b25631 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 259 13 74 176 34 208 208 464), lower := (rows 37 259 13 74 176 34 64 128 256), losses := [] }

theorem u25631 : Upper (D 7) (R 7) [36,257,9,66,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25632 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 13 74 176 48 194 194 450), lower := (rows 37 259 13 74 176 48 64 128 256), losses := [] }

theorem u25632 : Upper (D 7) (R 7) [36,257,9,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25632 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25633 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 13 74 176 96 210 146 402), lower := (rows 37 259 13 74 176 96 64 128 256), losses := [] }

theorem u25633 : Upper (D 7) (R 7) [36,257,9,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25634 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 13 74 176 160 82 210 338), lower := (rows 37 259 13 74 176 160 64 128 256), losses := [] }

theorem u25634 : Upper (D 7) (R 7) [36,257,9,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25635 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 259 13 74 208 34 240 176 432), lower := (rows 37 259 13 74 208 34 64 128 256), losses := [] }

theorem u25635 : Upper (D 7) (R 7) [36,257,9,66,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25636 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 37 259 13 74 208 48 226 162 418), lower := (rows 37 259 13 74 208 48 64 128 256), losses := [] }

theorem u25636 : Upper (D 7) (R 7) [36,257,9,66,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25636 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25637 : Route 9 := (fun mask => (mask,id))

def c25637 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25637 : Upper (D 7) (R 7) [36,257,9,66,192,128] 13 := by
  apply FastRouting.sound _ _ [36,257,9,66,192,128] 13 (by decide) (choices 1) [2,16,32] r25637 c25637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8989
  · exact u8990
  · exact u8991

def b25638 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 37 259 13 88 146 34 224 224 480), lower := (rows 37 259 13 88 146 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 128 256), good := (rows 37 291 13 61 178 34 0 128 256) }] }

theorem u25638 : Upper (D 7) (R 7) [36,257,9,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25639 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 13 88 146 96 226 162 418), lower := (rows 37 259 13 88 146 96 64 128 256), losses := [] }

theorem u25639 : Upper (D 7) (R 7) [36,257,9,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25640 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(1,7),(3,0),(4,0)], upper := (rows 37 259 13 88 146 160 98 226 354), lower := (rows 37 259 13 88 146 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 257 13 125 176 160 64 160 256) }] }

theorem u25640 : Upper (D 7) (R 7) [36,257,9,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25641 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,0),(3,5),(4,0)], upper := (rows 37 259 13 88 176 34 194 194 450), lower := (rows 37 259 13 88 176 34 64 128 256), losses := [{ target := 5, region := (rows 1 7 4 24 16 0 103 167 295), good := (rows 455 451 463 88 472 450 64 128 256) }] }

theorem u25641 : Upper (D 7) (R 7) [36,257,9,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25642 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 13 88 176 96 194 130 386), lower := (rows 37 259 13 88 176 96 64 128 256), losses := [] }

theorem u25642 : Upper (D 7) (R 7) [36,257,9,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25643 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 13 88 176 160 66 194 322), lower := (rows 37 259 13 88 176 160 64 128 256), losses := [] }

theorem u25643 : Upper (D 7) (R 7) [36,257,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25644 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 205, targets := 2 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(3,1)], upper := (rows 37 259 13 200 50 34 208 208 464), lower := (rows 37 259 13 200 50 34 64 128 256), losses := [] }

theorem u25644 : Upper (D 7) (R 7) [36,257,9,192,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25645 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 13 200 50 48 194 194 450), lower := (rows 37 259 13 200 50 48 64 128 256), losses := [] }

theorem u25645 : Upper (D 7) (R 7) [36,257,9,192,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25645 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25646 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 13 200 50 96 210 146 402), lower := (rows 37 259 13 200 50 96 64 128 256), losses := [] }

theorem u25646 : Upper (D 7) (R 7) [36,257,9,192,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25647 : Route 9 := (fun mask => (mask,id))

def c25647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u25647 : Upper (D 7) (R 7) [36,257,9,192,66,2] 13 := by
  apply FastRouting.sound _ _ [36,257,9,192,66,2] 13 (by decide) (choices 1) [16,32,128] r25647 c25647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8992
  · exact u8993
  · exact u8994

def b25648 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 37 259 13 200 82 48 226 162 418), lower := (rows 37 259 13 200 82 48 64 128 256), losses := [] }

theorem u25648 : Upper (D 7) (R 7) [36,257,9,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25648 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25649 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 259 13 200 82 160 114 178 306), lower := (rows 37 259 13 200 82 160 64 128 256), losses := [] }

theorem u25649 : Upper (D 7) (R 7) [36,257,9,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25650 : Route 9 := (fun mask => (mask,id))

def c25650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25650 : Upper (D 7) (R 7) [36,257,9,192,96,2] 13 := by
  apply FastRouting.sound _ _ [36,257,9,192,96,2] 13 (by decide) (choices 1) [2,16,128] r25650 c25650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8995
  · exact u8996
  · exact u8997

def b25651 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 53, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 13 200 112 48 194 130 386), lower := (rows 37 259 13 200 112 48 64 128 256), losses := [] }

theorem u25651 : Upper (D 7) (R 7) [36,257,9,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25651 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25652 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 53, targets := 2 },{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(4,1)], upper := (rows 37 259 13 200 112 160 82 146 274), lower := (rows 37 259 13 200 112 160 64 128 256), losses := [] }

theorem u25652 : Upper (D 7) (R 7) [36,257,9,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25653 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 37 259 14 25 82 96 224 160 416), lower := (rows 37 259 14 25 82 96 64 128 256), losses := [] }

theorem u25653 : Upper (D 7) (R 7) [36,257,10,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25654 : Route 9 := (fun mask => (mask,id))

def c25654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25654 : Upper (D 7) (R 7) [36,257,10,17,66,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,17,66,128] 13 (by decide) (choices 1) [32,128] r25654 c25654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8998
  · exact u8999

def b25655 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 14 25 112 34 192 192 448), lower := (rows 37 259 14 25 112 34 64 128 256), losses := [] }

theorem u25655 : Upper (D 7) (R 7) [36,257,10,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25656 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 37 259 14 25 112 96 194 130 386), lower := (rows 37 259 14 25 112 96 64 128 256), losses := [] }

theorem u25656 : Upper (D 7) (R 7) [36,257,10,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25657 : Route 9 := (fun mask => (mask,id))

def c25657 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25657 : Upper (D 7) (R 7) [36,257,10,17,96,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,17,96,128] 13 (by decide) (choices 1) [2,128] r25657 c25657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9000
  · exact u9001

def b25658 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 14 25 208 34 224 224 480), lower := (rows 37 259 14 25 208 34 64 128 256), losses := [] }

theorem u25658 : Upper (D 7) (R 7) [36,257,10,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25659 : Route 9 := (fun mask => (mask,id))

def c25659 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25659 : Upper (D 7) (R 7) [36,257,10,17,192,64] 13 := by
  apply FastRouting.sound _ _ [36,257,10,17,192,64] 13 (by decide) (choices 1) [2,32,128] r25659 c25659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9002
  · exact u9003
  · exact u9004

def b25660 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 259 14 56 81 34 192 192 448), lower := (rows 37 259 14 56 81 34 64 128 256), losses := [] }

theorem u25660 : Upper (D 7) (R 7) [36,257,10,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25661 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 37 259 14 56 81 96 194 130 386), lower := (rows 37 259 14 56 81 96 64 128 256), losses := [] }

theorem u25661 : Upper (D 7) (R 7) [36,257,10,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25662 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 37 259 14 56 81 160 194 194 450), lower := (rows 37 259 14 56 81 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 167 70 134 262), good := (rows 484 482 494 56 120 160 64 160 256) },{ target := 5, region := (rows 1 19 12 8 19 0 95 159 287), good := (rows 471 467 478 478 467 128 64 128 256) }] }

theorem u25662 : Upper (D 7) (R 7) [36,257,10,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25663 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 259 14 56 208 33 194 194 450), lower := (rows 37 259 14 56 208 33 64 128 256), losses := [] }

theorem u25663 : Upper (D 7) (R 7) [36,257,10,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25664 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 259 14 56 208 34 193 193 449), lower := (rows 37 259 14 56 208 34 64 128 256), losses := [] }

theorem u25664 : Upper (D 7) (R 7) [36,257,10,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25665 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 37 259 14 56 208 96 195 131 387), lower := (rows 37 259 14 56 208 96 64 128 256), losses := [] }

theorem u25665 : Upper (D 7) (R 7) [36,257,10,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25666 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 259 14 73 50 48 192 192 448), lower := (rows 37 259 14 73 50 48 64 128 256), losses := [] }

theorem u25666 : Upper (D 7) (R 7) [36,257,10,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25666 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25667 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,1),(1,6),(4,0),(4,6)], upper := (rows 37 259 14 73 50 96 208 144 400), lower := (rows 37 259 14 73 50 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 120 80 144 272), good := (rows 37 257 45 105 496 96 96 128 256) }] }

theorem u25667 : Upper (D 7) (R 7) [36,257,10,65,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25668 : Route 9 := (fun mask => (mask,id))

def c25668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25668 : Upper (D 7) (R 7) [36,257,10,65,34,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,34,128] 13 (by decide) (choices 1) [16,128] r25668 c25668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9005
  · exact u9006

def b25669 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 259 14 73 82 48 224 160 416), lower := (rows 37 259 14 73 82 48 64 128 256), losses := [] }

theorem u25669 : Upper (D 7) (R 7) [36,257,10,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25669 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25670 : Route 9 := (fun mask => (mask,id))

def c25670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u25670 : Upper (D 7) (R 7) [36,257,10,65,66,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,66,128] 13 (by decide) (choices 1) [16,32,128] r25670 c25670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9007
  · exact u9008
  · exact u9009

def b25671 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 14 73 112 34 208 144 400), lower := (rows 37 259 14 73 112 34 64 128 256), losses := [] }

theorem u25671 : Upper (D 7) (R 7) [36,257,10,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25672 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 14 73 112 48 194 130 386), lower := (rows 37 259 14 73 112 48 64 128 256), losses := [] }

theorem u25672 : Upper (D 7) (R 7) [36,257,10,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25672 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25673 : Route 9 := (fun mask => (mask,id))

def c25673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25673 : Upper (D 7) (R 7) [36,257,10,65,96,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,96,128] 13 (by decide) (choices 1) [2,16,128] r25673 c25673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9010
  · exact u9011
  · exact u9012

def r25674 : Route 9 := (fun mask => (mask,id))

def c25674 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25674 : Upper (D 7) (R 7) [36,257,10,65,130,16] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,130,16] 13 (by decide) (choices 1) [32,128] r25674 c25674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9013
  · exact u9014

def b25675 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,1),(1,6),(4,0),(4,6)], upper := (rows 37 259 14 73 146 96 240 176 432), lower := (rows 37 259 14 73 146 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 120 80 144 272), good := (rows 37 257 45 105 496 96 96 128 256) }] }

theorem u25675 : Upper (D 7) (R 7) [36,257,10,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25676 : Route 9 := (fun mask => (mask,id))

def c25676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25676 : Upper (D 7) (R 7) [36,257,10,65,130,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,130,128] 13 (by decide) (choices 1) [16,32] r25676 c25676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9015
  · exact u9016

def b25677 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 14 73 176 34 208 208 464), lower := (rows 37 259 14 73 176 34 64 128 256), losses := [] }

theorem u25677 : Upper (D 7) (R 7) [36,257,10,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25678 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 14 73 176 48 194 194 450), lower := (rows 37 259 14 73 176 48 64 128 256), losses := [] }

theorem u25678 : Upper (D 7) (R 7) [36,257,10,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25678 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25679 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,1),(1,6),(4,0),(4,6)], upper := (rows 37 259 14 73 176 96 210 146 402), lower := (rows 37 259 14 73 176 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 104 64 128 256), good := (rows 37 257 45 105 176 96 96 128 256) }] }

theorem u25679 : Upper (D 7) (R 7) [36,257,10,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u25679
end Delivery.IrregularNine14.P07
