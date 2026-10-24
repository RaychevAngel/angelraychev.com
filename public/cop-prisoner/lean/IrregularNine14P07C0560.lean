import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0294
import IrregularNine14P07C0295
import IrregularNine14P07C0296

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33600 : Route 9 := (fun mask => (mask,id))

def c33600 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33600 : Upper (D 7) (R 7) [12,288,18,192,96] 13 := by
  apply FastRouting.sound _ _ [12,288,18,192,96] 13 (by decide) (choices 1) [1,2,128] r33600 c33600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17687
  · exact u17688
  · exact u17689

def b33601 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 290 22 200 208 35 99 163 291), lower := (rows 13 290 22 200 208 32 64 128 256), losses := [] }

theorem u33601 : Upper (D 7) (R 7) [12,288,18,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33602 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 208, targets := 32 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,5)], upper := (rows 13 290 37 73 82 178 210 146 402), lower := (rows 13 290 37 73 82 32 64 128 256), losses := [] }

theorem u33602 : Upper (D 7) (R 7) [12,288,33,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33603 : Route 9 := (fun mask => (mask,id))

def c33603 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33603 : Upper (D 7) (R 7) [12,288,33,65,130] 13 := by
  apply FastRouting.sound _ _ [12,288,33,65,130] 13 (by decide) (choices 1) [2,16,64,128] r33603 c33603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17690
  · exact u17691
  · exact u17692
  · exact u17693

def b33604 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 208, targets := 32 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,5)], upper := (rows 13 290 37 73 208 178 210 146 402), lower := (rows 13 290 37 73 208 32 64 128 256), losses := [] }

theorem u33604 : Upper (D 7) (R 7) [12,288,33,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33605 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 228, targets := 2 },{ cop := 4, region := 200, targets := 32 }], pairs := [(1,0),(2,1),(3,0),(3,5)], upper := (rows 13 290 37 74 19 240 208 208 464), lower := (rows 13 290 37 74 19 32 64 128 256), losses := [] }

theorem u33605 : Upper (D 7) (R 7) [12,288,33,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33606 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,0),(1,6),(2,6),(3,0)], upper := (rows 13 290 37 74 81 178 210 146 402), lower := (rows 13 290 37 74 81 32 64 128 256), losses := [] }

theorem u33606 : Upper (D 7) (R 7) [12,288,33,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33607 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 161 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,7)], upper := (rows 13 290 37 74 82 177 209 145 401), lower := (rows 13 290 37 74 82 32 64 128 256), losses := [] }

theorem u33607 : Upper (D 7) (R 7) [12,288,33,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33608 : Route 9 := (fun mask => (mask,id))

def c33608 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33608 : Upper (D 7) (R 7) [12,288,33,66,129] 13 := by
  apply FastRouting.sound _ _ [12,288,33,66,129] 13 (by decide) (choices 1) [2,16,64,128] r33608 c33608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17694
  · exact u17695
  · exact u17696
  · exact u17697

def r33609 : Route 9 := (fun mask => (mask,id))

def c33609 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33609 : Upper (D 7) (R 7) [12,288,33,66,130] 13 := by
  apply FastRouting.sound _ _ [12,288,33,66,130] 13 (by decide) (choices 1) [1,16,64,128] r33609 c33609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17698
  · exact u17699
  · exact u17700
  · exact u17701

def r33610 : Route 9 := (fun mask => (mask,id))

def c33610 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33610 : Upper (D 7) (R 7) [12,288,33,66,192] 13 := by
  apply FastRouting.sound _ _ [12,288,33,66,192] 13 (by decide) (choices 1) [1,2,16,128] r33610 c33610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17702
  · exact u17703
  · exact u17704
  · exact u17705

def r33611 : Route 9 := (fun mask => (mask,id))

def c33611 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33611 : Upper (D 7) (R 7) [12,288,33,80,3] 13 := by
  apply FastRouting.sound _ _ [12,288,33,80,3] 13 (by decide) (choices 1) [2,64,128] r33611 c33611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17706
  · exact u17707
  · exact u17708

def b33612 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 423, targets := 64 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,6),(1,6),(2,6),(3,1)], upper := (rows 13 290 37 88 81 162 194 130 386), lower := (rows 13 290 37 88 81 32 64 128 256), losses := [] }

theorem u33612 : Upper (D 7) (R 7) [12,288,33,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33613 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 13 290 37 88 82 163 195 131 387), lower := (rows 13 290 37 88 82 32 64 128 256), losses := [] }

theorem u33613 : Upper (D 7) (R 7) [12,288,33,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33614 : Route 9 := (fun mask => (mask,id))

def c33614 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33614 : Upper (D 7) (R 7) [12,288,33,80,129] 13 := by
  apply FastRouting.sound _ _ [12,288,33,80,129] 13 (by decide) (choices 1) [2,64,128] r33614 c33614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17709
  · exact u17710
  · exact u17711

def r33615 : Route 9 := (fun mask => (mask,id))

def c33615 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33615 : Upper (D 7) (R 7) [12,288,33,80,130] 13 := by
  apply FastRouting.sound _ _ [12,288,33,80,130] 13 (by decide) (choices 1) [1,2,64,128] r33615 c33615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17712
  · exact u17713
  · exact u17714
  · exact u17715

def b33616 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 13 290 37 88 208 163 195 131 387), lower := (rows 13 290 37 88 208 32 64 128 256), losses := [] }

theorem u33616 : Upper (D 7) (R 7) [12,288,33,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33617 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33617 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33617 : Upper (D 7) (R 7) [12,288,33,192,3] 13 := by
  apply FastRouting.sound _ _ [12,288,33,192,3] 13 (by decide) (choices 1) [2,16,64] r33617 c33617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17716
  · exact u17717
  · exact u17718

def b33618 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,0),(1,6),(2,6),(3,0)], upper := (rows 13 290 37 200 81 178 210 146 402), lower := (rows 13 290 37 200 81 32 64 128 256), losses := [] }

theorem u33618 : Upper (D 7) (R 7) [12,288,33,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33619 : Route 9 := (fun mask => (mask,id))

def c33619 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33619 : Upper (D 7) (R 7) [12,288,33,192,66] 13 := by
  apply FastRouting.sound _ _ [12,288,33,192,66] 13 (by decide) (choices 1) [1,2,16,128] r33619 c33619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17719
  · exact u17720
  · exact u17721
  · exact u17722

def b33620 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 290 37 200 208 51 83 147 275), lower := (rows 13 290 37 200 208 32 64 128 256), losses := [] }

theorem u33620 : Upper (D 7) (R 7) [12,288,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33621 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 200, targets := 32 }], pairs := [(0,5),(1,0),(2,0),(3,5)], upper := (rows 13 290 52 73 19 226 194 194 450), lower := (rows 13 290 52 73 19 32 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 28 16 0 82 146 274), good := (rows 13 450 477 73 475 0 64 128 256) }] }

theorem u33621 : Upper (D 7) (R 7) [12,288,48,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33622 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,7)], upper := (rows 13 290 52 73 81 162 194 130 386), lower := (rows 13 290 52 73 81 32 64 128 256), losses := [] }

theorem u33622 : Upper (D 7) (R 7) [12,288,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33623 : Route 9 := (fun mask => (mask,id))

def c33623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33623 : Upper (D 7) (R 7) [12,288,48,65,66] 13 := by
  apply FastRouting.sound _ _ [12,288,48,65,66] 13 (by decide) (choices 1) [1,2,128] r33623 c33623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17723
  · exact u17724
  · exact u17725

def r33624 : Route 9 := (fun mask => (mask,id))

def c33624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33624 : Upper (D 7) (R 7) [12,288,48,65,129] 13 := by
  apply FastRouting.sound _ _ [12,288,48,65,129] 13 (by decide) (choices 1) [2,64,128] r33624 c33624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17726
  · exact u17727
  · exact u17728

def r33625 : Route 9 := (fun mask => (mask,id))

def c33625 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33625 : Upper (D 7) (R 7) [12,288,48,65,130] 13 := by
  apply FastRouting.sound _ _ [12,288,48,65,130] 13 (by decide) (choices 1) [1,2,64,128] r33625 c33625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17729
  · exact u17730
  · exact u17731
  · exact u17732

def r33626 : Route 9 := (fun mask => (mask,id))

def c33626 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33626 : Upper (D 7) (R 7) [12,288,48,65,192] 13 := by
  apply FastRouting.sound _ _ [12,288,48,65,192] 13 (by decide) (choices 1) [1,2,128] r33626 c33626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17733
  · exact u17734
  · exact u17735

def r33627 : Route 9 := (fun mask => (mask,id))

def c33627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33627 : Upper (D 7) (R 7) [12,288,48,66,3] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66,3] 13 (by decide) (choices 1) [1,64,128] r33627 c33627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17736
  · exact u17737
  · exact u17738

def r33628 : Route 9 := (fun mask => (mask,id))

def c33628 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33628 : Upper (D 7) (R 7) [12,288,48,66,65] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66,65] 13 (by decide) (choices 1) [1,2,128] r33628 c33628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17739
  · exact u17740
  · exact u17741

def b33629 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 16, targets := 161 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,7)], upper := (rows 13 290 52 74 82 161 193 129 385), lower := (rows 13 290 52 74 82 32 64 128 256), losses := [] }

theorem u33629 : Upper (D 7) (R 7) [12,288,48,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33630 : Route 9 := (fun mask => (mask,id))

def c33630 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33630 : Upper (D 7) (R 7) [12,288,48,66,129] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66,129] 13 (by decide) (choices 1) [1,2,64,128] r33630 c33630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17742
  · exact u17743
  · exact u17744
  · exact u17745

def r33631 : Route 9 := (fun mask => (mask,id))

def c33631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33631 : Upper (D 7) (R 7) [12,288,48,66,130] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66,130] 13 (by decide) (choices 1) [1,64,128] r33631 c33631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17746
  · exact u17747
  · exact u17748

def r33632 : Route 9 := (fun mask => (mask,id))

def c33632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33632 : Upper (D 7) (R 7) [12,288,48,66,192] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66,192] 13 (by decide) (choices 1) [1,2,128] r33632 c33632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17749
  · exact u17750
  · exact u17751

def r33633 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33633 : Upper (D 7) (R 7) [12,288,48,192,3] 13 := by
  apply FastRouting.sound _ _ [12,288,48,192,3] 13 (by decide) (choices 1) [1,2,64] r33633 c33633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17752
  · exact u17753
  · exact u17754

def r33634 : Route 9 := (fun mask => (mask,id))

def c33634 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33634 : Upper (D 7) (R 7) [12,288,48,192,65] 13 := by
  apply FastRouting.sound _ _ [12,288,48,192,65] 13 (by decide) (choices 1) [1,2,128] r33634 c33634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17755
  · exact u17756
  · exact u17757

def r33635 : Route 9 := (fun mask => (mask,id))

def c33635 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33635 : Upper (D 7) (R 7) [12,288,48,192,66] 13 := by
  apply FastRouting.sound _ _ [12,288,48,192,66] 13 (by decide) (choices 1) [1,2,128] r33635 c33635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17758
  · exact u17759
  · exact u17760

def b33636 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 290 52 200 208 35 67 131 259), lower := (rows 13 290 52 200 208 32 64 128 256), losses := [] }

theorem u33636 : Upper (D 7) (R 7) [12,288,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33637 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 205, targets := 32 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 290 69 137 50 242 210 210 466), lower := (rows 13 290 69 137 50 32 64 128 256), losses := [] }

theorem u33637 : Upper (D 7) (R 7) [12,288,65,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33638 : Route 9 := (fun mask => (mask,id))

def c33638 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33638 : Upper (D 7) (R 7) [12,288,65,129,66] 13 := by
  apply FastRouting.sound _ _ [12,288,65,129,66] 13 (by decide) (choices 1) [2,16,128] r33638 c33638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17761
  · exact u17762
  · exact u17763

def r33639 : Route 9 := (fun mask => (mask,id))

def c33639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33639 : Upper (D 7) (R 7) [12,288,65,129,96] 13 := by
  apply FastRouting.sound _ _ [12,288,65,129,96] 13 (by decide) (choices 1) [2,16,128] r33639 c33639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17764
  · exact u17765
  · exact u17766

def b33640 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 13, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 69 137 208 50 114 178 306), lower := (rows 13 290 69 137 208 32 64 128 256), losses := [] }

theorem u33640 : Upper (D 7) (R 7) [12,288,65,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33641 : Route 9 := (fun mask => (mask,id))

def c33641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33641 : Upper (D 7) (R 7) [12,288,65,130,3] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,3] 13 (by decide) (choices 1) [16,64,128] r33641 c33641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17767
  · exact u17768
  · exact u17769

def r33642 : Route 9 := (fun mask => (mask,id))

def c33642 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33642 : Upper (D 7) (R 7) [12,288,65,130,33] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,33] 13 (by decide) (choices 1) [2,16,64,128] r33642 c33642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17770
  · exact u17771
  · exact u17772
  · exact u17773

def b33643 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 290 69 138 50 241 209 209 465), lower := (rows 13 290 69 138 50 32 64 128 256), losses := [] }

theorem u33643 : Upper (D 7) (R 7) [12,288,65,130,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33644 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 13 290 69 138 81 178 242 178 434), lower := (rows 13 290 69 138 81 32 64 128 256), losses := [] }

theorem u33644 : Upper (D 7) (R 7) [12,288,65,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33645 : Route 9 := (fun mask => (mask,id))

def c33645 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33645 : Upper (D 7) (R 7) [12,288,65,130,66] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,66] 13 (by decide) (choices 1) [1,16,128] r33645 c33645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17774
  · exact u17775
  · exact u17776

def r33646 : Route 9 := (fun mask => (mask,id))

def c33646 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33646 : Upper (D 7) (R 7) [12,288,65,130,96] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,96] 13 (by decide) (choices 1) [1,2,16,128] r33646 c33646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17777
  · exact u17778
  · exact u17779
  · exact u17780

def b33647 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 290 69 138 145 114 114 242 370), lower := (rows 13 290 69 138 145 32 64 128 256), losses := [] }

theorem u33647 : Upper (D 7) (R 7) [12,288,65,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33648 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 13 290 69 138 146 113 113 241 369), lower := (rows 13 290 69 138 146 32 64 128 256), losses := [] }

theorem u33648 : Upper (D 7) (R 7) [12,288,65,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33649 : Route 9 := (fun mask => (mask,id))

def c33649 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33649 : Upper (D 7) (R 7) [12,288,65,130,160] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,160] 13 (by decide) (choices 1) [1,2,16,64] r33649 c33649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17781
  · exact u17782
  · exact u17783
  · exact u17784

def r33650 : Route 9 := (fun mask => (mask,id))

def c33650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33650 : Upper (D 7) (R 7) [12,288,65,130,192] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,192] 13 (by decide) (choices 1) [1,2,16] r33650 c33650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17785
  · exact u17786
  · exact u17787

def r33651 : Route 9 := (fun mask => (mask,id))

def c33651 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33651 : Upper (D 7) (R 7) [12,288,65,144,3] 13 := by
  apply FastRouting.sound _ _ [12,288,65,144,3] 13 (by decide) (choices 1) [2,64,128] r33651 c33651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17788
  · exact u17789
  · exact u17790

def r33652 : Route 9 := (fun mask => (mask,id))

def c33652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33652 : Upper (D 7) (R 7) [12,288,65,144,33] 13 := by
  apply FastRouting.sound _ _ [12,288,65,144,33] 13 (by decide) (choices 1) [2,64,128] r33652 c33652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17791
  · exact u17792
  · exact u17793

def b33653 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 290 69 152 50 227 195 195 451), lower := (rows 13 290 69 152 50 32 64 128 256), losses := [] }

theorem u33653 : Upper (D 7) (R 7) [12,288,65,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33654 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 13 290 69 152 81 162 226 162 418), lower := (rows 13 290 69 152 81 32 64 128 256), losses := [] }

theorem u33654 : Upper (D 7) (R 7) [12,288,65,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33655 : Route 9 := (fun mask => (mask,id))

def c33655 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33655 : Upper (D 7) (R 7) [12,288,65,144,66] 13 := by
  apply FastRouting.sound _ _ [12,288,65,144,66] 13 (by decide) (choices 1) [1,2,128] r33655 c33655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17794
  · exact u17795
  · exact u17796

def r33656 : Route 9 := (fun mask => (mask,id))

def c33656 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33656 : Upper (D 7) (R 7) [12,288,65,144,96] 13 := by
  apply FastRouting.sound _ _ [12,288,65,144,96] 13 (by decide) (choices 1) [1,2,128] r33656 c33656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17797
  · exact u17798
  · exact u17799

def b33657 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 13 290 69 152 145 98 98 226 354), lower := (rows 13 290 69 152 145 32 64 128 256), losses := [] }

theorem u33657 : Upper (D 7) (R 7) [12,288,65,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33658 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 290 69 152 146 99 99 227 355), lower := (rows 13 290 69 152 146 32 64 128 256), losses := [] }

theorem u33658 : Upper (D 7) (R 7) [12,288,65,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33659 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 290 69 152 176 99 67 195 323), lower := (rows 13 290 69 152 176 32 64 128 256), losses := [] }

theorem u33659 : Upper (D 7) (R 7) [12,288,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u33659
end Delivery.IrregularNine14.P07
