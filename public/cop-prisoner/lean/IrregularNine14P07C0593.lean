import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0345
import IrregularNine14P07C0346
import IrregularNine14P07C0347

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35580 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35580 : Upper (D 7) (R 7) [34,257,9,192,6] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,6] 13 (by decide) (choices 1) [16,64] r35580 c35580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20741
  · exact u20742

def b35581 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 259 13 200 50 244 212 212 468), lower := (rows 35 259 13 200 50 32 64 128 256), losses := [] }

theorem u35581 : Upper (D 7) (R 7) [34,257,9,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35582 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35582 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35582 : Upper (D 7) (R 7) [34,257,9,192,36] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,36] 13 (by decide) (choices 1) [2,16,64] r35582 c35582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20743
  · exact u20744
  · exact u20745

def r35583 : Route 9 := (fun mask => (mask,id))

def c35583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35583 : Upper (D 7) (R 7) [34,257,9,192,66] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,66] 13 (by decide) (choices 1) [4,16,128] r35583 c35583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20746
  · exact u20747
  · exact u20748

def r35584 : Route 9 := (fun mask => (mask,id))

def c35584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35584 : Upper (D 7) (R 7) [34,257,9,192,68] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,68] 13 (by decide) (choices 1) [2,16,128] r35584 c35584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20749
  · exact u20750
  · exact u20751

def r35585 : Route 9 := (fun mask => (mask,id))

def c35585 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35585 : Upper (D 7) (R 7) [34,257,9,192,96] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,96] 13 (by decide) (choices 1) [2,4,16,128] r35585 c35585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20752
  · exact u20753
  · exact u20754
  · exact u20755

def b35586 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 35 259 13 200 208 54 118 182 310), lower := (rows 35 259 13 200 208 32 64 128 256), losses := [] }

theorem u35586 : Upper (D 7) (R 7) [34,257,9,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35587 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 14 28 49 224 192 192 448), lower := (rows 35 259 14 28 49 32 64 128 256), losses := [] }

theorem u35587 : Upper (D 7) (R 7) [34,257,10,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35588 : Route 9 := (fun mask => (mask,id))

def c35588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35588 : Upper (D 7) (R 7) [34,257,10,20,65] 13 := by
  apply FastRouting.sound _ _ [34,257,10,20,65] 13 (by decide) (choices 1) [64,128] r35588 c35588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20756
  · exact u20757

def r35589 : Route 9 := (fun mask => (mask,id))

def c35589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35589 : Upper (D 7) (R 7) [34,257,10,20,96] 13 := by
  apply FastRouting.sound _ _ [34,257,10,20,96] 13 (by decide) (choices 1) [1,64,128] r35589 c35589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20758
  · exact u20759
  · exact u20760

def r35590 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35590 : Upper (D 7) (R 7) [34,257,10,20,192] 13 := by
  apply FastRouting.sound _ _ [34,257,10,20,192] 13 (by decide) (choices 1) [1,64] r35590 c35590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20761
  · exact u20762

def b35591 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 14 41 84 240 208 208 464), lower := (rows 35 259 14 41 84 32 64 128 256), losses := [] }

theorem u35591 : Upper (D 7) (R 7) [34,257,10,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35592 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 14 41 208 244 212 212 468), lower := (rows 35 259 14 41 208 32 64 128 256), losses := [] }

theorem u35592 : Upper (D 7) (R 7) [34,257,10,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35593 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 14 44 81 240 208 208 464), lower := (rows 35 259 14 44 81 32 64 128 256), losses := [] }

theorem u35593 : Upper (D 7) (R 7) [34,257,10,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35594 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 14 44 208 241 209 209 465), lower := (rows 35 259 14 44 208 32 64 128 256), losses := [] }

theorem u35594 : Upper (D 7) (R 7) [34,257,10,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35595 : Route 9 := (fun mask => (mask,id))

def c35595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35595 : Upper (D 7) (R 7) [34,257,10,48,65] 13 := by
  apply FastRouting.sound _ _ [34,257,10,48,65] 13 (by decide) (choices 1) [4,64,128] r35595 c35595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20763
  · exact u20764
  · exact u20765

def b35596 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 35 259 14 56 84 225 193 193 449), lower := (rows 35 259 14 56 84 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 35 67 131 259), good := (rows 481 481 508 56 92 32 64 128 256) },{ target := 5, region := (rows 1 3 4 8 20 0 67 131 259), good := (rows 451 451 478 24 84 0 64 128 256) }] }

theorem u35596 : Upper (D 7) (R 7) [34,257,10,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35597 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35597 : Upper (D 7) (R 7) [34,257,10,48,192] 13 := by
  apply FastRouting.sound _ _ [34,257,10,48,192] 13 (by decide) (choices 1) [1,4,64] r35597 c35597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20766
  · exact u20767
  · exact u20768

def r35598 : Route 9 := (fun mask => (mask,id))

def c35598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35598 : Upper (D 7) (R 7) [34,257,10,65,36] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,36] 13 (by decide) (choices 1) [16,64,128] r35598 c35598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20769
  · exact u20770
  · exact u20771

def b35599 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 35 259 14 73 84 176 240 176 432), lower := (rows 35 259 14 73 84 32 64 128 256), losses := [] }

theorem u35599 : Upper (D 7) (R 7) [34,257,10,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35600 : Route 9 := (fun mask => (mask,id))

def c35600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35600 : Upper (D 7) (R 7) [34,257,10,65,96] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,96] 13 (by decide) (choices 1) [4,16,128] r35600 c35600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20772
  · exact u20773
  · exact u20774

def r35601 : Route 9 := (fun mask => (mask,id))

def c35601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35601 : Upper (D 7) (R 7) [34,257,10,65,132] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,132] 13 (by decide) (choices 1) [16,64,128] r35601 c35601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20775
  · exact u20776
  · exact u20777

def r35602 : Route 9 := (fun mask => (mask,id))

def c35602 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35602 : Upper (D 7) (R 7) [34,257,10,65,160] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,160] 13 (by decide) (choices 1) [4,16,64,128] r35602 c35602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20778
  · exact u20779
  · exact u20780
  · exact u20781

def r35603 : Route 9 := (fun mask => (mask,id))

def c35603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35603 : Upper (D 7) (R 7) [34,257,10,65,192] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,192] 13 (by decide) (choices 1) [4,16,128] r35603 c35603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20782
  · exact u20783
  · exact u20784

def b35604 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 35 259 14 76 49 240 208 208 464), lower := (rows 35 259 14 76 49 32 64 128 256), losses := [] }

theorem u35604 : Upper (D 7) (R 7) [34,257,10,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35605 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(1,6),(3,1),(4,1)], upper := (rows 35 259 14 76 81 176 240 176 432), lower := (rows 35 259 14 76 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 19 55 87 151 279), good := (rows 497 497 508 492 497 32 64 128 256) }] }

theorem u35605 : Upper (D 7) (R 7) [34,257,10,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35606 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 387, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(1,6),(3,1),(4,1)], upper := (rows 35 259 14 76 112 177 209 145 401), lower := (rows 35 259 14 76 112 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 23 35 67 131 259), good := (rows 497 497 508 92 112 32 64 128 256) }] }

theorem u35606 : Upper (D 7) (R 7) [34,257,10,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35607 : Route 9 := (fun mask => (mask,id))

def c35607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35607 : Upper (D 7) (R 7) [34,257,10,68,129] 13 := by
  apply FastRouting.sound _ _ [34,257,10,68,129] 13 (by decide) (choices 1) [16,64,128] r35607 c35607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20785
  · exact u20786
  · exact u20787

def r35608 : Route 9 := (fun mask => (mask,id))

def c35608 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35608 : Upper (D 7) (R 7) [34,257,10,68,160] 13 := by
  apply FastRouting.sound _ _ [34,257,10,68,160] 13 (by decide) (choices 1) [1,16,64,128] r35608 c35608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20788
  · exact u20789
  · exact u20790
  · exact u20791

def b35609 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 291, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(1,6),(3,1),(4,1)], upper := (rows 35 259 14 76 208 177 241 177 433), lower := (rows 35 259 14 76 208 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 23 35 67 131 259), good := (rows 497 497 508 92 208 32 64 128 256) }] }

theorem u35609 : Upper (D 7) (R 7) [34,257,10,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35610 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 259 14 88 49 228 196 196 452), lower := (rows 35 259 14 88 49 32 64 128 256), losses := [] }

theorem u35610 : Upper (D 7) (R 7) [34,257,10,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35611 : Route 9 := (fun mask => (mask,id))

def c35611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35611 : Upper (D 7) (R 7) [34,257,10,80,36] 13 := by
  apply FastRouting.sound _ _ [34,257,10,80,36] 13 (by decide) (choices 1) [1,64,128] r35611 c35611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20792
  · exact u20793
  · exact u20794

def b35612 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 14 88 81 164 228 164 420), lower := (rows 35 259 14 88 81 32 64 128 256), losses := [] }

theorem u35612 : Upper (D 7) (R 7) [34,257,10,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35613 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 14 88 84 161 225 161 417), lower := (rows 35 259 14 88 84 32 64 128 256), losses := [] }

theorem u35613 : Upper (D 7) (R 7) [34,257,10,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35614 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 14 88 112 165 197 133 389), lower := (rows 35 259 14 88 112 32 64 128 256), losses := [] }

theorem u35614 : Upper (D 7) (R 7) [34,257,10,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35615 : Route 9 := (fun mask => (mask,id))

def c35615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35615 : Upper (D 7) (R 7) [34,257,10,80,129] 13 := by
  apply FastRouting.sound _ _ [34,257,10,80,129] 13 (by decide) (choices 1) [4,64,128] r35615 c35615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20795
  · exact u20796
  · exact u20797

def r35616 : Route 9 := (fun mask => (mask,id))

def c35616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35616 : Upper (D 7) (R 7) [34,257,10,80,132] 13 := by
  apply FastRouting.sound _ _ [34,257,10,80,132] 13 (by decide) (choices 1) [1,64,128] r35616 c35616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20798
  · exact u20799
  · exact u20800

def r35617 : Route 9 := (fun mask => (mask,id))

def c35617 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35617 : Upper (D 7) (R 7) [34,257,10,80,160] 13 := by
  apply FastRouting.sound _ _ [34,257,10,80,160] 13 (by decide) (choices 1) [1,4,64,128] r35617 c35617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20801
  · exact u20802
  · exact u20803
  · exact u20804

def b35618 : PairBound 9 := { available := 165, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 14 88 208 165 229 165 421), lower := (rows 35 259 14 88 208 32 64 128 256), losses := [] }

theorem u35618 : Upper (D 7) (R 7) [34,257,10,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35619 : Route 9 := (fun mask => (mask,id))

def c35619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35619 : Upper (D 7) (R 7) [34,257,10,96,65] 13 := by
  apply FastRouting.sound _ _ [34,257,10,96,65] 13 (by decide) (choices 1) [4,16,128] r35619 c35619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20805
  · exact u20806
  · exact u20807

def r35620 : Route 9 := (fun mask => (mask,id))

def c35620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35620 : Upper (D 7) (R 7) [34,257,10,96,68] 13 := by
  apply FastRouting.sound _ _ [34,257,10,96,68] 13 (by decide) (choices 1) [1,16,128] r35620 c35620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20808
  · exact u20809
  · exact u20810

def r35621 : Route 9 := (fun mask => (mask,id))

def c35621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35621 : Upper (D 7) (R 7) [34,257,10,96,129] 13 := by
  apply FastRouting.sound _ _ [34,257,10,96,129] 13 (by decide) (choices 1) [4,16,64,128] r35621 c35621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20811
  · exact u20812
  · exact u20813
  · exact u20814

def r35622 : Route 9 := (fun mask => (mask,id))

def c35622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35622 : Upper (D 7) (R 7) [34,257,10,96,132] 13 := by
  apply FastRouting.sound _ _ [34,257,10,96,132] 13 (by decide) (choices 1) [1,16,64,128] r35622 c35622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20815
  · exact u20816
  · exact u20817
  · exact u20818

def r35623 : Route 9 := (fun mask => (mask,id))

def c35623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35623 : Upper (D 7) (R 7) [34,257,10,96,192] 13 := by
  apply FastRouting.sound _ _ [34,257,10,96,192] 13 (by decide) (choices 1) [1,4,16,128] r35623 c35623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20819
  · exact u20820
  · exact u20821
  · exact u20822

def b35624 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 259 14 200 49 244 212 212 468), lower := (rows 35 259 14 200 49 32 64 128 256), losses := [] }

theorem u35624 : Upper (D 7) (R 7) [34,257,10,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35625 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35625 : Upper (D 7) (R 7) [34,257,10,192,36] 13 := by
  apply FastRouting.sound _ _ [34,257,10,192,36] 13 (by decide) (choices 1) [1,16,64] r35625 c35625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20823
  · exact u20824
  · exact u20825

def r35626 : Route 9 := (fun mask => (mask,id))

def c35626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35626 : Upper (D 7) (R 7) [34,257,10,192,65] 13 := by
  apply FastRouting.sound _ _ [34,257,10,192,65] 13 (by decide) (choices 1) [4,16,128] r35626 c35626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20826
  · exact u20827
  · exact u20828

def r35627 : Route 9 := (fun mask => (mask,id))

def c35627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35627 : Upper (D 7) (R 7) [34,257,10,192,68] 13 := by
  apply FastRouting.sound _ _ [34,257,10,192,68] 13 (by decide) (choices 1) [1,16,128] r35627 c35627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20829
  · exact u20830
  · exact u20831

def r35628 : Route 9 := (fun mask => (mask,id))

def c35628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35628 : Upper (D 7) (R 7) [34,257,10,192,96] 13 := by
  apply FastRouting.sound _ _ [34,257,10,192,96] 13 (by decide) (choices 1) [1,4,16,128] r35628 c35628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20832
  · exact u20833
  · exact u20834
  · exact u20835

def b35629 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 35 259 14 200 208 53 117 181 309), lower := (rows 35 259 14 200 208 32 64 128 256), losses := [] }

theorem u35629 : Upper (D 7) (R 7) [34,257,10,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35630 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 259 28 41 82 228 196 196 452), lower := (rows 35 259 28 41 82 32 64 128 256), losses := [] }

theorem u35630 : Upper (D 7) (R 7) [34,257,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35631 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 259 28 41 84 226 194 194 450), lower := (rows 35 259 28 41 84 32 64 128 256), losses := [] }

theorem u35631 : Upper (D 7) (R 7) [34,257,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35632 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 259 28 41 208 230 198 198 454), lower := (rows 35 259 28 41 208 32 64 128 256), losses := [] }

theorem u35632 : Upper (D 7) (R 7) [34,257,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35633 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 259 28 42 81 228 196 196 452), lower := (rows 35 259 28 42 81 32 64 128 256), losses := [] }

theorem u35633 : Upper (D 7) (R 7) [34,257,24,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35634 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 259 28 42 84 225 193 193 449), lower := (rows 35 259 28 42 84 32 64 128 256), losses := [] }

theorem u35634 : Upper (D 7) (R 7) [34,257,24,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35635 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 259 28 42 208 229 197 197 453), lower := (rows 35 259 28 42 208 32 64 128 256), losses := [] }

theorem u35635 : Upper (D 7) (R 7) [34,257,24,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35636 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 35 259 28 44 81 226 194 194 450), lower := (rows 35 259 28 44 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 482 482 28 44 508 32 64 128 256) }] }

theorem u35636 : Upper (D 7) (R 7) [34,257,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35637 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,5)], upper := (rows 35 259 28 44 82 225 193 193 449), lower := (rows 35 259 28 44 82 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 481 481 28 44 508 32 64 128 256) }] }

theorem u35637 : Upper (D 7) (R 7) [34,257,24,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35638 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35638 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35638 : Upper (D 7) (R 7) [34,257,24,36,192] 13 := by
  apply FastRouting.sound _ _ [34,257,24,36,192] 13 (by decide) (choices 1) [1,2,64] r35638 c35638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20836
  · exact u20837
  · exact u20838

def r35639 : Route 9 := (fun mask => (mask,id))

def c35639 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35639 : Upper (D 7) (R 7) [34,257,24,65,66] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,66] 13 (by decide) (choices 1) [4,128] r35639 c35639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20839
  · exact u20840

#print axioms u35639
end Delivery.IrregularNine14.P07
