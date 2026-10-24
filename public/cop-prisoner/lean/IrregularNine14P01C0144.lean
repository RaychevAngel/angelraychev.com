import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0093
import IrregularNine14P01C0094
import IrregularNine14P01C0095

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8640 : Route 9 := (fun mask => (mask,id))

def c8640 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8640 : Upper (D 1) (R 1) [304,80,65,160] 13 := by
  apply FastRouting.sound _ _ [304,80,65,160] 13 (by decide) (choices 1) [2,4,8,128] r8640 c8640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5635
  · exact u5636
  · exact u5637
  · exact u5638

def b8641 : PairBound 9 := { available := 174, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 70 137 190 174 238 174 430), lower := (rows 305 82 70 137 16 32 64 128 256), losses := [] }

theorem u8641 : Upper (D 1) (R 1) [304,80,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8641
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8642 : PairBound 9 := { available := 173, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 70 138 189 173 237 173 429), lower := (rows 305 82 70 138 16 32 64 128 256), losses := [] }

theorem u8642 : Upper (D 1) (R 1) [304,80,66,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8642
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8643 : PairBound 9 := { available := 171, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 70 140 187 171 235 171 427), lower := (rows 305 82 70 140 16 32 64 128 256), losses := [] }

theorem u8643 : Upper (D 1) (R 1) [304,80,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8643
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8644 : PairBound 9 := { available := 143, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 70 168 159 175 207 143 399), lower := (rows 305 82 70 168 16 32 64 128 256), losses := [] }

theorem u8644 : Upper (D 1) (R 1) [304,80,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8644
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8645 : Route 9 := (fun mask => (mask,id))

def c8645 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8645 : Upper (D 1) (R 1) [304,80,72,129] 13 := by
  apply FastRouting.sound _ _ [304,80,72,129] 13 (by decide) (choices 1) [2,4,32,128] r8645 c8645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5639
  · exact u5640
  · exact u5641
  · exact u5642

def r8646 : Route 9 := (fun mask => (mask,id))

def c8646 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8646 : Upper (D 1) (R 1) [304,80,72,130] 13 := by
  apply FastRouting.sound _ _ [304,80,72,130] 13 (by decide) (choices 1) [1,2,4,32,128] r8646 c8646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5643
  · exact u5644
  · exact u5645
  · exact u5646
  · exact u5647

def b8647 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 76 140 179 163 227 163 419), lower := (rows 305 82 76 140 16 32 64 128 256), losses := [] }

theorem u8647 : Upper (D 1) (R 1) [304,80,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8647
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8648 : Route 9 := (fun mask => (mask,id))

def c8648 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8648 : Upper (D 1) (R 1) [304,80,72,160] 13 := by
  apply FastRouting.sound _ _ [304,80,72,160] 13 (by decide) (choices 1) [1,2,4,128] r8648 c8648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5648
  · exact u5649
  · exact u5650
  · exact u5651

def r8649 : Route 9 := (fun mask => (mask,id))

def c8649 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8649 : Upper (D 1) (R 1) [304,80,96,129] 13 := by
  apply FastRouting.sound _ _ [304,80,96,129] 13 (by decide) (choices 1) [2,4,8,128] r8649 c8649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5652
  · exact u5653
  · exact u5654
  · exact u5655

def r8650 : Route 9 := (fun mask => (mask,id))

def c8650 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8650 : Upper (D 1) (R 1) [304,80,96,130] 13 := by
  apply FastRouting.sound _ _ [304,80,96,130] 13 (by decide) (choices 1) [1,2,4,8,128] r8650 c8650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5656
  · exact u5657
  · exact u5658
  · exact u5659
  · exact u5660

def r8651 : Route 9 := (fun mask => (mask,id))

def c8651 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8651 : Upper (D 1) (R 1) [304,80,96,132] 13 := by
  apply FastRouting.sound _ _ [304,80,96,132] 13 (by decide) (choices 1) [1,2,8,128] r8651 c8651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5661
  · exact u5662
  · exact u5663
  · exact u5664

def r8652 : Route 9 := (fun mask => (mask,id))

def c8652 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u8652 : Upper (D 1) (R 1) [304,80,129,130] 13 := by
  apply FastRouting.sound _ _ [304,80,129,130] 13 (by decide) (choices 1) [2,4,8,32,64] r8652 c8652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5665
  · exact u5666
  · exact u5667
  · exact u5668
  · exact u5669

def b8653 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 82 133 140 122 106 106 234 362), lower := (rows 305 82 133 140 16 32 64 128 256), losses := [] }

theorem u8653 : Upper (D 1) (R 1) [304,80,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8653
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8654 : Route 9 := (fun mask => (mask,id))

def c8654 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8654 : Upper (D 1) (R 1) [304,80,129,160] 13 := by
  apply FastRouting.sound _ _ [304,80,129,160] 13 (by decide) (choices 1) [2,4,8,64] r8654 c8654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5670
  · exact u5671
  · exact u5672
  · exact u5673

def r8655 : Route 9 := (fun mask => (mask,id))

def c8655 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8655 : Upper (D 1) (R 1) [304,80,129,192] 13 := by
  apply FastRouting.sound _ _ [304,80,129,192] 13 (by decide) (choices 1) [2,4,8,32] r8655 c8655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5674
  · exact u5675
  · exact u5676
  · exact u5677

def b8656 : PairBound 9 := { available := 109, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 134 138 125 109 109 237 365), lower := (rows 305 82 134 138 16 32 64 128 256), losses := [] }

theorem u8656 : Upper (D 1) (R 1) [304,80,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8656
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8657 : PairBound 9 := { available := 107, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 82 134 140 123 107 107 235 363), lower := (rows 305 82 134 140 16 32 64 128 256), losses := [] }

theorem u8657 : Upper (D 1) (R 1) [304,80,130,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8657
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8658 : Route 9 := (fun mask => (mask,id))

def c8658 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8658 : Upper (D 1) (R 1) [304,80,130,160] 13 := by
  apply FastRouting.sound _ _ [304,80,130,160] 13 (by decide) (choices 1) [1,2,4,8,64] r8658 c8658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5678
  · exact u5679
  · exact u5680
  · exact u5681
  · exact u5682

def r8659 : Route 9 := (fun mask => (mask,id))

def c8659 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8659 : Upper (D 1) (R 1) [304,80,130,192] 13 := by
  apply FastRouting.sound _ _ [304,80,130,192] 13 (by decide) (choices 1) [1,2,4,8,32] r8659 c8659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5683
  · exact u5684
  · exact u5685
  · exact u5686
  · exact u5687

def b8660 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 305 82 140 140 115 99 99 227 355), lower := (rows 305 82 140 140 16 32 64 128 256), losses := [] }

theorem u8660 : Upper (D 1) (R 1) [304,80,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8660
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8661 : PairBound 9 := { available := 71, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 82 140 168 87 103 71 199 327), lower := (rows 305 82 140 168 16 32 64 128 256), losses := [] }

theorem u8661 : Upper (D 1) (R 1) [304,80,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8661
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8662 : PairBound 9 := { available := 39, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 82 140 200 55 39 103 167 295), lower := (rows 305 82 140 200 16 32 64 128 256), losses := [] }

theorem u8662 : Upper (D 1) (R 1) [304,80,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8662
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8663 : Route 9 := (fun mask => (mask,id))

def c8663 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8663 : Upper (D 1) (R 1) [304,80,160,192] 13 := by
  apply FastRouting.sound _ _ [304,80,160,192] 13 (by decide) (choices 1) [1,2,4,8] r8663 c8663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5688
  · exact u5689
  · exact u5690
  · exact u5691

def b8664 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 194 7 14 248 248 248 248 504), lower := (rows 305 194 7 14 16 32 64 128 256), losses := [] }

theorem u8664 : Upper (D 1) (R 1) [304,192,3,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8664
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8665 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 256 => 8 | _ => 0)

theorem u8665 : Upper (D 1) (R 1) [304,192,3,18] 13 := by
  apply FastRouting.sound _ _ [304,192,3,18] 13 (by decide) (choices 1) [4,8,32,64] r8665 c8665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5692
  · exact u5693
  · exact u5694
  · exact u5695

def b8666 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 305 194 7 28 250 234 234 234 490), lower := (rows 305 194 7 28 16 32 64 128 256), losses := [] }

theorem u8666 : Upper (D 1) (R 1) [304,192,3,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8666
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8667 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 194 7 56 222 238 206 206 462), lower := (rows 305 194 7 56 16 32 64 128 256), losses := [] }

theorem u8667 : Upper (D 1) (R 1) [304,192,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8667
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8668 : PairBound 9 := { available := 188, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 194 7 74 188 188 252 188 444), lower := (rows 305 194 7 74 16 32 64 128 256), losses := [] }

theorem u8668 : Upper (D 1) (R 1) [304,192,3,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8668
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8669 : Route 9 := (fun mask => (mask,id))

def c8669 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8669 : Upper (D 1) (R 1) [304,192,3,68] 13 := by
  apply FastRouting.sound _ _ [304,192,3,68] 13 (by decide) (choices 1) [2,8,32,128] r8669 c8669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5696
  · exact u5697
  · exact u5698
  · exact u5699

def r8670 : Route 9 := (fun mask => (mask,id))

def c8670 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u8670 : Upper (D 1) (R 1) [304,192,3,80] 13 := by
  apply FastRouting.sound _ _ [304,192,3,80] 13 (by decide) (choices 1) [2,4,8,32,128] r8670 c8670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5700
  · exact u5701
  · exact u5702
  · exact u5703
  · exact u5704

def b8671 : PairBound 9 := { available := 62, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 194 7 200 62 62 126 190 318), lower := (rows 305 194 7 200 16 32 64 128 256), losses := [] }

theorem u8671 : Upper (D 1) (R 1) [304,192,3,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8671
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8672 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8672 : Upper (D 1) (R 1) [304,192,9,6] 13 := by
  apply FastRouting.sound _ _ [304,192,9,6] 13 (by decide) (choices 1) [2,32,64] r8672 c8672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5705
  · exact u5706
  · exact u5707

def b8673 : PairBound 9 := { available := 230, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 305 194 13 26 246 230 230 230 486), lower := (rows 305 194 13 26 16 32 64 128 256), losses := [] }

theorem u8673 : Upper (D 1) (R 1) [304,192,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8673
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8674 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 13 28 242 226 226 226 482), lower := (rows 305 194 13 28 16 32 64 128 256), losses := [] }

theorem u8674 : Upper (D 1) (R 1) [304,192,9,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8674
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8675 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 13 56 214 230 198 198 454), lower := (rows 305 194 13 56 16 32 64 128 256), losses := [] }

theorem u8675 : Upper (D 1) (R 1) [304,192,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8675
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8676 : PairBound 9 := { available := 182, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 194 13 74 182 182 246 182 438), lower := (rows 305 194 13 74 16 32 64 128 256), losses := [] }

theorem u8676 : Upper (D 1) (R 1) [304,192,9,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8676
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8677 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 305 194 13 76 178 178 242 178 434), lower := (rows 305 194 13 76 16 32 64 128 256), losses := [] }

theorem u8677 : Upper (D 1) (R 1) [304,192,9,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8677
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8678 : PairBound 9 := { available := 166, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 305 194 13 88 182 166 230 166 422), lower := (rows 305 194 13 88 16 32 64 128 256), losses := [] }

theorem u8678 : Upper (D 1) (R 1) [304,192,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8678
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8679 : PairBound 9 := { available := 54, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 194 13 200 54 54 118 182 310), lower := (rows 305 194 13 200 16 32 64 128 256), losses := [] }

theorem u8679 : Upper (D 1) (R 1) [304,192,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8679
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8680 : PairBound 9 := { available := 241, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 305 194 14 14 241 241 241 241 497), lower := (rows 305 194 14 14 16 32 64 128 256), losses := [] }

theorem u8680 : Upper (D 1) (R 1) [304,192,10,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8680
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8681 : PairBound 9 := { available := 230, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 194 14 25 246 230 230 230 486), lower := (rows 305 194 14 25 16 32 64 128 256), losses := [] }

theorem u8681 : Upper (D 1) (R 1) [304,192,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8681
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8682 : PairBound 9 := { available := 229, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 194 14 26 245 229 229 229 485), lower := (rows 305 194 14 26 16 32 64 128 256), losses := [] }

theorem u8682 : Upper (D 1) (R 1) [304,192,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8682
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8683 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 305 194 14 28 243 227 227 227 483), lower := (rows 305 194 14 28 16 32 64 128 256), losses := [] }

theorem u8683 : Upper (D 1) (R 1) [304,192,10,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8683
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8684 : PairBound 9 := { available := 199, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 194 14 56 215 231 199 199 455), lower := (rows 305 194 14 56 16 32 64 128 256), losses := [] }

theorem u8684 : Upper (D 1) (R 1) [304,192,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8684
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8685 : PairBound 9 := { available := 182, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 194 14 73 182 182 246 182 438), lower := (rows 305 194 14 73 16 32 64 128 256), losses := [] }

theorem u8685 : Upper (D 1) (R 1) [304,192,10,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8685
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8686 : PairBound 9 := { available := 181, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 305 194 14 74 181 181 245 181 437), lower := (rows 305 194 14 74 16 32 64 128 256), losses := [] }

theorem u8686 : Upper (D 1) (R 1) [304,192,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8686
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8687 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 305 194 14 76 179 179 243 179 435), lower := (rows 305 194 14 76 16 32 64 128 256), losses := [] }

theorem u8687 : Upper (D 1) (R 1) [304,192,10,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8687
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8688 : PairBound 9 := { available := 167, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 194 14 88 183 167 231 167 423), lower := (rows 305 194 14 88 16 32 64 128 256), losses := [] }

theorem u8688 : Upper (D 1) (R 1) [304,192,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8688
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8689 : PairBound 9 := { available := 55, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 305 194 14 200 55 55 119 183 311), lower := (rows 305 194 14 200 16 32 64 128 256), losses := [] }

theorem u8689 : Upper (D 1) (R 1) [304,192,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8689
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8690 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 21 42 222 238 206 206 462), lower := (rows 305 194 21 42 16 32 64 128 256), losses := [] }

theorem u8690 : Upper (D 1) (R 1) [304,192,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8690
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8691 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 21 44 218 234 202 202 458), lower := (rows 305 194 21 44 16 32 64 128 256), losses := [] }

theorem u8691 : Upper (D 1) (R 1) [304,192,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8691
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8692 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 21 76 186 170 234 170 426), lower := (rows 305 194 21 76 16 32 64 128 256), losses := [] }

theorem u8692 : Upper (D 1) (R 1) [304,192,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8692
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8693 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 21 104 158 174 206 142 398), lower := (rows 305 194 21 104 16 32 64 128 256), losses := [] }

theorem u8693 : Upper (D 1) (R 1) [304,192,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8693
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8694 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8694 : Upper (D 1) (R 1) [304,192,18,34] 13 := by
  apply FastRouting.sound _ _ [304,192,18,34] 13 (by decide) (choices 1) [1,4,8,64] r8694 c8694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5708
  · exact u5709
  · exact u5710
  · exact u5711

def r8695 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8695 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8695 : Upper (D 1) (R 1) [304,192,18,36] 13 := by
  apply FastRouting.sound _ _ [304,192,18,36] 13 (by decide) (choices 1) [1,2,8,64] r8695 c8695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5712
  · exact u5713
  · exact u5714
  · exact u5715

def r8696 : Route 9 := (fun mask => (mask,id))

def c8696 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u8696 : Upper (D 1) (R 1) [304,192,18,65] 13 := by
  apply FastRouting.sound _ _ [304,192,18,65] 13 (by decide) (choices 1) [2,4,8,32,128] r8696 c8696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5716
  · exact u5717
  · exact u5718
  · exact u5719
  · exact u5720

def b8697 : PairBound 9 := { available := 173, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 194 22 74 189 173 237 173 429), lower := (rows 305 194 22 74 16 32 64 128 256), losses := [] }

theorem u8697 : Upper (D 1) (R 1) [304,192,18,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8697
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8698 : Route 9 := (fun mask => (mask,id))

def c8698 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8698 : Upper (D 1) (R 1) [304,192,18,68] 13 := by
  apply FastRouting.sound _ _ [304,192,18,68] 13 (by decide) (choices 1) [1,2,8,32,128] r8698 c8698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5721
  · exact u5722
  · exact u5723
  · exact u5724
  · exact u5725

def r8699 : Route 9 := (fun mask => (mask,id))

def c8699 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8699 : Upper (D 1) (R 1) [304,192,18,96] 13 := by
  apply FastRouting.sound _ _ [304,192,18,96] 13 (by decide) (choices 1) [1,2,4,8,128] r8699 c8699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5726
  · exact u5727
  · exact u5728
  · exact u5729
  · exact u5730

#print axioms u8699
end Delivery.IrregularNine14.P01
