import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0097
import IrregularNine14P01C0098
import IrregularNine14P01C0099
import IrregularNine14P01C0100

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8760 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 84 490 506 490 490 490 490), lower := (rows 23 35 84 8 16 32 64 128 256), losses := [] }

theorem u8760 : Upper (D 1) (R 1) [22,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8760
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8761 : PairBound 9 := { available := 474, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 100 474 474 506 474 474 474), lower := (rows 23 35 100 8 16 32 64 128 256), losses := [] }

theorem u8761 : Upper (D 1) (R 1) [22,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8761
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8762 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8762 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8762 : Upper (D 1) (R 1) [22,33,192] 13 := by
  apply FastRouting.sound _ _ [22,33,192] 13 (by decide) (choices 2) [18,34,48,66,80,96,192,258,272,288,320] r8762 c8762
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5854
  · exact u5855
  · exact u5856
  · exact u5857
  · exact u5858
  · exact u5859
  · exact u5860
  · exact u5861
  · exact u5862
  · exact u5863
  · exact u5864

def b8763 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 23 35 262 248 248 248 248 248 504), lower := (rows 23 35 262 8 16 32 64 128 256), losses := [] }

theorem u8763 : Upper (D 1) (R 1) [22,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8763
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8764 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8764 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8764 : Upper (D 1) (R 1) [22,33,264] 13 := by
  apply FastRouting.sound _ _ [22,33,264] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r8764 c8764
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5865
  · exact u5866
  · exact u5867
  · exact u5868
  · exact u5869
  · exact u5870
  · exact u5871

def b8765 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 276 234 250 234 234 234 490), lower := (rows 23 35 276 8 16 32 64 128 256), losses := [] }

theorem u8765 : Upper (D 1) (R 1) [22,33,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8765
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8766 : PairBound 9 := { available := 218, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 292 218 218 250 218 218 474), lower := (rows 23 35 292 8 16 32 64 128 256), losses := [] }

theorem u8766 : Upper (D 1) (R 1) [22,33,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8766
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8767 : Route 9 := (fun mask => (mask,id))

def c8767 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8767 : Upper (D 1) (R 1) [22,33,320] 13 := by
  apply FastRouting.sound _ _ [22,33,320] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192] r8767 c8767
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5872
  · exact u5873
  · exact u5874
  · exact u5875
  · exact u5876
  · exact u5877
  · exact u5878
  · exact u5879
  · exact u5880
  · exact u5881

def b8768 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 7 504 496 496 496 496 496), lower := (rows 23 42 7 8 16 32 64 128 256), losses := [] }

theorem u8768 : Upper (D 1) (R 1) [22,40,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8768
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8769 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 21 490 498 482 482 482 482), lower := (rows 23 42 21 8 16 32 64 128 256), losses := [] }

theorem u8769 : Upper (D 1) (R 1) [22,40,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8769
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8770 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 23 42 22 489 497 481 481 481 481), lower := (rows 23 42 22 8 16 32 64 128 256), losses := [] }

theorem u8770 : Upper (D 1) (R 1) [22,40,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8770
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8771 : PairBound 9 := { available := 466, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 37 474 466 498 466 466 466), lower := (rows 23 42 37 8 16 32 64 128 256), losses := [] }

theorem u8771 : Upper (D 1) (R 1) [22,40,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8771
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8772 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 38 473 465 497 465 465 465), lower := (rows 23 42 38 8 16 32 64 128 256), losses := [] }

theorem u8772 : Upper (D 1) (R 1) [22,40,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8772
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8773 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 52 459 467 483 451 451 451), lower := (rows 23 42 52 8 16 32 64 128 256), losses := [] }

theorem u8773 : Upper (D 1) (R 1) [22,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8773
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8774 : Route 9 := (fun mask => (mask,id))

def c8774 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8774 : Upper (D 1) (R 1) [22,40,65] 13 := by
  apply FastRouting.sound _ _ [22,40,65] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192,258,272,288,320,384] r8774 c8774
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5882
  · exact u5883
  · exact u5884
  · exact u5885
  · exact u5886
  · exact u5887
  · exact u5888
  · exact u5889
  · exact u5890
  · exact u5891
  · exact u5892
  · exact u5893
  · exact u5894
  · exact u5895
  · exact u5896

def b8775 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 23 42 70 505 497 497 497 497 497), lower := (rows 23 42 70 8 16 32 64 128 256), losses := [] }

theorem u8775 : Upper (D 1) (R 1) [22,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8775
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8776 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 84 491 499 483 483 483 483), lower := (rows 23 42 84 8 16 32 64 128 256), losses := [] }

theorem u8776 : Upper (D 1) (R 1) [22,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8776
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8777 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 100 475 467 499 467 467 467), lower := (rows 23 42 100 8 16 32 64 128 256), losses := [] }

theorem u8777 : Upper (D 1) (R 1) [22,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8777
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8778 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8778 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8778 : Upper (D 1) (R 1) [22,40,192] 13 := by
  apply FastRouting.sound _ _ [22,40,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192,257,258,272,288,320] r8778 c8778
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5897
  · exact u5898
  · exact u5899
  · exact u5900
  · exact u5901
  · exact u5902
  · exact u5903
  · exact u5904
  · exact u5905
  · exact u5906
  · exact u5907
  · exact u5908
  · exact u5909
  · exact u5910
  · exact u5911
  · exact u5912

def r8779 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8779 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8779 : Upper (D 1) (R 1) [22,40,257] 13 := by
  apply FastRouting.sound _ _ [22,40,257] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r8779 c8779
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5913
  · exact u5914
  · exact u5915
  · exact u5916
  · exact u5917
  · exact u5918
  · exact u5919

def b8780 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 23 42 262 249 241 241 241 241 497), lower := (rows 23 42 262 8 16 32 64 128 256), losses := [] }

theorem u8780 : Upper (D 1) (R 1) [22,40,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8780
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8781 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 276 235 243 227 227 227 483), lower := (rows 23 42 276 8 16 32 64 128 256), losses := [] }

theorem u8781 : Upper (D 1) (R 1) [22,40,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8781
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8782 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 292 219 211 243 211 211 467), lower := (rows 23 42 292 8 16 32 64 128 256), losses := [] }

theorem u8782 : Upper (D 1) (R 1) [22,40,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8782
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8783 : Route 9 := (fun mask => (mask,id))

def c8783 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8783 : Upper (D 1) (R 1) [22,40,320] 13 := by
  apply FastRouting.sound _ _ [22,40,320] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r8783 c8783
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5920
  · exact u5921
  · exact u5922
  · exact u5923
  · exact u5924
  · exact u5925
  · exact u5926
  · exact u5927
  · exact u5928
  · exact u5929
  · exact u5930
  · exact u5931
  · exact u5932
  · exact u5933
  · exact u5934

def b8784 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 98 7 504 504 504 504 504 504), lower := (rows 23 98 7 8 16 32 64 128 256), losses := [] }

theorem u8784 : Upper (D 1) (R 1) [22,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8784
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8785 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8785 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8785 : Upper (D 1) (R 1) [22,96,9] 13 := by
  apply FastRouting.sound _ _ [22,96,9] 13 (by decide) (choices 2) [18,34,48,96,130,144,160,258,272,288,384] r8785 c8785
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5935
  · exact u5936
  · exact u5937
  · exact u5938
  · exact u5939
  · exact u5940
  · exact u5941
  · exact u5942
  · exact u5943
  · exact u5944
  · exact u5945

def b8786 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 23 98 14 505 497 497 497 497 497), lower := (rows 23 98 14 8 16 32 64 128 256), losses := [] }

theorem u8786 : Upper (D 1) (R 1) [22,96,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8786
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8787 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 21 490 506 490 490 490 490), lower := (rows 23 98 21 8 16 32 64 128 256), losses := [] }

theorem u8787 : Upper (D 1) (R 1) [22,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8787
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8788 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 22 489 505 489 489 489 489), lower := (rows 23 98 22 8 16 32 64 128 256), losses := [] }

theorem u8788 : Upper (D 1) (R 1) [22,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8788
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8789 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 28 491 499 483 483 483 483), lower := (rows 23 98 28 8 16 32 64 128 256), losses := [] }

theorem u8789 : Upper (D 1) (R 1) [22,96,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8789
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8790 : PairBound 9 := { available := 474, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 37 474 474 506 474 474 474), lower := (rows 23 98 37 8 16 32 64 128 256), losses := [] }

theorem u8790 : Upper (D 1) (R 1) [22,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8790
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8791 : PairBound 9 := { available := 473, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 98 38 473 473 505 473 473 473), lower := (rows 23 98 38 8 16 32 64 128 256), losses := [] }

theorem u8791 : Upper (D 1) (R 1) [22,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8791
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8792 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 44 475 467 499 467 467 467), lower := (rows 23 98 44 8 16 32 64 128 256), losses := [] }

theorem u8792 : Upper (D 1) (R 1) [22,96,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8792
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8793 : PairBound 9 := { available := 459, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 52 459 475 491 459 459 459), lower := (rows 23 98 52 8 16 32 64 128 256), losses := [] }

theorem u8793 : Upper (D 1) (R 1) [22,96,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8793
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8794 : PairBound 9 := { available := 411, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 98 100 411 411 443 475 411 411), lower := (rows 23 98 100 8 16 32 64 128 256), losses := [] }

theorem u8794 : Upper (D 1) (R 1) [22,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8794
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8795 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8795 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8795 : Upper (D 1) (R 1) [22,96,129] 13 := by
  apply FastRouting.sound _ _ [22,96,129] 13 (by decide) (choices 2) [18,34,48,96,130,144,160,258,272,288,384] r8795 c8795
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5946
  · exact u5947
  · exact u5948
  · exact u5949
  · exact u5950
  · exact u5951
  · exact u5952
  · exact u5953
  · exact u5954
  · exact u5955
  · exact u5956

def b8796 : PairBound 9 := { available := 505, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 23 98 134 505 505 505 505 505 505), lower := (rows 23 98 134 8 16 32 64 128 256), losses := [] }

theorem u8796 : Upper (D 1) (R 1) [22,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8796
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8797 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8797 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8797 : Upper (D 1) (R 1) [22,96,136] 13 := by
  apply FastRouting.sound _ _ [22,96,136] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160,257,258,272,288,384] r8797 c8797
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5957
  · exact u5958
  · exact u5959
  · exact u5960
  · exact u5961
  · exact u5962
  · exact u5963
  · exact u5964
  · exact u5965
  · exact u5966
  · exact u5967
  · exact u5968
  · exact u5969
  · exact u5970
  · exact u5971
  · exact u5972

def b8798 : PairBound 9 := { available := 491, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 148 491 507 491 491 491 491), lower := (rows 23 98 148 8 16 32 64 128 256), losses := [] }

theorem u8798 : Upper (D 1) (R 1) [22,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8798
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8799 : PairBound 9 := { available := 475, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 475 475 507 475 475 475), lower := (rows 23 98 164 8 16 32 64 128 256), losses := [] }

theorem u8799 : Upper (D 1) (R 1) [22,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8799
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8800 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8800 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8800 : Upper (D 1) (R 1) [22,96,257] 13 := by
  apply FastRouting.sound _ _ [22,96,257] 13 (by decide) (choices 2) [18,34,48,96,130,144,160] r8800 c8800
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5973
  · exact u5974
  · exact u5975
  · exact u5976
  · exact u5977
  · exact u5978
  · exact u5979

def b8801 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 23 98 262 249 249 249 249 249 505), lower := (rows 23 98 262 8 16 32 64 128 256), losses := [] }

theorem u8801 : Upper (D 1) (R 1) [22,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8801
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8802 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8802 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8802 : Upper (D 1) (R 1) [22,96,264] 13 := by
  apply FastRouting.sound _ _ [22,96,264] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r8802 c8802
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5980
  · exact u5981
  · exact u5982
  · exact u5983
  · exact u5984
  · exact u5985
  · exact u5986
  · exact u5987
  · exact u5988
  · exact u5989
  · exact u5990

def b8803 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 276 235 251 235 235 235 491), lower := (rows 23 98 276 8 16 32 64 128 256), losses := [] }

theorem u8803 : Upper (D 1) (R 1) [22,96,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8803
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8804 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 292 219 219 251 219 219 475), lower := (rows 23 98 292 8 16 32 64 128 256), losses := [] }

theorem u8804 : Upper (D 1) (R 1) [22,96,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8804
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8805 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8805 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8805 : Upper (D 1) (R 1) [22,96,384] 13 := by
  apply FastRouting.sound _ _ [22,96,384] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r8805 c8805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5991
  · exact u5992
  · exact u5993
  · exact u5994
  · exact u5995
  · exact u5996
  · exact u5997
  · exact u5998
  · exact u5999
  · exact u6000
  · exact u6001

def b8806 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 23 259 14 248 240 240 240 240 496), lower := (rows 23 259 14 8 16 32 64 128 256), losses := [] }

theorem u8806 : Upper (D 1) (R 1) [22,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8806
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8807 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 23 259 22 232 248 232 232 232 488), lower := (rows 23 259 22 8 16 32 64 128 256), losses := [] }

theorem u8807 : Upper (D 1) (R 1) [22,257,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8807
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8808 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 259 28 234 242 226 226 226 482), lower := (rows 23 259 28 8 16 32 64 128 256), losses := [] }

theorem u8808 : Upper (D 1) (R 1) [22,257,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8808
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8809 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 23 259 38 248 248 248 248 248 504), lower := (rows 23 259 38 8 16 32 64 128 256), losses := [] }

theorem u8809 : Upper (D 1) (R 1) [22,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8809
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8810 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8810 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8810 : Upper (D 1) (R 1) [22,257,40] 13 := by
  apply FastRouting.sound _ _ [22,257,40] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r8810 c8810
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6002
  · exact u6003
  · exact u6004
  · exact u6005
  · exact u6006
  · exact u6007
  · exact u6008

def b8811 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 259 52 234 250 234 234 234 490), lower := (rows 23 259 52 8 16 32 64 128 256), losses := [] }

theorem u8811 : Upper (D 1) (R 1) [22,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8811
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8812 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8812 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8812 : Upper (D 1) (R 1) [22,257,96] 13 := by
  apply FastRouting.sound _ _ [22,257,96] 13 (by decide) (choices 2) [18,34,48,96,130,144,160] r8812 c8812
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6009
  · exact u6010
  · exact u6011
  · exact u6012
  · exact u6013
  · exact u6014
  · exact u6015

def b8813 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 266 7 248 240 240 240 240 496), lower := (rows 23 266 7 8 16 32 64 128 256), losses := [] }

theorem u8813 : Upper (D 1) (R 1) [22,264,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8813
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8814 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 266 21 234 242 226 226 226 482), lower := (rows 23 266 21 8 16 32 64 128 256), losses := [] }

theorem u8814 : Upper (D 1) (R 1) [22,264,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8814
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8815 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 23 266 22 233 241 225 225 225 481), lower := (rows 23 266 22 8 16 32 64 128 256), losses := [] }

theorem u8815 : Upper (D 1) (R 1) [22,264,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8815
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8816 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8816 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8816 : Upper (D 1) (R 1) [22,264,33] 13 := by
  apply FastRouting.sound _ _ [22,264,33] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r8816 c8816
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6016
  · exact u6017
  · exact u6018
  · exact u6019
  · exact u6020
  · exact u6021
  · exact u6022

def b8817 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 23 266 38 249 241 241 241 241 497), lower := (rows 23 266 38 8 16 32 64 128 256), losses := [] }

theorem u8817 : Upper (D 1) (R 1) [22,264,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8817
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8818 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 266 52 235 243 227 227 227 483), lower := (rows 23 266 52 8 16 32 64 128 256), losses := [] }

theorem u8818 : Upper (D 1) (R 1) [22,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8818
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8819 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8819 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8819 : Upper (D 1) (R 1) [22,264,96] 13 := by
  apply FastRouting.sound _ _ [22,264,96] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r8819 c8819
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6023
  · exact u6024
  · exact u6025
  · exact u6026
  · exact u6027
  · exact u6028
  · exact u6029
  · exact u6030
  · exact u6031
  · exact u6032
  · exact u6033

#print axioms u8819
end Delivery.IrregularNine14.P01
