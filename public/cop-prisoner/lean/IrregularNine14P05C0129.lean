import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0068
import IrregularNine14P05C0069

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7740 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 164 41 273 46 78 142 270), lower := (rows 19 70 164 41 273 32 64 128 256), losses := [] }

theorem u7740 : Upper (D 5) (R 5) [18,68,160,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7740
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7741 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 41 274 45 77 141 269), lower := (rows 19 70 164 41 274 32 64 128 256), losses := [] }

theorem u7741 : Upper (D 5) (R 5) [18,68,160,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7741
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7742 : Route 9 := (fun mask => (mask,id))

def c7742 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7742 : Upper (D 5) (R 5) [18,68,160,33,260] 13 := by
  apply FastRouting.sound _ _ [18,68,160,33,260] 13 (by decide) (choices 1) [1,2,8] r7742 c7742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4108
  · exact u4109
  · exact u4110

def r7743 : Route 9 := (fun mask => (mask,id))

def c7743 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7743 : Upper (D 5) (R 5) [18,68,160,33,264] 13 := by
  apply FastRouting.sound _ _ [18,68,160,33,264] 13 (by decide) (choices 1) [1,2,4,8] r7743 c7743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4111
  · exact u4112
  · exact u4113
  · exact u4114

def b7744 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 164 42 21 297 329 393 265), lower := (rows 19 70 164 42 21 32 64 128 256), losses := [] }

theorem u7744 : Upper (D 5) (R 5) [18,68,160,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7744
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7745 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 164 42 25 301 333 397 269), lower := (rows 19 70 164 42 25 32 64 128 256), losses := [] }

theorem u7745 : Upper (D 5) (R 5) [18,68,160,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7745
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7746 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 164 42 28 297 329 393 265), lower := (rows 19 70 164 42 28 32 64 128 256), losses := [] }

theorem u7746 : Upper (D 5) (R 5) [18,68,160,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7746
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7747 : Route 9 := (fun mask => (mask,id))

def c7747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7747 : Upper (D 5) (R 5) [18,68,160,34,257] 13 := by
  apply FastRouting.sound _ _ [18,68,160,34,257] 13 (by decide) (choices 1) [1,4,8] r7747 c7747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4115
  · exact u4116
  · exact u4117

def r7748 : Route 9 := (fun mask => (mask,id))

def c7748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7748 : Upper (D 5) (R 5) [18,68,160,34,260] 13 := by
  apply FastRouting.sound _ _ [18,68,160,34,260] 13 (by decide) (choices 1) [1,8] r7748 c7748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4118
  · exact u4119

def r7749 : Route 9 := (fun mask => (mask,id))

def c7749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7749 : Upper (D 5) (R 5) [18,68,160,34,264] 13 := by
  apply FastRouting.sound _ _ [18,68,160,34,264] 13 (by decide) (choices 1) [1,4,8] r7749 c7749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4120
  · exact u4121
  · exact u4122

def b7750 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 265 19 44 108 172 300), lower := (rows 19 70 164 265 19 32 64 128 256), losses := [] }

theorem u7750 : Upper (D 5) (R 5) [18,68,160,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7750
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7751 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 164 265 21 42 106 170 298), lower := (rows 19 70 164 265 21 32 64 128 256), losses := [] }

theorem u7751 : Upper (D 5) (R 5) [18,68,160,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7751
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7752 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 164 265 22 41 105 169 297), lower := (rows 19 70 164 265 22 32 64 128 256), losses := [] }

theorem u7752 : Upper (D 5) (R 5) [18,68,160,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7752
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7753 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 164 265 25 46 110 174 302), lower := (rows 19 70 164 265 25 32 64 128 256), losses := [] }

theorem u7753 : Upper (D 5) (R 5) [18,68,160,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7753
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7754 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 265 26 45 109 173 301), lower := (rows 19 70 164 265 26 32 64 128 256), losses := [] }

theorem u7754 : Upper (D 5) (R 5) [18,68,160,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7754
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7755 : Route 9 := (fun mask => (mask,id))

def c7755 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7755 : Upper (D 5) (R 5) [18,68,160,257,12] 13 := by
  apply FastRouting.sound _ _ [18,68,160,257,12] 13 (by decide) (choices 1) [1,2,8] r7755 c7755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4123
  · exact u4124
  · exact u4125

def b7756 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 164 265 49 46 78 142 270), lower := (rows 19 70 164 265 49 32 64 128 256), losses := [] }

theorem u7756 : Upper (D 5) (R 5) [18,68,160,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7756
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7757 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 265 50 45 77 141 269), lower := (rows 19 70 164 265 50 32 64 128 256), losses := [] }

theorem u7757 : Upper (D 5) (R 5) [18,68,160,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7757
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7758 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 164 265 52 43 75 139 267), lower := (rows 19 70 164 265 52 32 64 128 256), losses := [] }

theorem u7758 : Upper (D 5) (R 5) [18,68,160,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7758
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7759 : Route 9 := (fun mask => (mask,id))

def c7759 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7759 : Upper (D 5) (R 5) [18,68,160,257,40] 13 := by
  apply FastRouting.sound _ _ [18,68,160,257,40] 13 (by decide) (choices 1) [1,2,4,8] r7759 c7759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4126
  · exact u4127
  · exact u4128
  · exact u4129

def b7760 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 164 266 21 41 105 169 297), lower := (rows 19 70 164 266 21 32 64 128 256), losses := [] }

theorem u7760 : Upper (D 5) (R 5) [18,68,160,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7760
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7761 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 164 266 25 45 109 173 301), lower := (rows 19 70 164 266 25 32 64 128 256), losses := [] }

theorem u7761 : Upper (D 5) (R 5) [18,68,160,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7761
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7762 : Route 9 := (fun mask => (mask,id))

def c7762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7762 : Upper (D 5) (R 5) [18,68,160,258,12] 13 := by
  apply FastRouting.sound _ _ [18,68,160,258,12] 13 (by decide) (choices 1) [1,8] r7762 c7762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4130
  · exact u4131

def r7763 : Route 9 := (fun mask => (mask,id))

def c7763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7763 : Upper (D 5) (R 5) [18,68,160,258,33] 13 := by
  apply FastRouting.sound _ _ [18,68,160,258,33] 13 (by decide) (choices 1) [1,4,8] r7763 c7763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4132
  · exact u4133
  · exact u4134

def b7764 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 164 266 52 41 73 137 265), lower := (rows 19 70 164 266 52 32 64 128 256), losses := [] }

theorem u7764 : Upper (D 5) (R 5) [18,68,160,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7764
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7765 : Route 9 := (fun mask => (mask,id))

def c7765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7765 : Upper (D 5) (R 5) [18,68,160,258,40] 13 := by
  apply FastRouting.sound _ _ [18,68,160,258,40] 13 (by decide) (choices 1) [1,4,8] r7765 c7765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4135
  · exact u4136
  · exact u4137

def b7766 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 268 19 41 105 169 297), lower := (rows 19 70 164 268 19 32 64 128 256), losses := [] }

theorem u7766 : Upper (D 5) (R 5) [18,68,160,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7766
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7767 : Route 9 := (fun mask => (mask,id))

def c7767 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7767 : Upper (D 5) (R 5) [18,68,160,260,9] 13 := by
  apply FastRouting.sound _ _ [18,68,160,260,9] 13 (by decide) (choices 1) [1,2,8] r7767 c7767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4138
  · exact u4139
  · exact u4140

def b7768 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 164 268 26 41 105 169 297), lower := (rows 19 70 164 268 26 32 64 128 256), losses := [] }

theorem u7768 : Upper (D 5) (R 5) [18,68,160,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7768
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7769 : Route 9 := (fun mask => (mask,id))

def c7769 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7769 : Upper (D 5) (R 5) [18,68,160,260,33] 13 := by
  apply FastRouting.sound _ _ [18,68,160,260,33] 13 (by decide) (choices 1) [1,2,8] r7769 c7769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4141
  · exact u4142
  · exact u4143

def b7770 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 268 50 41 73 137 265), lower := (rows 19 70 164 268 50 32 64 128 256), losses := [] }

theorem u7770 : Upper (D 5) (R 5) [18,68,160,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7770
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7771 : Route 9 := (fun mask => (mask,id))

def c7771 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7771 : Upper (D 5) (R 5) [18,68,160,260,40] 13 := by
  apply FastRouting.sound _ _ [18,68,160,260,40] 13 (by decide) (choices 1) [1,2,8] r7771 c7771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4144
  · exact u4145
  · exact u4146

def b7772 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 296 19 45 77 141 269), lower := (rows 19 70 164 296 19 32 64 128 256), losses := [] }

theorem u7772 : Upper (D 5) (R 5) [18,68,160,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7772
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7773 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 164 296 21 43 75 139 267), lower := (rows 19 70 164 296 21 32 64 128 256), losses := [] }

theorem u7773 : Upper (D 5) (R 5) [18,68,160,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7773
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7774 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 164 296 22 41 73 137 265), lower := (rows 19 70 164 296 22 32 64 128 256), losses := [] }

theorem u7774 : Upper (D 5) (R 5) [18,68,160,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7774
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7775 : Route 9 := (fun mask => (mask,id))

def c7775 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7775 : Upper (D 5) (R 5) [18,68,160,288,9] 13 := by
  apply FastRouting.sound _ _ [18,68,160,288,9] 13 (by decide) (choices 1) [1,2,4,8] r7775 c7775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4147
  · exact u4148
  · exact u4149
  · exact u4150

def b7776 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 296 26 45 77 141 269), lower := (rows 19 70 164 296 26 32 64 128 256), losses := [] }

theorem u7776 : Upper (D 5) (R 5) [18,68,160,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7776
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7777 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 164 296 28 43 75 139 267), lower := (rows 19 70 164 296 28 32 64 128 256), losses := [] }

theorem u7777 : Upper (D 5) (R 5) [18,68,160,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7777
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7778 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 388 41 19 44 108 172 300), lower := (rows 19 70 388 41 19 32 64 128 256), losses := [] }

theorem u7778 : Upper (D 5) (R 5) [18,68,384,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7778
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7779 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 388 41 21 42 106 170 298), lower := (rows 19 70 388 41 21 32 64 128 256), losses := [] }

theorem u7779 : Upper (D 5) (R 5) [18,68,384,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7779
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7780 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 388 41 22 41 105 169 297), lower := (rows 19 70 388 41 22 32 64 128 256), losses := [] }

theorem u7780 : Upper (D 5) (R 5) [18,68,384,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7780
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7781 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 388 41 25 46 110 174 302), lower := (rows 19 70 388 41 25 32 64 128 256), losses := [] }

theorem u7781 : Upper (D 5) (R 5) [18,68,384,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7781
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7782 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 388 41 26 45 109 173 301), lower := (rows 19 70 388 41 26 32 64 128 256), losses := [] }

theorem u7782 : Upper (D 5) (R 5) [18,68,384,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7782
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7783 : Route 9 := (fun mask => (mask,id))

def c7783 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7783 : Upper (D 5) (R 5) [18,68,384,33,12] 13 := by
  apply FastRouting.sound _ _ [18,68,384,33,12] 13 (by decide) (choices 1) [1,2,8] r7783 c7783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4151
  · exact u4152
  · exact u4153

def b7784 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 454, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 388 41 49 46 78 142 270), lower := (rows 19 70 388 41 49 32 64 128 256), losses := [] }

theorem u7784 : Upper (D 5) (R 5) [18,68,384,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7784
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7785 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 388 41 50 45 77 141 269), lower := (rows 19 70 388 41 50 32 64 128 256), losses := [] }

theorem u7785 : Upper (D 5) (R 5) [18,68,384,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7785
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7786 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 19 70 388 41 52 43 75 139 267), lower := (rows 19 70 388 41 52 32 64 128 256), losses := [] }

theorem u7786 : Upper (D 5) (R 5) [18,68,384,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7786
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7787 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 388 41 56 47 79 143 271), lower := (rows 19 70 388 41 56 32 64 128 256), losses := [] }

theorem u7787 : Upper (D 5) (R 5) [18,68,384,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7787
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7788 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 388 42 21 41 105 169 297), lower := (rows 19 70 388 42 21 32 64 128 256), losses := [] }

theorem u7788 : Upper (D 5) (R 5) [18,68,384,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7788
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7789 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 388 42 25 45 109 173 301), lower := (rows 19 70 388 42 25 32 64 128 256), losses := [] }

theorem u7789 : Upper (D 5) (R 5) [18,68,384,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7789
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7790 : Route 9 := (fun mask => (mask,id))

def c7790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7790 : Upper (D 5) (R 5) [18,68,384,34,12] 13 := by
  apply FastRouting.sound _ _ [18,68,384,34,12] 13 (by decide) (choices 1) [1,8] r7790 c7790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4154
  · exact u4155

def b7791 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 17, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 388 42 49 45 77 141 269), lower := (rows 19 70 388 42 49 32 64 128 256), losses := [] }

theorem u7791 : Upper (D 5) (R 5) [18,68,384,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7791
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7792 : Route 9 := (fun mask => (mask,id))

def c7792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7792 : Upper (D 5) (R 5) [18,68,384,34,36] 13 := by
  apply FastRouting.sound _ _ [18,68,384,34,36] 13 (by decide) (choices 1) [1,8] r7792 c7792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4156
  · exact u4157

def b7793 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 388 42 56 45 77 141 269), lower := (rows 19 70 388 42 56 32 64 128 256), losses := [] }

theorem u7793 : Upper (D 5) (R 5) [18,68,384,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7793
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7794 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 388 44 19 41 105 169 297), lower := (rows 19 70 388 44 19 32 64 128 256), losses := [] }

theorem u7794 : Upper (D 5) (R 5) [18,68,384,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7794
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7795 : Route 9 := (fun mask => (mask,id))

def c7795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7795 : Upper (D 5) (R 5) [18,68,384,36,9] 13 := by
  apply FastRouting.sound _ _ [18,68,384,36,9] 13 (by decide) (choices 1) [1,2,8] r7795 c7795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4158
  · exact u4159
  · exact u4160

def b7796 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 388 44 26 41 105 169 297), lower := (rows 19 70 388 44 26 32 64 128 256), losses := [] }

theorem u7796 : Upper (D 5) (R 5) [18,68,384,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7796
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7797 : Route 9 := (fun mask => (mask,id))

def c7797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7797 : Upper (D 5) (R 5) [18,68,384,36,33] 13 := by
  apply FastRouting.sound _ _ [18,68,384,36,33] 13 (by decide) (choices 1) [1,2,8] r7797 c7797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4161
  · exact u4162
  · exact u4163

def b7798 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 388 44 50 41 73 137 265), lower := (rows 19 70 388 44 50 32 64 128 256), losses := [] }

theorem u7798 : Upper (D 5) (R 5) [18,68,384,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7798
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7799 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 388 44 56 43 75 139 267), lower := (rows 19 70 388 44 56 32 64 128 256), losses := [] }

theorem u7799 : Upper (D 5) (R 5) [18,68,384,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7799
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u7799
end Delivery.IrregularNine14.P05
