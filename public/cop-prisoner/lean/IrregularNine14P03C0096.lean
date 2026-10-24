import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0036
import IrregularNine14P03C0037
import IrregularNine14P03C0038

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5760 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 138 148 49 113 177 305), lower := (rows 289 67 76 138 148 32 64 128 256), losses := [] }

theorem u5760 : Upper (D 3) (R 3) [288,65,72,130,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5760
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5761 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 138 176 53 85 149 277), lower := (rows 289 67 76 138 176 32 64 128 256), losses := [] }

theorem u5761 : Upper (D 3) (R 3) [288,65,72,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5761
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5762 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 140 145 51 115 179 307), lower := (rows 289 67 76 140 145 32 64 128 256), losses := [] }

theorem u5762 : Upper (D 3) (R 3) [288,65,72,132,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5762
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5763 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 140 146 49 113 177 305), lower := (rows 289 67 76 140 146 32 64 128 256), losses := [] }

theorem u5763 : Upper (D 3) (R 3) [288,65,72,132,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5763
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5764 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 140 176 51 83 147 275), lower := (rows 289 67 76 140 176 32 64 128 256), losses := [] }

theorem u5764 : Upper (D 3) (R 3) [288,65,72,132,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5764
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5765 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 76 152 146 37 101 165 293), lower := (rows 289 67 76 152 146 32 64 128 256), losses := [] }

theorem u5765 : Upper (D 3) (R 3) [288,65,72,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5765
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5766 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 76 152 148 35 99 163 291), lower := (rows 289 67 76 152 148 32 64 128 256), losses := [] }

theorem u5766 : Upper (D 3) (R 3) [288,65,72,144,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5766
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5767 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 76 152 176 39 71 135 263), lower := (rows 289 67 76 152 176 32 64 128 256), losses := [] }

theorem u5767 : Upper (D 3) (R 3) [288,65,72,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5767
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5768 : Route 9 := (fun mask => (mask,id))

def c5768 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5768 : Upper (D 3) (R 3) [288,65,72,160,129] 13 := by
  apply FastRouting.sound _ _ [288,65,72,160,129] 13 (by decide) (choices 1) [1,2,4,16] r5768 c5768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2198
  · exact u2199
  · exact u2200
  · exact u2201

def r5769 : Route 9 := (fun mask => (mask,id))

def c5769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5769 : Upper (D 3) (R 3) [288,65,72,160,130] 13 := by
  apply FastRouting.sound _ _ [288,65,72,160,130] 13 (by decide) (choices 1) [1,4,16] r5769 c5769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2202
  · exact u2203
  · exact u2204

def b5770 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 76 168 148 51 83 147 275), lower := (rows 289 67 76 168 148 32 64 128 256), losses := [] }

theorem u5770 : Upper (D 3) (R 3) [288,65,72,160,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5770
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5771 : Route 9 := (fun mask => (mask,id))

def c5771 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5771 : Upper (D 3) (R 3) [288,65,96,130,132] 13 := by
  apply FastRouting.sound _ _ [288,65,96,130,132] 13 (by decide) (choices 1) [1,8,16] r5771 c5771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2205
  · exact u2206
  · exact u2207

def b5772 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 67 100 138 152 53 85 149 277), lower := (rows 289 67 100 138 152 32 64 128 256), losses := [] }

theorem u5772 : Upper (D 3) (R 3) [288,65,96,130,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5772
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5773 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 67 100 140 152 51 83 147 275), lower := (rows 289 67 100 140 152 32 64 128 256), losses := [] }

theorem u5773 : Upper (D 3) (R 3) [288,65,96,132,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5773
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5774 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 67 100 152 152 39 71 135 263), lower := (rows 289 67 100 152 152 32 64 128 256), losses := [] }

theorem u5774 : Upper (D 3) (R 3) [288,65,96,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5774
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5775 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 76 138 176 49 81 145 273), lower := (rows 289 70 76 138 176 32 64 128 256), losses := [] }

theorem u5775 : Upper (D 3) (R 3) [288,68,72,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5775
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5776 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 76 168 146 49 81 145 273), lower := (rows 289 70 76 168 146 32 64 128 256), losses := [] }

theorem u5776 : Upper (D 3) (R 3) [288,68,72,160,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5776
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5777 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 134 88 176 41 73 137 265), lower := (rows 289 70 134 88 176 32 64 128 256), losses := [] }

theorem u5777 : Upper (D 3) (R 3) [288,68,130,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5777
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5778 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 140 88 176 35 67 131 259), lower := (rows 289 70 140 88 176 32 64 128 256), losses := [] }

theorem u5778 : Upper (D 3) (R 3) [288,68,136,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5778
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5779 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 21 41 496 480 480 480 480), lower := (rows 7 11 21 41 16 32 64 128 256), losses := [] }

theorem u5779 : Upper (D 3) (R 3) [6,9,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5779
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5780_33 : Upper (D 3) (R 3) [6,9,17,96,33] 13 :=
  permutation_upper _ _ _ [6,9,17,33,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2208

theorem m5780_129 : Upper (D 3) (R 3) [6,9,17,96,129] 13 :=
  permutation_upper _ _ _ [6,9,17,33,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2209

def r5780 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5780 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5780 : Upper (D 3) (R 3) [6,9,17,96] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r5780 c5780
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5780_33
  · exact u2212
  · exact m5780_129
  · exact u2213
  · exact u2214
  · exact u2215
  · exact u2216

def b5781 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 21 265 240 224 224 224 480), lower := (rows 7 11 21 265 16 32 64 128 256), losses := [] }

theorem u5781 : Upper (D 3) (R 3) [6,9,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5781
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5782_33 : Upper (D 3) (R 3) [6,9,17,288,33] 13 :=
  permutation_upper _ _ _ [6,9,17,33,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2210

theorem m5782_65 : Upper (D 3) (R 3) [6,9,17,288,65] 13 :=
  permutation_upper _ _ _ [6,9,17,33,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2211

theorem m5782_96 : Upper (D 3) (R 3) [6,9,17,288,96] 13 :=
  permutation_upper _ _ _ [6,9,17,96,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2215

theorem m5782_192 : Upper (D 3) (R 3) [6,9,17,288,192] 13 :=
  permutation_upper _ _ _ [6,9,17,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2216

def r5782 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5782 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5782 : Upper (D 3) (R 3) [6,9,17,288] 13 := by
  apply FastRouting.sound _ _ [6,9,17,288] 13 (by decide) (choices 2) [33,65,96,192] r5782 c5782
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m5782_33
  · exact m5782_65
  · exact m5782_96
  · exact m5782_192

def b5783 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 37 25 496 480 480 480 480), lower := (rows 7 11 37 25 16 32 64 128 256), losses := [] }

theorem u5783 : Upper (D 3) (R 3) [6,9,33,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5783
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5784 : PairBound 9 := { available := 464, camps := [{ cop := 5, region := 15, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 41 464 496 464 464 464), lower := (rows 7 11 37 41 16 32 64 128 256), losses := [] }

theorem u5784 : Upper (D 3) (R 3) [6,9,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5784
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5785 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 7, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 56 465 481 449 449 449), lower := (rows 7 11 37 56 16 32 64 128 256), losses := [] }

theorem u5785 : Upper (D 3) (R 3) [6,9,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5785
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5786 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 37 73 496 496 496 496 496), lower := (rows 7 11 37 73 16 32 64 128 256), losses := [] }

theorem u5786 : Upper (D 3) (R 3) [6,9,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5786
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5787 : Route 9 := (fun mask => (mask,id))

def c5787 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5787 : Upper (D 3) (R 3) [6,9,33,80] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r5787 c5787
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2217
  · exact u2218
  · exact u2219
  · exact u2220
  · exact u2221
  · exact u2222
  · exact u2223
  · exact u2224
  · exact u2225
  · exact u2226

def b5788 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 7, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 104 465 497 465 465 465), lower := (rows 7 11 37 104 16 32 64 128 256), losses := [] }

theorem u5788 : Upper (D 3) (R 3) [6,9,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5788
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5789 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5789 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5789 : Upper (D 3) (R 3) [6,9,33,192] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r5789 c5789
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2227
  · exact u2228
  · exact u2229
  · exact u2230
  · exact u2231
  · exact u2232
  · exact u2233

def b5790 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 37 265 240 240 240 240 496), lower := (rows 7 11 37 265 16 32 64 128 256), losses := [] }

theorem u5790 : Upper (D 3) (R 3) [6,9,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5790
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5791 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5791 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5791 : Upper (D 3) (R 3) [6,9,33,272] 13 := by
  apply FastRouting.sound _ _ [6,9,33,272] 13 (by decide) (choices 2) [33,65,96,192] r5791 c5791
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2234
  · exact u2235
  · exact u2236
  · exact u2237

def b5792 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 7, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 296 209 241 209 209 465), lower := (rows 7 11 37 296 16 32 64 128 256), losses := [] }

theorem u5792 : Upper (D 3) (R 3) [6,9,33,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5792
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5793 : Route 9 := (fun mask => (mask,id))

def c5793 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5793 : Upper (D 3) (R 3) [6,9,33,320] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5793 c5793
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2238
  · exact u2239
  · exact u2240
  · exact u2241
  · exact u2242
  · exact u2243

def b5794 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 52 41 465 481 449 449 449), lower := (rows 7 11 52 41 16 32 64 128 256), losses := [] }

theorem u5794 : Upper (D 3) (R 3) [6,9,48,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5794
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5795 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 52 73 497 481 481 481 481), lower := (rows 7 11 52 73 16 32 64 128 256), losses := [] }

theorem u5795 : Upper (D 3) (R 3) [6,9,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5795
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5796 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 11 52 104 465 481 449 449 449), lower := (rows 7 11 52 104 16 32 64 128 256), losses := [] }

theorem u5796 : Upper (D 3) (R 3) [6,9,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5796
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5797 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5797 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5797 : Upper (D 3) (R 3) [6,9,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r5797 c5797
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2244
  · exact u2245
  · exact u2246
  · exact u2247
  · exact u2248
  · exact u2249
  · exact u2250

def b5798 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 52 265 241 225 225 225 481), lower := (rows 7 11 52 265 16 32 64 128 256), losses := [] }

theorem u5798 : Upper (D 3) (R 3) [6,9,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5798
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5799 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 11 52 296 209 225 193 193 449), lower := (rows 7 11 52 296 16 32 64 128 256), losses := [] }

theorem u5799 : Upper (D 3) (R 3) [6,9,48,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5799
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5800 : Route 9 := (fun mask => (mask,id))

def c5800 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5800 : Upper (D 3) (R 3) [6,9,48,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5800 c5800
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2251
  · exact u2252
  · exact u2253
  · exact u2254
  · exact u2255
  · exact u2256

def b5801 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 100 25 497 481 481 481 481), lower := (rows 7 11 100 25 16 32 64 128 256), losses := [] }

theorem u5801 : Upper (D 3) (R 3) [6,9,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5801
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5802 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 41 465 497 465 465 465), lower := (rows 7 11 100 41 16 32 64 128 256), losses := [] }

theorem u5802 : Upper (D 3) (R 3) [6,9,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5802
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5803 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 11 100 56 465 481 449 449 449), lower := (rows 7 11 100 56 16 32 64 128 256), losses := [] }

theorem u5803 : Upper (D 3) (R 3) [6,9,96,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5803
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5804 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 11, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 104 401 433 465 401 401), lower := (rows 7 11 100 104 16 32 64 128 256), losses := [] }

theorem u5804 : Upper (D 3) (R 3) [6,9,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5804
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5805 : PairBound 9 := { available := 497, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 100 137 497 497 497 497 497), lower := (rows 7 11 100 137 16 32 64 128 256), losses := [] }

theorem u5805 : Upper (D 3) (R 3) [6,9,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5805
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5806 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5806 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5806 : Upper (D 3) (R 3) [6,9,96,144] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r5806 c5806
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2257
  · exact u2258
  · exact u2259
  · exact u2260
  · exact u2261
  · exact u2262
  · exact u2263

def b5807 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 11 100 168 465 497 465 465 465), lower := (rows 7 11 100 168 16 32 64 128 256), losses := [] }

theorem u5807 : Upper (D 3) (R 3) [6,9,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5807
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5808 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 100 265 241 241 241 241 497), lower := (rows 7 11 100 265 16 32 64 128 256), losses := [] }

theorem u5808 : Upper (D 3) (R 3) [6,9,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5808
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5809 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5809 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5809 : Upper (D 3) (R 3) [6,9,96,272] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272] 13 (by decide) (choices 2) [33,96,129,160] r5809 c5809
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2264
  · exact u2265
  · exact u2266
  · exact u2267

def b5810 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 11 100 296 209 241 209 209 465), lower := (rows 7 11 100 296 16 32 64 128 256), losses := [] }

theorem u5810 : Upper (D 3) (R 3) [6,9,96,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5810
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5811 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5811 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5811 : Upper (D 3) (R 3) [6,9,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384] 13 (by decide) (choices 2) [33,96,129,160] r5811 c5811
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2268
  · exact u2269
  · exact u2270
  · exact u2271

def b5812 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 261 25 240 224 224 224 480), lower := (rows 7 11 261 25 16 32 64 128 256), losses := [] }

theorem u5812 : Upper (D 3) (R 3) [6,9,257,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5812
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5813 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 261 41 240 240 240 240 496), lower := (rows 7 11 261 41 16 32 64 128 256), losses := [] }

theorem u5813 : Upper (D 3) (R 3) [6,9,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5813
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5814 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5814 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5814 : Upper (D 3) (R 3) [6,9,257,48] 13 := by
  apply FastRouting.sound _ _ [6,9,257,48] 13 (by decide) (choices 2) [33,65,96,192] r5814 c5814
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2272
  · exact u2273
  · exact u2274
  · exact u2275

def r5815 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5815 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5815 : Upper (D 3) (R 3) [6,9,257,96] 13 := by
  apply FastRouting.sound _ _ [6,9,257,96] 13 (by decide) (choices 2) [33,96,129,160] r5815 c5815
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2276
  · exact u2277
  · exact u2278
  · exact u2279

def b5816 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 276 41 241 225 225 225 481), lower := (rows 7 11 276 41 16 32 64 128 256), losses := [] }

theorem u5816 : Upper (D 3) (R 3) [6,9,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5816
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5817 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5817 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5817 : Upper (D 3) (R 3) [6,9,272,96] 13 := by
  apply FastRouting.sound _ _ [6,9,272,96] 13 (by decide) (choices 2) [33,96,129,160] r5817 c5817
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2280
  · exact u2281
  · exact u2282
  · exact u2283

def b5818 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 292 25 241 225 225 225 481), lower := (rows 7 11 292 25 16 32 64 128 256), losses := [] }

theorem u5818 : Upper (D 3) (R 3) [6,9,288,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5818
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5819 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 292 41 209 241 209 209 465), lower := (rows 7 11 292 41 16 32 64 128 256), losses := [] }

theorem u5819 : Upper (D 3) (R 3) [6,9,288,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5819
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5819
end Delivery.IrregularNine14.P03
