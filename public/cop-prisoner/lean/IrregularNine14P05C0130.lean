import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0069
import IrregularNine14P05C0070

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7800 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 21, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 19 98 37 137 22 300 332 396 268), lower := (rows 19 98 37 137 22 32 64 128 256), losses := [] }

theorem u7800 : Upper (D 5) (R 5) [18,96,33,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7800
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7801 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 37 137 26 300 332 396 268), lower := (rows 19 98 37 137 26 32 64 128 256), losses := [] }

theorem u7801 : Upper (D 5) (R 5) [18,96,33,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7801
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7802 : Route 9 := (fun mask => (mask,id))

def c7802 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7802 : Upper (D 5) (R 5) [18,96,33,129,12] 13 := by
  apply FastRouting.sound _ _ [18,96,33,129,12] 13 (by decide) (choices 1) [2,4,8,256] r7802 c7802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4164
  · exact u4165
  · exact u4166
  · exact u4167

def b7803 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 37 137 274 44 76 140 268), lower := (rows 19 98 37 137 274 32 64 128 256), losses := [] }

theorem u7803 : Upper (D 5) (R 5) [18,96,33,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7803
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7804 : Route 9 := (fun mask => (mask,id))

def c7804 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7804 : Upper (D 5) (R 5) [18,96,33,129,260] 13 := by
  apply FastRouting.sound _ _ [18,96,33,129,260] 13 (by decide) (choices 1) [2,4,8] r7804 c7804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4168
  · exact u4169
  · exact u4170

def r7805 : Route 9 := (fun mask => (mask,id))

def c7805 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7805 : Upper (D 5) (R 5) [18,96,33,129,264] 13 := by
  apply FastRouting.sound _ _ [18,96,33,129,264] 13 (by decide) (choices 1) [2,4,8] r7805 c7805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4171
  · exact u4172
  · exact u4173

def b7806 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 21, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 19 98 37 138 21 300 332 396 268), lower := (rows 19 98 37 138 21 32 64 128 256), losses := [] }

theorem u7806 : Upper (D 5) (R 5) [18,96,33,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7806
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7807 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 98 37 138 25 300 332 396 268), lower := (rows 19 98 37 138 25 32 64 128 256), losses := [] }

theorem u7807 : Upper (D 5) (R 5) [18,96,33,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7807
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7808 : Route 9 := (fun mask => (mask,id))

def c7808 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7808 : Upper (D 5) (R 5) [18,96,33,130,12] 13 := by
  apply FastRouting.sound _ _ [18,96,33,130,12] 13 (by decide) (choices 1) [1,4,8,256] r7808 c7808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4174
  · exact u4175
  · exact u4176
  · exact u4177

def b7809 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 98 37 138 273 44 76 140 268), lower := (rows 19 98 37 138 273 32 64 128 256), losses := [] }

theorem u7809 : Upper (D 5) (R 5) [18,96,33,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7809
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7810 : Route 9 := (fun mask => (mask,id))

def c7810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7810 : Upper (D 5) (R 5) [18,96,33,130,260] 13 := by
  apply FastRouting.sound _ _ [18,96,33,130,260] 13 (by decide) (choices 1) [1,4,8] r7810 c7810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4178
  · exact u4179
  · exact u4180

def r7811 : Route 9 := (fun mask => (mask,id))

def c7811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7811 : Upper (D 5) (R 5) [18,96,33,130,264] 13 := by
  apply FastRouting.sound _ _ [18,96,33,130,264] 13 (by decide) (choices 1) [1,4,8] r7811 c7811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4181
  · exact u4182
  · exact u4183

def b7812 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 98 37 140 19 300 332 396 268), lower := (rows 19 98 37 140 19 32 64 128 256), losses := [] }

theorem u7812 : Upper (D 5) (R 5) [18,96,33,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7812
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7813 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 21, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 19 98 37 140 21 298 330 394 266), lower := (rows 19 98 37 140 21 32 64 128 256), losses := [] }

theorem u7813 : Upper (D 5) (R 5) [18,96,33,132,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7813
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7814 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 21, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 19 98 37 140 22 297 329 393 265), lower := (rows 19 98 37 140 22 32 64 128 256), losses := [] }

theorem u7814 : Upper (D 5) (R 5) [18,96,33,132,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7814
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7815 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 98 37 140 25 302 334 398 270), lower := (rows 19 98 37 140 25 32 64 128 256), losses := [] }

theorem u7815 : Upper (D 5) (R 5) [18,96,33,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7815
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7816 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 37 140 26 301 333 397 269), lower := (rows 19 98 37 140 26 32 64 128 256), losses := [] }

theorem u7816 : Upper (D 5) (R 5) [18,96,33,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7816
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7817 : PairBound 9 := { available := 267, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 98 37 140 28 299 331 395 267), lower := (rows 19 98 37 140 28 32 64 128 256), losses := [] }

theorem u7817 : Upper (D 5) (R 5) [18,96,33,132,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7817
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7818 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 98 37 140 273 46 78 142 270), lower := (rows 19 98 37 140 273 32 64 128 256), losses := [] }

theorem u7818 : Upper (D 5) (R 5) [18,96,33,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7818
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7819 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 37 140 274 45 77 141 269), lower := (rows 19 98 37 140 274 32 64 128 256), losses := [] }

theorem u7819 : Upper (D 5) (R 5) [18,96,33,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7819
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7820 : Route 9 := (fun mask => (mask,id))

def c7820 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7820 : Upper (D 5) (R 5) [18,96,33,132,260] 13 := by
  apply FastRouting.sound _ _ [18,96,33,132,260] 13 (by decide) (choices 1) [1,2,8] r7820 c7820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4184
  · exact u4185
  · exact u4186

def r7821 : Route 9 := (fun mask => (mask,id))

def c7821 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7821 : Upper (D 5) (R 5) [18,96,33,132,264] 13 := by
  apply FastRouting.sound _ _ [18,96,33,132,264] 13 (by decide) (choices 1) [1,2,4,8] r7821 c7821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4187
  · exact u4188
  · exact u4189
  · exact u4190

def b7822 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 98 37 392 19 44 76 140 268), lower := (rows 19 98 37 392 19 32 64 128 256), losses := [] }

theorem u7822 : Upper (D 5) (R 5) [18,96,33,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7822
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7823 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 21, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 19 98 37 392 21 46 78 142 270), lower := (rows 19 98 37 392 21 32 64 128 256), losses := [] }

theorem u7823 : Upper (D 5) (R 5) [18,96,33,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7823
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7824 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 21, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 19 98 37 392 22 45 77 141 269), lower := (rows 19 98 37 392 22 32 64 128 256), losses := [] }

theorem u7824 : Upper (D 5) (R 5) [18,96,33,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7824
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7825 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 98 37 392 25 46 78 142 270), lower := (rows 19 98 37 392 25 32 64 128 256), losses := [] }

theorem u7825 : Upper (D 5) (R 5) [18,96,33,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7825
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7826 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 37 392 26 45 77 141 269), lower := (rows 19 98 37 392 26 32 64 128 256), losses := [] }

theorem u7826 : Upper (D 5) (R 5) [18,96,33,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7826
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7827 : Route 9 := (fun mask => (mask,id))

def c7827 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7827 : Upper (D 5) (R 5) [18,96,33,384,12] 13 := by
  apply FastRouting.sound _ _ [18,96,33,384,12] 13 (by decide) (choices 1) [1,2,4,8] r7827 c7827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4191
  · exact u4192
  · exact u4193
  · exact u4194

def b7828 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 137 19 300 332 396 268), lower := (rows 19 98 44 137 19 32 64 128 256), losses := [] }

theorem u7828 : Upper (D 5) (R 5) [18,96,40,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7828
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7829 : PairBound 9 := { available := 270, camps := [{ cop := 3, region := 358, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 44 137 21 302 334 398 270), lower := (rows 19 98 44 137 21 32 64 128 256), losses := [] }

theorem u7829 : Upper (D 5) (R 5) [18,96,40,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7829
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7830 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 98 44 137 22 301 333 397 269), lower := (rows 19 98 44 137 22 32 64 128 256), losses := [] }

theorem u7830 : Upper (D 5) (R 5) [18,96,40,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7830
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7831 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 98 44 137 25 294 326 390 262), lower := (rows 19 98 44 137 25 32 64 128 256), losses := [] }

theorem u7831 : Upper (D 5) (R 5) [18,96,40,129,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7831
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7832 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 137 26 293 325 389 261), lower := (rows 19 98 44 137 26 32 64 128 256), losses := [] }

theorem u7832 : Upper (D 5) (R 5) [18,96,40,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7832
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7833 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 98 44 137 28 295 327 391 263), lower := (rows 19 98 44 137 28 32 64 128 256), losses := [] }

theorem u7833 : Upper (D 5) (R 5) [18,96,40,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7833
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7834 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 102, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 44 137 273 46 78 142 270), lower := (rows 19 98 44 137 273 32 64 128 256), losses := [] }

theorem u7834 : Upper (D 5) (R 5) [18,96,40,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7834
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7835 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 137 274 45 77 141 269), lower := (rows 19 98 44 137 274 32 64 128 256), losses := [] }

theorem u7835 : Upper (D 5) (R 5) [18,96,40,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7835
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7836 : Route 9 := (fun mask => (mask,id))

def c7836 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7836 : Upper (D 5) (R 5) [18,96,40,129,260] 13 := by
  apply FastRouting.sound _ _ [18,96,40,129,260] 13 (by decide) (choices 1) [1,2,4,8] r7836 c7836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4195
  · exact u4196
  · exact u4197
  · exact u4198

def r7837 : Route 9 := (fun mask => (mask,id))

def c7837 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7837 : Upper (D 5) (R 5) [18,96,40,129,264] 13 := by
  apply FastRouting.sound _ _ [18,96,40,129,264] 13 (by decide) (choices 1) [1,2,4] r7837 c7837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4199
  · exact u4200
  · exact u4201

def r7838 : Route 9 := (fun mask => (mask,id))

def c7838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7838 : Upper (D 5) (R 5) [18,96,40,130,5] 13 := by
  apply FastRouting.sound _ _ [18,96,40,130,5] 13 (by decide) (choices 1) [1,4,8,256] r7838 c7838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4202
  · exact u4203
  · exact u4204
  · exact u4205

def b7839 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 98 44 138 25 293 325 389 261), lower := (rows 19 98 44 138 25 32 64 128 256), losses := [] }

theorem u7839 : Upper (D 5) (R 5) [18,96,40,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7839
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7840 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 98 44 138 28 293 325 389 261), lower := (rows 19 98 44 138 28 32 64 128 256), losses := [] }

theorem u7840 : Upper (D 5) (R 5) [18,96,40,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7840
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7841 : Route 9 := (fun mask => (mask,id))

def c7841 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7841 : Upper (D 5) (R 5) [18,96,40,130,257] 13 := by
  apply FastRouting.sound _ _ [18,96,40,130,257] 13 (by decide) (choices 1) [1,4,8] r7841 c7841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4206
  · exact u4207
  · exact u4208

def r7842 : Route 9 := (fun mask => (mask,id))

def c7842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7842 : Upper (D 5) (R 5) [18,96,40,130,260] 13 := by
  apply FastRouting.sound _ _ [18,96,40,130,260] 13 (by decide) (choices 1) [1,4,8] r7842 c7842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4209
  · exact u4210
  · exact u4211

def r7843 : Route 9 := (fun mask => (mask,id))

def c7843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7843 : Upper (D 5) (R 5) [18,96,40,130,264] 13 := by
  apply FastRouting.sound _ _ [18,96,40,130,264] 13 (by decide) (choices 1) [1,4] r7843 c7843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4212
  · exact u4213

def b7844 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 140 19 301 333 397 269), lower := (rows 19 98 44 140 19 32 64 128 256), losses := [] }

theorem u7844 : Upper (D 5) (R 5) [18,96,40,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7844
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7845 : Route 9 := (fun mask => (mask,id))

def c7845 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7845 : Upper (D 5) (R 5) [18,96,40,132,5] 13 := by
  apply FastRouting.sound _ _ [18,96,40,132,5] 13 (by decide) (choices 1) [1,2,8,256] r7845 c7845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4214
  · exact u4215
  · exact u4216
  · exact u4217

def b7846 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 98 44 140 22 297 329 393 265), lower := (rows 19 98 44 140 22 32 64 128 256), losses := [] }

theorem u7846 : Upper (D 5) (R 5) [18,96,40,132,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7846
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7847 : Route 9 := (fun mask => (mask,id))

def c7847 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7847 : Upper (D 5) (R 5) [18,96,40,132,9] 13 := by
  apply FastRouting.sound _ _ [18,96,40,132,9] 13 (by decide) (choices 1) [1,2,4,256] r7847 c7847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4218
  · exact u4219
  · exact u4220
  · exact u4221

def b7848 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 140 26 293 325 389 261), lower := (rows 19 98 44 140 26 32 64 128 256), losses := [] }

theorem u7848 : Upper (D 5) (R 5) [18,96,40,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7848
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7849 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 355, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 140 28 291 323 387 259), lower := (rows 19 98 44 140 28 32 64 128 256), losses := [] }

theorem u7849 : Upper (D 5) (R 5) [18,96,40,132,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7849
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7850 : Route 9 := (fun mask => (mask,id))

def c7850 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7850 : Upper (D 5) (R 5) [18,96,40,132,257] 13 := by
  apply FastRouting.sound _ _ [18,96,40,132,257] 13 (by decide) (choices 1) [1,2,4,8] r7850 c7850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4222
  · exact u4223
  · exact u4224
  · exact u4225

def b7851 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 140 274 45 77 141 269), lower := (rows 19 98 44 140 274 32 64 128 256), losses := [] }

theorem u7851 : Upper (D 5) (R 5) [18,96,40,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7851
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7852 : Route 9 := (fun mask => (mask,id))

def c7852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7852 : Upper (D 5) (R 5) [18,96,40,132,260] 13 := by
  apply FastRouting.sound _ _ [18,96,40,132,260] 13 (by decide) (choices 1) [1,2,8] r7852 c7852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4226
  · exact u4227
  · exact u4228

def r7853 : Route 9 := (fun mask => (mask,id))

def c7853 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7853 : Upper (D 5) (R 5) [18,96,40,132,264] 13 := by
  apply FastRouting.sound _ _ [18,96,40,132,264] 13 (by decide) (choices 1) [1,2,4] r7853 c7853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4229
  · exact u4230
  · exact u4231

def b7854 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 392 19 45 77 141 269), lower := (rows 19 98 44 392 19 32 64 128 256), losses := [] }

theorem u7854 : Upper (D 5) (R 5) [18,96,40,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7854
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7855 : Route 9 := (fun mask => (mask,id))

def c7855 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7855 : Upper (D 5) (R 5) [18,96,40,384,5] 13 := by
  apply FastRouting.sound _ _ [18,96,40,384,5] 13 (by decide) (choices 1) [1,2,4,8] r7855 c7855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4232
  · exact u4233
  · exact u4234
  · exact u4235

def b7856 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 98 44 392 22 45 77 141 269), lower := (rows 19 98 44 392 22 32 64 128 256), losses := [] }

theorem u7856 : Upper (D 5) (R 5) [18,96,40,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7856
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7857 : Route 9 := (fun mask => (mask,id))

def c7857 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7857 : Upper (D 5) (R 5) [18,96,40,384,9] 13 := by
  apply FastRouting.sound _ _ [18,96,40,384,9] 13 (by decide) (choices 1) [1,2,4] r7857 c7857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4236
  · exact u4237
  · exact u4238

def b7858 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 392 26 37 69 133 261), lower := (rows 19 98 44 392 26 32 64 128 256), losses := [] }

theorem u7858 : Upper (D 5) (R 5) [18,96,40,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7858
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7859 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 98 44 392 28 39 71 135 263), lower := (rows 19 98 44 392 28 32 64 128 256), losses := [] }

theorem u7859 : Upper (D 5) (R 5) [18,96,40,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7859
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u7859
end Delivery.IrregularNine14.P05
