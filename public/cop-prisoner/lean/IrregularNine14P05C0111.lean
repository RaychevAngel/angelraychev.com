import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0052
import IrregularNine14P05C0053

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6660 : Route 9 := (fun mask => (mask,id))

def c6660 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6660 : Upper (D 5) (R 5) [6,72,144,33,264] 13 := by
  apply FastRouting.sound _ _ [6,72,144,33,264] 13 (by decide) (choices 1) [1,2,4] r6660 c6660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3174
  · exact u3175
  · exact u3176

def r6661 : Route 9 := (fun mask => (mask,id))

def c6661 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6661 : Upper (D 5) (R 5) [6,72,144,33,288] 13 := by
  apply FastRouting.sound _ _ [6,72,144,33,288] 13 (by decide) (choices 1) [1,2,4,8] r6661 c6661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3177
  · exact u3178
  · exact u3179
  · exact u3180

def b6662 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 148 42 21 297 361 425 297), lower := (rows 7 74 148 42 21 32 64 128 256), losses := [] }

theorem u6662 : Upper (D 5) (R 5) [6,72,144,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6662
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6663 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 420, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 148 42 25 293 357 421 293), lower := (rows 7 74 148 42 25 32 64 128 256), losses := [] }

theorem u6663 : Upper (D 5) (R 5) [6,72,144,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6663
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6664 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 42 28 289 353 417 289), lower := (rows 7 74 148 42 28 32 64 128 256), losses := [] }

theorem u6664 : Upper (D 5) (R 5) [6,72,144,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6664
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6665 : Route 9 := (fun mask => (mask,id))

def c6665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6665 : Upper (D 5) (R 5) [6,72,144,34,33] 13 := by
  apply FastRouting.sound _ _ [6,72,144,34,33] 13 (by decide) (choices 1) [1,4,8,256] r6665 c6665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3181
  · exact u3182
  · exact u3183
  · exact u3184

def b6666 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 42 52 297 329 393 265), lower := (rows 7 74 148 42 52 32 64 128 256), losses := [] }

theorem u6666 : Upper (D 5) (R 5) [6,72,144,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6666
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6667 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 74 148 42 56 293 325 389 261), lower := (rows 7 74 148 42 56 32 64 128 256), losses := [] }

theorem u6667 : Upper (D 5) (R 5) [6,72,144,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6667
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6668 : Route 9 := (fun mask => (mask,id))

def c6668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6668 : Upper (D 5) (R 5) [6,72,144,34,257] 13 := by
  apply FastRouting.sound _ _ [6,72,144,34,257] 13 (by decide) (choices 1) [1,4,8] r6668 c6668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3185
  · exact u3186
  · exact u3187

def b6669 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 106, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 42 276 41 105 169 297), lower := (rows 7 74 148 42 276 32 64 128 256), losses := [] }

theorem u6669 : Upper (D 5) (R 5) [6,72,144,34,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6669
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6670 : Route 9 := (fun mask => (mask,id))

def c6670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6670 : Upper (D 5) (R 5) [6,72,144,34,264] 13 := by
  apply FastRouting.sound _ _ [6,72,144,34,264] 13 (by decide) (choices 1) [1,4] r6670 c6670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3188
  · exact u3189

def r6671 : Route 9 := (fun mask => (mask,id))

def c6671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6671 : Upper (D 5) (R 5) [6,72,144,34,288] 13 := by
  apply FastRouting.sound _ _ [6,72,144,34,288] 13 (by decide) (choices 1) [1,4,8] r6671 c6671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3190
  · exact u3191
  · exact u3192

def b6672 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 148 44 19 297 361 425 297), lower := (rows 7 74 148 44 19 32 64 128 256), losses := [] }

theorem u6672 : Upper (D 5) (R 5) [6,72,144,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6672
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6673 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(2,3)], upper := (rows 7 74 148 44 25 291 355 419 291), lower := (rows 7 74 148 44 25 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 20 0 16 33 65 129 257), good := (rows 487 66 148 36 501 32 64 128 256) }] }

theorem u6673 : Upper (D 5) (R 5) [6,72,144,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6673
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6674 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 148 44 26 289 353 417 289), lower := (rows 7 74 148 44 26 32 64 128 256), losses := [] }

theorem u6674 : Upper (D 5) (R 5) [6,72,144,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6674
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6675 : PairBound 9 := { available := 267, camps := [{ cop := 3, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 148 44 49 299 331 395 267), lower := (rows 7 74 148 44 49 32 64 128 256), losses := [] }

theorem u6675 : Upper (D 5) (R 5) [6,72,144,36,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6675
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6676 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 148 44 50 297 329 393 265), lower := (rows 7 74 148 44 50 32 64 128 256), losses := [] }

theorem u6676 : Upper (D 5) (R 5) [6,72,144,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6676
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6677 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 74 148 44 56 291 323 387 259), lower := (rows 7 74 148 44 56 32 64 128 256), losses := [] }

theorem u6677 : Upper (D 5) (R 5) [6,72,144,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6677
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6678 : Route 9 := (fun mask => (mask,id))

def c6678 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6678 : Upper (D 5) (R 5) [6,72,144,36,257] 13 := by
  apply FastRouting.sound _ _ [6,72,144,36,257] 13 (by decide) (choices 1) [1,2,8] r6678 c6678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3193
  · exact u3194
  · exact u3195

def r6679 : Route 9 := (fun mask => (mask,id))

def c6679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6679 : Upper (D 5) (R 5) [6,72,144,36,258] 13 := by
  apply FastRouting.sound _ _ [6,72,144,36,258] 13 (by decide) (choices 1) [1,8] r6679 c6679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3196
  · exact u3197

def r6680 : Route 9 := (fun mask => (mask,id))

def c6680 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6680 : Upper (D 5) (R 5) [6,72,144,36,264] 13 := by
  apply FastRouting.sound _ _ [6,72,144,36,264] 13 (by decide) (choices 1) [1,2] r6680 c6680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3198
  · exact u3199

def b6681 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 148 44 304 43 75 139 267), lower := (rows 7 74 148 44 304 32 64 128 256), losses := [] }

theorem u6681 : Upper (D 5) (R 5) [6,72,144,36,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6681
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6682 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 148 265 19 44 108 172 300), lower := (rows 7 74 148 265 19 32 64 128 256), losses := [] }

theorem u6682 : Upper (D 5) (R 5) [6,72,144,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6682
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6683 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 148 265 21 42 106 170 298), lower := (rows 7 74 148 265 21 32 64 128 256), losses := [] }

theorem u6683 : Upper (D 5) (R 5) [6,72,144,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6683
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6684 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 265 22 41 105 169 297), lower := (rows 7 74 148 265 22 32 64 128 256), losses := [] }

theorem u6684 : Upper (D 5) (R 5) [6,72,144,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6684
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6685 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 148 265 25 38 102 166 294), lower := (rows 7 74 148 265 25 32 64 128 256), losses := [] }

theorem u6685 : Upper (D 5) (R 5) [6,72,144,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6685
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6686 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 148 265 26 37 101 165 293), lower := (rows 7 74 148 265 26 32 64 128 256), losses := [] }

theorem u6686 : Upper (D 5) (R 5) [6,72,144,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6686
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6687 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 265 28 35 99 163 291), lower := (rows 7 74 148 265 28 32 64 128 256), losses := [] }

theorem u6687 : Upper (D 5) (R 5) [6,72,144,257,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6687
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6688 : Route 9 := (fun mask => (mask,id))

def c6688 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6688 : Upper (D 5) (R 5) [6,72,144,257,33] 13 := by
  apply FastRouting.sound _ _ [6,72,144,257,33] 13 (by decide) (choices 1) [2,4,8] r6688 c6688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3200
  · exact u3201
  · exact u3202

def r6689 : Route 9 := (fun mask => (mask,id))

def c6689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6689 : Upper (D 5) (R 5) [6,72,144,257,34] 13 := by
  apply FastRouting.sound _ _ [6,72,144,257,34] 13 (by decide) (choices 1) [1,4,8] r6689 c6689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3203
  · exact u3204
  · exact u3205

def b6690 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 265 52 43 107 171 299), lower := (rows 7 74 148 265 52 32 64 128 256), losses := [] }

theorem u6690 : Upper (D 5) (R 5) [6,72,144,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6690
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6691 : Route 9 := (fun mask => (mask,id))

def c6691 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6691 : Upper (D 5) (R 5) [6,72,144,257,40] 13 := by
  apply FastRouting.sound _ _ [6,72,144,257,40] 13 (by decide) (choices 1) [1,2,4] r6691 c6691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3206
  · exact u3207
  · exact u3208

def b6692 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 148 266 21 41 105 169 297), lower := (rows 7 74 148 266 21 32 64 128 256), losses := [] }

theorem u6692 : Upper (D 5) (R 5) [6,72,144,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6692
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6693 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 164, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 148 266 25 37 101 165 293), lower := (rows 7 74 148 266 25 32 64 128 256), losses := [] }

theorem u6693 : Upper (D 5) (R 5) [6,72,144,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6693
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6694 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 266 28 33 97 161 289), lower := (rows 7 74 148 266 28 32 64 128 256), losses := [] }

theorem u6694 : Upper (D 5) (R 5) [6,72,144,258,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6694
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6695 : Route 9 := (fun mask => (mask,id))

def c6695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6695 : Upper (D 5) (R 5) [6,72,144,258,33] 13 := by
  apply FastRouting.sound _ _ [6,72,144,258,33] 13 (by decide) (choices 1) [1,4,8] r6695 c6695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3209
  · exact u3210
  · exact u3211

def b6696 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 266 52 41 105 169 297), lower := (rows 7 74 148 266 52 32 64 128 256), losses := [] }

theorem u6696 : Upper (D 5) (R 5) [6,72,144,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6696
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6697 : Route 9 := (fun mask => (mask,id))

def c6697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6697 : Upper (D 5) (R 5) [6,72,144,258,40] 13 := by
  apply FastRouting.sound _ _ [6,72,144,258,40] 13 (by decide) (choices 1) [1,4] r6697 c6697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3212
  · exact u3213

def b6698 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 148 268 19 41 105 169 297), lower := (rows 7 74 148 268 19 32 64 128 256), losses := [] }

theorem u6698 : Upper (D 5) (R 5) [6,72,144,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6698
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6699 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(2,3)], upper := (rows 7 74 148 268 25 35 99 163 291), lower := (rows 7 74 148 268 25 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 20 0 16 33 65 129 257), good := (rows 487 66 148 260 501 32 64 128 256) }] }

theorem u6699 : Upper (D 5) (R 5) [6,72,144,260,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6699
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6700 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 148 268 26 33 97 161 289), lower := (rows 7 74 148 268 26 32 64 128 256), losses := [] }

theorem u6700 : Upper (D 5) (R 5) [6,72,144,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6700
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6701 : Route 9 := (fun mask => (mask,id))

def c6701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6701 : Upper (D 5) (R 5) [6,72,144,260,33] 13 := by
  apply FastRouting.sound _ _ [6,72,144,260,33] 13 (by decide) (choices 1) [1,2,8] r6701 c6701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3214
  · exact u3215
  · exact u3216

def r6702 : Route 9 := (fun mask => (mask,id))

def c6702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6702 : Upper (D 5) (R 5) [6,72,144,260,34] 13 := by
  apply FastRouting.sound _ _ [6,72,144,260,34] 13 (by decide) (choices 1) [1,8] r6702 c6702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3217
  · exact u3218

def r6703 : Route 9 := (fun mask => (mask,id))

def c6703 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6703 : Upper (D 5) (R 5) [6,72,144,260,40] 13 := by
  apply FastRouting.sound _ _ [6,72,144,260,40] 13 (by decide) (choices 1) [1,2] r6703 c6703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3219
  · exact u3220

def b6704 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 148 296 19 45 109 173 301), lower := (rows 7 74 148 296 19 32 64 128 256), losses := [] }

theorem u6704 : Upper (D 5) (R 5) [6,72,144,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6704
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6705 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 148 296 21 43 107 171 299), lower := (rows 7 74 148 296 21 32 64 128 256), losses := [] }

theorem u6705 : Upper (D 5) (R 5) [6,72,144,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6705
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6706 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 296 22 41 105 169 297), lower := (rows 7 74 148 296 22 32 64 128 256), losses := [] }

theorem u6706 : Upper (D 5) (R 5) [6,72,144,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6706
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6707 : Route 9 := (fun mask => (mask,id))

def c6707 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6707 : Upper (D 5) (R 5) [6,72,144,288,9] 13 := by
  apply FastRouting.sound _ _ [6,72,144,288,9] 13 (by decide) (choices 1) [1,2,4] r6707 c6707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3221
  · exact u3222
  · exact u3223

def b6708 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 148 296 26 37 101 165 293), lower := (rows 7 74 148 296 26 32 64 128 256), losses := [] }

theorem u6708 : Upper (D 5) (R 5) [6,72,144,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6708
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6709 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 296 28 35 99 163 291), lower := (rows 7 74 148 296 28 32 64 128 256), losses := [] }

theorem u6709 : Upper (D 5) (R 5) [6,72,144,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6709
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6710 : Route 9 := (fun mask => (mask,id))

def c6710 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6710 : Upper (D 5) (R 5) [6,72,144,288,33] 13 := by
  apply FastRouting.sound _ _ [6,72,144,288,33] 13 (by decide) (choices 1) [1,2,4,8] r6710 c6710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3224
  · exact u3225
  · exact u3226
  · exact u3227

def r6711 : Route 9 := (fun mask => (mask,id))

def c6711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6711 : Upper (D 5) (R 5) [6,72,144,288,34] 13 := by
  apply FastRouting.sound _ _ [6,72,144,288,34] 13 (by decide) (choices 1) [1,4,8] r6711 c6711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3228
  · exact u3229
  · exact u3230

def b6712 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 296 52 43 75 139 267), lower := (rows 7 74 148 296 52 32 64 128 256), losses := [] }

theorem u6712 : Upper (D 5) (R 5) [6,72,144,288,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6712
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6713 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 74 148 296 56 39 71 135 263), lower := (rows 7 74 148 296 56 32 64 128 256), losses := [] }

theorem u6713 : Upper (D 5) (R 5) [6,72,144,288,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6713
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6714 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 74 164 25 19 300 364 428 300), lower := (rows 7 74 164 25 19 32 64 128 256), losses := [] }

theorem u6714 : Upper (D 5) (R 5) [6,72,160,17,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6714
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6715 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 74 164 25 21 298 362 426 298), lower := (rows 7 74 164 25 21 32 64 128 256), losses := [] }

theorem u6715 : Upper (D 5) (R 5) [6,72,160,17,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6715
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6716 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 164 25 22 297 361 425 297), lower := (rows 7 74 164 25 22 32 64 128 256), losses := [] }

theorem u6716 : Upper (D 5) (R 5) [6,72,160,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6716
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6717 : PairBound 9 := { available := 294, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 164 25 25 294 358 422 294), lower := (rows 7 74 164 25 25 32 64 128 256), losses := [] }

theorem u6717 : Upper (D 5) (R 5) [6,72,160,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6717
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6718 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 74 164 25 26 293 357 421 293), lower := (rows 7 74 164 25 26 32 64 128 256), losses := [] }

theorem u6718 : Upper (D 5) (R 5) [6,72,160,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6718
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6719 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 74 164 25 28 291 355 419 291), lower := (rows 7 74 164 25 28 32 64 128 256), losses := [] }

theorem u6719 : Upper (D 5) (R 5) [6,72,160,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6719
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u6719
end Delivery.IrregularNine14.P05
