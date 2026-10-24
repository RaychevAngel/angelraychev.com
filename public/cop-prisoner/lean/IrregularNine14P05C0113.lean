import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0054
import IrregularNine14P05C0055
import IrregularNine14P05C0056

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6780 : Route 9 := (fun mask => (mask,id))

def c6780 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6780 : Upper (D 5) (R 5) [6,72,160,257,12] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,12] 13 (by decide) (choices 1) [1,2,16] r6780 c6780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3298
  · exact u3299
  · exact u3300

def r6781 : Route 9 := (fun mask => (mask,id))

def c6781 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6781 : Upper (D 5) (R 5) [6,72,160,257,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,33] 13 (by decide) (choices 1) [2,4,8,16] r6781 c6781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3301
  · exact u3302
  · exact u3303
  · exact u3304

def r6782 : Route 9 := (fun mask => (mask,id))

def c6782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6782 : Upper (D 5) (R 5) [6,72,160,257,34] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,34] 13 (by decide) (choices 1) [1,4,8,16] r6782 c6782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3305
  · exact u3306
  · exact u3307
  · exact u3308

def b6783 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 74 164 265 52 59 91 155 283), lower := (rows 7 74 164 265 52 32 64 128 256), losses := [] }

theorem u6783 : Upper (D 5) (R 5) [6,72,160,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6783
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6784 : Route 9 := (fun mask => (mask,id))

def c6784 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6784 : Upper (D 5) (R 5) [6,72,160,257,40] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,40] 13 (by decide) (choices 1) [1,2,4,16] r6784 c6784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3309
  · exact u3310
  · exact u3311
  · exact u3312

def b6785 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 164 266 21 57 121 185 313), lower := (rows 7 74 164 266 21 32 64 128 256), losses := [] }

theorem u6785 : Upper (D 5) (R 5) [6,72,160,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6785
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6786 : PairBound 9 := { available := 53, camps := [{ cop := 4, region := 164, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 164 266 25 53 117 181 309), lower := (rows 7 74 164 266 25 32 64 128 256), losses := [] }

theorem u6786 : Upper (D 5) (R 5) [6,72,160,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6786
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6787 : Route 9 := (fun mask => (mask,id))

def c6787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6787 : Upper (D 5) (R 5) [6,72,160,258,12] 13 := by
  apply FastRouting.sound _ _ [6,72,160,258,12] 13 (by decide) (choices 1) [1,16] r6787 c6787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3313
  · exact u3314

def r6788 : Route 9 := (fun mask => (mask,id))

def c6788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6788 : Upper (D 5) (R 5) [6,72,160,258,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,258,33] 13 (by decide) (choices 1) [1,4,8,16] r6788 c6788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3315
  · exact u3316
  · exact u3317
  · exact u3318

def b6789 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 74 164 266 52 57 89 153 281), lower := (rows 7 74 164 266 52 32 64 128 256), losses := [] }

theorem u6789 : Upper (D 5) (R 5) [6,72,160,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6789
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6790 : Route 9 := (fun mask => (mask,id))

def c6790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6790 : Upper (D 5) (R 5) [6,72,160,258,40] 13 := by
  apply FastRouting.sound _ _ [6,72,160,258,40] 13 (by decide) (choices 1) [1,4,16] r6790 c6790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3319
  · exact u3320
  · exact u3321

def b6791 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 268 19 57 121 185 313), lower := (rows 7 74 164 268 19 32 64 128 256), losses := [] }

theorem u6791 : Upper (D 5) (R 5) [6,72,160,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6791
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6792 : Route 9 := (fun mask => (mask,id))

def c6792 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6792 : Upper (D 5) (R 5) [6,72,160,260,9] 13 := by
  apply FastRouting.sound _ _ [6,72,160,260,9] 13 (by decide) (choices 1) [1,2,16] r6792 c6792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3322
  · exact u3323
  · exact u3324

def b6793 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 164 268 26 49 113 177 305), lower := (rows 7 74 164 268 26 32 64 128 256), losses := [] }

theorem u6793 : Upper (D 5) (R 5) [6,72,160,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6793
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6794 : Route 9 := (fun mask => (mask,id))

def c6794 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6794 : Upper (D 5) (R 5) [6,72,160,260,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,260,33] 13 (by decide) (choices 1) [1,2,8,16] r6794 c6794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3325
  · exact u3326
  · exact u3327
  · exact u3328

def r6795 : Route 9 := (fun mask => (mask,id))

def c6795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6795 : Upper (D 5) (R 5) [6,72,160,260,34] 13 := by
  apply FastRouting.sound _ _ [6,72,160,260,34] 13 (by decide) (choices 1) [1,8,16] r6795 c6795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3329
  · exact u3330
  · exact u3331

def r6796 : Route 9 := (fun mask => (mask,id))

def c6796 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6796 : Upper (D 5) (R 5) [6,72,160,260,40] 13 := by
  apply FastRouting.sound _ _ [6,72,160,260,40] 13 (by decide) (choices 1) [1,2,16] r6796 c6796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3332
  · exact u3333
  · exact u3334

def b6797 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 280 19 45 109 173 301), lower := (rows 7 74 164 280 19 32 64 128 256), losses := [] }

theorem u6797 : Upper (D 5) (R 5) [6,72,160,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6797
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6798 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 164 280 21 43 107 171 299), lower := (rows 7 74 164 280 21 32 64 128 256), losses := [] }

theorem u6798 : Upper (D 5) (R 5) [6,72,160,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6798
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6799 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 74 164 280 22 41 105 169 297), lower := (rows 7 74 164 280 22 32 64 128 256), losses := [] }

theorem u6799 : Upper (D 5) (R 5) [6,72,160,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6799
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6800 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 280 25 39 103 167 295), lower := (rows 7 74 164 280 25 32 64 128 256), losses := [] }

theorem u6800 : Upper (D 5) (R 5) [6,72,160,272,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6800
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6801 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 164 280 26 37 101 165 293), lower := (rows 7 74 164 280 26 32 64 128 256), losses := [] }

theorem u6801 : Upper (D 5) (R 5) [6,72,160,272,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6801
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6802 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 280 28 35 99 163 291), lower := (rows 7 74 164 280 28 32 64 128 256), losses := [] }

theorem u6802 : Upper (D 5) (R 5) [6,72,160,272,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6802
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6803 : Route 9 := (fun mask => (mask,id))

def c6803 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6803 : Upper (D 5) (R 5) [6,72,160,272,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,272,33] 13 (by decide) (choices 1) [1,2,4,8] r6803 c6803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3335
  · exact u3336
  · exact u3337
  · exact u3338

def r6804 : Route 9 := (fun mask => (mask,id))

def c6804 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6804 : Upper (D 5) (R 5) [6,72,160,272,34] 13 := by
  apply FastRouting.sound _ _ [6,72,160,272,34] 13 (by decide) (choices 1) [1,4,8] r6804 c6804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3339
  · exact u3340
  · exact u3341

def b6805 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 74 164 280 52 43 75 139 267), lower := (rows 7 74 164 280 52 32 64 128 256), losses := [] }

theorem u6805 : Upper (D 5) (R 5) [6,72,160,272,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6805
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6806 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 280 56 39 71 135 263), lower := (rows 7 74 164 280 56 32 64 128 256), losses := [] }

theorem u6806 : Upper (D 5) (R 5) [6,72,160,272,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6806
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6807 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 164 296 19 61 93 157 285), lower := (rows 7 74 164 296 19 32 64 128 256), losses := [] }

theorem u6807 : Upper (D 5) (R 5) [6,72,160,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6807
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6808 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 164 296 21 59 91 155 283), lower := (rows 7 74 164 296 21 32 64 128 256), losses := [] }

theorem u6808 : Upper (D 5) (R 5) [6,72,160,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6808
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6809 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 74 164 296 22 57 89 153 281), lower := (rows 7 74 164 296 22 32 64 128 256), losses := [] }

theorem u6809 : Upper (D 5) (R 5) [6,72,160,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6809
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6810 : Route 9 := (fun mask => (mask,id))

def c6810 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6810 : Upper (D 5) (R 5) [6,72,160,288,9] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,9] 13 (by decide) (choices 1) [1,2,4,16] r6810 c6810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3342
  · exact u3343
  · exact u3344
  · exact u3345

def b6811 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 164 296 26 53 85 149 277), lower := (rows 7 74 164 296 26 32 64 128 256), losses := [] }

theorem u6811 : Upper (D 5) (R 5) [6,72,160,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6811
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6812 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 296 28 51 83 147 275), lower := (rows 7 74 164 296 28 32 64 128 256), losses := [] }

theorem u6812 : Upper (D 5) (R 5) [6,72,160,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6812
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6813 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 74 388 25 19 44 108 172 300), lower := (rows 7 74 388 25 19 32 64 128 256), losses := [] }

theorem u6813 : Upper (D 5) (R 5) [6,72,384,17,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6813
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6814 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 74 388 25 21 42 106 170 298), lower := (rows 7 74 388 25 21 32 64 128 256), losses := [] }

theorem u6814 : Upper (D 5) (R 5) [6,72,384,17,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6814
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6815 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 388 25 22 41 105 169 297), lower := (rows 7 74 388 25 22 32 64 128 256), losses := [] }

theorem u6815 : Upper (D 5) (R 5) [6,72,384,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6815
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6816 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 388 25 25 38 102 166 294), lower := (rows 7 74 388 25 25 32 64 128 256), losses := [] }

theorem u6816 : Upper (D 5) (R 5) [6,72,384,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6816
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6817 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 74 388 25 26 37 101 165 293), lower := (rows 7 74 388 25 26 32 64 128 256), losses := [] }

theorem u6817 : Upper (D 5) (R 5) [6,72,384,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6817
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6818 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 74 388 25 28 35 99 163 291), lower := (rows 7 74 388 25 28 32 64 128 256), losses := [] }

theorem u6818 : Upper (D 5) (R 5) [6,72,384,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6818
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6819 : PairBound 9 := { available := 46, camps := [{ cop := 4, region := 8, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 388 25 49 46 110 174 302), lower := (rows 7 74 388 25 49 32 64 128 256), losses := [] }

theorem u6819 : Upper (D 5) (R 5) [6,72,384,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6819
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6820 : Route 9 := (fun mask => (mask,id))

def c6820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6820 : Upper (D 5) (R 5) [6,72,384,17,34] 13 := by
  apply FastRouting.sound _ _ [6,72,384,17,34] 13 (by decide) (choices 1) [1,4,8] r6820 c6820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3346
  · exact u3347
  · exact u3348

def r6821 : Route 9 := (fun mask => (mask,id))

def c6821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6821 : Upper (D 5) (R 5) [6,72,384,17,36] 13 := by
  apply FastRouting.sound _ _ [6,72,384,17,36] 13 (by decide) (choices 1) [1,2,8] r6821 c6821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3349
  · exact u3350
  · exact u3351

def b6822 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 421, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 388 25 56 39 103 167 295), lower := (rows 7 74 388 25 56 32 64 128 256), losses := [] }

theorem u6822 : Upper (D 5) (R 5) [6,72,384,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6822
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6823 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 388 26 21 41 105 169 297), lower := (rows 7 74 388 26 21 32 64 128 256), losses := [] }

theorem u6823 : Upper (D 5) (R 5) [6,72,384,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6823
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6824 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 74 388 26 25 37 101 165 293), lower := (rows 7 74 388 26 25 32 64 128 256), losses := [] }

theorem u6824 : Upper (D 5) (R 5) [6,72,384,18,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6824
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6825 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 74 388 26 28 33 97 161 289), lower := (rows 7 74 388 26 28 32 64 128 256), losses := [] }

theorem u6825 : Upper (D 5) (R 5) [6,72,384,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6825
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6826 : Route 9 := (fun mask => (mask,id))

def c6826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6826 : Upper (D 5) (R 5) [6,72,384,18,33] 13 := by
  apply FastRouting.sound _ _ [6,72,384,18,33] 13 (by decide) (choices 1) [1,4,8] r6826 c6826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3352
  · exact u3353
  · exact u3354

def r6827 : Route 9 := (fun mask => (mask,id))

def c6827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6827 : Upper (D 5) (R 5) [6,72,384,18,36] 13 := by
  apply FastRouting.sound _ _ [6,72,384,18,36] 13 (by decide) (choices 1) [1,8] r6827 c6827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3355
  · exact u3356

def b6828 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 420, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 388 26 56 37 101 165 293), lower := (rows 7 74 388 26 56 32 64 128 256), losses := [] }

theorem u6828 : Upper (D 5) (R 5) [6,72,384,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6828
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6829 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 388 28 19 41 105 169 297), lower := (rows 7 74 388 28 19 32 64 128 256), losses := [] }

theorem u6829 : Upper (D 5) (R 5) [6,72,384,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6829
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6830 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 74 388 28 25 35 99 163 291), lower := (rows 7 74 388 28 25 32 64 128 256), losses := [] }

theorem u6830 : Upper (D 5) (R 5) [6,72,384,20,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6830
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6831 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 388 28 26 33 97 161 289), lower := (rows 7 74 388 28 26 32 64 128 256), losses := [] }

theorem u6831 : Upper (D 5) (R 5) [6,72,384,20,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6831
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6832 : Route 9 := (fun mask => (mask,id))

def c6832 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6832 : Upper (D 5) (R 5) [6,72,384,20,33] 13 := by
  apply FastRouting.sound _ _ [6,72,384,20,33] 13 (by decide) (choices 1) [1,2,8] r6832 c6832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3357
  · exact u3358
  · exact u3359

def r6833 : Route 9 := (fun mask => (mask,id))

def c6833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6833 : Upper (D 5) (R 5) [6,72,384,20,34] 13 := by
  apply FastRouting.sound _ _ [6,72,384,20,34] 13 (by decide) (choices 1) [1,8] r6833 c6833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3360
  · exact u3361

def b6834 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 421, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 388 28 56 35 99 163 291), lower := (rows 7 74 388 28 56 32 64 128 256), losses := [] }

theorem u6834 : Upper (D 5) (R 5) [6,72,384,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6834
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6835 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 388 41 19 60 124 188 316), lower := (rows 7 74 388 41 19 32 64 128 256), losses := [] }

theorem u6835 : Upper (D 5) (R 5) [6,72,384,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6835
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6836 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 388 41 21 58 122 186 314), lower := (rows 7 74 388 41 21 32 64 128 256), losses := [] }

theorem u6836 : Upper (D 5) (R 5) [6,72,384,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6836
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6837 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 74 388 41 22 57 121 185 313), lower := (rows 7 74 388 41 22 32 64 128 256), losses := [] }

theorem u6837 : Upper (D 5) (R 5) [6,72,384,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6837
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6838 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 388 41 25 54 118 182 310), lower := (rows 7 74 388 41 25 32 64 128 256), losses := [] }

theorem u6838 : Upper (D 5) (R 5) [6,72,384,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6838
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6839 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 388 41 26 53 117 181 309), lower := (rows 7 74 388 41 26 32 64 128 256), losses := [] }

theorem u6839 : Upper (D 5) (R 5) [6,72,384,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6839
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u6839
end Delivery.IrregularNine14.P05
