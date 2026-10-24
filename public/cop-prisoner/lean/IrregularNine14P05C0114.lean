import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0056
import IrregularNine14P05C0057

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6840 : Route 9 := (fun mask => (mask,id))

def c6840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6840 : Upper (D 5) (R 5) [6,72,384,33,12] 13 := by
  apply FastRouting.sound _ _ [6,72,384,33,12] 13 (by decide) (choices 1) [1,2,16] r6840 c6840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3362
  · exact u3363
  · exact u3364

def b6841 : PairBound 9 := { available := 30, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 388 41 49 62 94 158 286), lower := (rows 7 74 388 41 49 32 64 128 256), losses := [] }

theorem u6841 : Upper (D 5) (R 5) [6,72,384,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6841
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6842 : Route 9 := (fun mask => (mask,id))

def c6842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6842 : Upper (D 5) (R 5) [6,72,384,33,34] 13 := by
  apply FastRouting.sound _ _ [6,72,384,33,34] 13 (by decide) (choices 1) [1,4,8,16] r6842 c6842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3365
  · exact u3366
  · exact u3367
  · exact u3368

def r6843 : Route 9 := (fun mask => (mask,id))

def c6843 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6843 : Upper (D 5) (R 5) [6,72,384,33,36] 13 := by
  apply FastRouting.sound _ _ [6,72,384,33,36] 13 (by decide) (choices 1) [1,2,8,16] r6843 c6843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3369
  · exact u3370
  · exact u3371
  · exact u3372

def b6844 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 74 388 41 56 55 87 151 279), lower := (rows 7 74 388 41 56 32 64 128 256), losses := [] }

theorem u6844 : Upper (D 5) (R 5) [6,72,384,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6844
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6845 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 388 42 21 57 121 185 313), lower := (rows 7 74 388 42 21 32 64 128 256), losses := [] }

theorem u6845 : Upper (D 5) (R 5) [6,72,384,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6845
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6846 : PairBound 9 := { available := 53, camps := [{ cop := 4, region := 420, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 388 42 25 53 117 181 309), lower := (rows 7 74 388 42 25 32 64 128 256), losses := [] }

theorem u6846 : Upper (D 5) (R 5) [6,72,384,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6846
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6847 : Route 9 := (fun mask => (mask,id))

def c6847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6847 : Upper (D 5) (R 5) [6,72,384,34,12] 13 := by
  apply FastRouting.sound _ _ [6,72,384,34,12] 13 (by decide) (choices 1) [1,16] r6847 c6847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3373
  · exact u3374

def r6848 : Route 9 := (fun mask => (mask,id))

def c6848 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6848 : Upper (D 5) (R 5) [6,72,384,34,33] 13 := by
  apply FastRouting.sound _ _ [6,72,384,34,33] 13 (by decide) (choices 1) [1,4,8,16] r6848 c6848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3375
  · exact u3376
  · exact u3377
  · exact u3378

def r6849 : Route 9 := (fun mask => (mask,id))

def c6849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6849 : Upper (D 5) (R 5) [6,72,384,34,36] 13 := by
  apply FastRouting.sound _ _ [6,72,384,34,36] 13 (by decide) (choices 1) [1,8,16] r6849 c6849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3379
  · exact u3380
  · exact u3381

def b6850 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 74 388 42 56 53 85 149 277), lower := (rows 7 74 388 42 56 32 64 128 256), losses := [] }

theorem u6850 : Upper (D 5) (R 5) [6,72,384,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6850
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6851 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 388 44 19 57 121 185 313), lower := (rows 7 74 388 44 19 32 64 128 256), losses := [] }

theorem u6851 : Upper (D 5) (R 5) [6,72,384,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6851
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6852 : Route 9 := (fun mask => (mask,id))

def c6852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6852 : Upper (D 5) (R 5) [6,72,384,36,9] 13 := by
  apply FastRouting.sound _ _ [6,72,384,36,9] 13 (by decide) (choices 1) [1,2,16] r6852 c6852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3382
  · exact u3383
  · exact u3384

def b6853 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 388 44 26 49 113 177 305), lower := (rows 7 74 388 44 26 32 64 128 256), losses := [] }

theorem u6853 : Upper (D 5) (R 5) [6,72,384,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6853
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6854 : Route 9 := (fun mask => (mask,id))

def c6854 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6854 : Upper (D 5) (R 5) [6,72,384,36,33] 13 := by
  apply FastRouting.sound _ _ [6,72,384,36,33] 13 (by decide) (choices 1) [1,2,8,16] r6854 c6854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3385
  · exact u3386
  · exact u3387
  · exact u3388

def r6855 : Route 9 := (fun mask => (mask,id))

def c6855 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6855 : Upper (D 5) (R 5) [6,72,384,36,34] 13 := by
  apply FastRouting.sound _ _ [6,72,384,36,34] 13 (by decide) (choices 1) [1,8,16] r6855 c6855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3389
  · exact u3390
  · exact u3391

def b6856 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 74 388 44 56 51 83 147 275), lower := (rows 7 74 388 44 56 32 64 128 256), losses := [] }

theorem u6856 : Upper (D 5) (R 5) [6,72,384,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6856
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6857 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 388 56 19 45 109 173 301), lower := (rows 7 74 388 56 19 32 64 128 256), losses := [] }

theorem u6857 : Upper (D 5) (R 5) [6,72,384,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6857
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6858 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 388 56 21 43 107 171 299), lower := (rows 7 74 388 56 21 32 64 128 256), losses := [] }

theorem u6858 : Upper (D 5) (R 5) [6,72,384,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6858
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6859 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 74 388 56 22 41 105 169 297), lower := (rows 7 74 388 56 22 32 64 128 256), losses := [] }

theorem u6859 : Upper (D 5) (R 5) [6,72,384,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6859
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6860 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 421, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 388 56 25 39 103 167 295), lower := (rows 7 74 388 56 25 32 64 128 256), losses := [] }

theorem u6860 : Upper (D 5) (R 5) [6,72,384,48,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6860
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6861 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 388 56 26 37 101 165 293), lower := (rows 7 74 388 56 26 32 64 128 256), losses := [] }

theorem u6861 : Upper (D 5) (R 5) [6,72,384,48,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6861
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6862 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 421, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 388 56 28 35 99 163 291), lower := (rows 7 74 388 56 28 32 64 128 256), losses := [] }

theorem u6862 : Upper (D 5) (R 5) [6,72,384,48,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6862
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6863 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 388 56 49 47 79 143 271), lower := (rows 7 74 388 56 49 32 64 128 256), losses := [] }

theorem u6863 : Upper (D 5) (R 5) [6,72,384,48,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6863
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6864 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 388 56 50 45 77 141 269), lower := (rows 7 74 388 56 50 32 64 128 256), losses := [] }

theorem u6864 : Upper (D 5) (R 5) [6,72,384,48,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6864
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6865 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 388 56 52 43 75 139 267), lower := (rows 7 74 388 56 52 32 64 128 256), losses := [] }

theorem u6865 : Upper (D 5) (R 5) [6,72,384,48,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6865
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6866 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 24, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 74 388 56 56 39 71 135 263), lower := (rows 7 74 388 56 56 32 64 128 256), losses := [] }

theorem u6866 : Upper (D 5) (R 5) [6,72,384,48,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6866
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6867 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 82 164 41 19 300 332 396 268), lower := (rows 7 82 164 41 19 32 64 128 256), losses := [] }

theorem u6867 : Upper (D 5) (R 5) [6,80,160,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6867
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6868 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 82 164 41 21 298 330 394 266), lower := (rows 7 82 164 41 21 32 64 128 256), losses := [] }

theorem u6868 : Upper (D 5) (R 5) [6,80,160,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6868
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6869 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 41 22 297 329 393 265), lower := (rows 7 82 164 41 22 32 64 128 256), losses := [] }

theorem u6869 : Upper (D 5) (R 5) [6,80,160,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6869
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6870 : PairBound 9 := { available := 270, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 82 164 41 25 302 334 398 270), lower := (rows 7 82 164 41 25 32 64 128 256), losses := [] }

theorem u6870 : Upper (D 5) (R 5) [6,80,160,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6870
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6871 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 41 26 301 333 397 269), lower := (rows 7 82 164 41 26 32 64 128 256), losses := [] }

theorem u6871 : Upper (D 5) (R 5) [6,80,160,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6871
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6872 : PairBound 9 := { available := 267, camps := [{ cop := 4, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 82 164 41 28 299 331 395 267), lower := (rows 7 82 164 41 28 32 64 128 256), losses := [] }

theorem u6872 : Upper (D 5) (R 5) [6,80,160,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6872
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6873 : Route 9 := (fun mask => (mask,id))

def c6873 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6873 : Upper (D 5) (R 5) [6,80,160,33,257] 13 := by
  apply FastRouting.sound _ _ [6,80,160,33,257] 13 (by decide) (choices 1) [2,4,8] r6873 c6873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3392
  · exact u3393
  · exact u3394

def b6874 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 172, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 41 274 45 77 141 269), lower := (rows 7 82 164 41 274 32 64 128 256), losses := [] }

theorem u6874 : Upper (D 5) (R 5) [6,80,160,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6874
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6875 : Route 9 := (fun mask => (mask,id))

def c6875 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6875 : Upper (D 5) (R 5) [6,80,160,33,260] 13 := by
  apply FastRouting.sound _ _ [6,80,160,33,260] 13 (by decide) (choices 1) [1,2,8] r6875 c6875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3395
  · exact u3396
  · exact u3397

def r6876 : Route 9 := (fun mask => (mask,id))

def c6876 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6876 : Upper (D 5) (R 5) [6,80,160,33,264] 13 := by
  apply FastRouting.sound _ _ [6,80,160,33,264] 13 (by decide) (choices 1) [1,2,4,8] r6876 c6876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3398
  · exact u3399
  · exact u3400
  · exact u3401

def b6877 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 82 164 42 21 297 329 393 265), lower := (rows 7 82 164 42 21 32 64 128 256), losses := [] }

theorem u6877 : Upper (D 5) (R 5) [6,80,160,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6877
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6878 : Route 9 := (fun mask => (mask,id))

def c6878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6878 : Upper (D 5) (R 5) [6,80,160,34,9] 13 := by
  apply FastRouting.sound _ _ [6,80,160,34,9] 13 (by decide) (choices 1) [1,4,8,256] r6878 c6878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3402
  · exact u3403
  · exact u3404
  · exact u3405

def b6879 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 82 164 42 28 297 329 393 265), lower := (rows 7 82 164 42 28 32 64 128 256), losses := [] }

theorem u6879 : Upper (D 5) (R 5) [6,80,160,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6879
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6880 : Route 9 := (fun mask => (mask,id))

def c6880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6880 : Upper (D 5) (R 5) [6,80,160,34,257] 13 := by
  apply FastRouting.sound _ _ [6,80,160,34,257] 13 (by decide) (choices 1) [1,4,8] r6880 c6880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3406
  · exact u3407
  · exact u3408

def r6881 : Route 9 := (fun mask => (mask,id))

def c6881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6881 : Upper (D 5) (R 5) [6,80,160,34,260] 13 := by
  apply FastRouting.sound _ _ [6,80,160,34,260] 13 (by decide) (choices 1) [1,8] r6881 c6881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3409
  · exact u3410

def r6882 : Route 9 := (fun mask => (mask,id))

def c6882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6882 : Upper (D 5) (R 5) [6,80,160,34,264] 13 := by
  apply FastRouting.sound _ _ [6,80,160,34,264] 13 (by decide) (choices 1) [1,4,8] r6882 c6882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3411
  · exact u3412
  · exact u3413

def b6883 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 82 164 265 19 44 108 172 300), lower := (rows 7 82 164 265 19 32 64 128 256), losses := [] }

theorem u6883 : Upper (D 5) (R 5) [6,80,160,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6883
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6884 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 82 164 265 21 42 106 170 298), lower := (rows 7 82 164 265 21 32 64 128 256), losses := [] }

theorem u6884 : Upper (D 5) (R 5) [6,80,160,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6884
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6885 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 265 22 41 105 169 297), lower := (rows 7 82 164 265 22 32 64 128 256), losses := [] }

theorem u6885 : Upper (D 5) (R 5) [6,80,160,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6885
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6886 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 82 164 265 25 46 110 174 302), lower := (rows 7 82 164 265 25 32 64 128 256), losses := [] }

theorem u6886 : Upper (D 5) (R 5) [6,80,160,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6886
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6887 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 265 26 45 109 173 301), lower := (rows 7 82 164 265 26 32 64 128 256), losses := [] }

theorem u6887 : Upper (D 5) (R 5) [6,80,160,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6887
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6888 : Route 9 := (fun mask => (mask,id))

def c6888 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6888 : Upper (D 5) (R 5) [6,80,160,257,12] 13 := by
  apply FastRouting.sound _ _ [6,80,160,257,12] 13 (by decide) (choices 1) [1,2,8] r6888 c6888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3414
  · exact u3415
  · exact u3416

def b6889 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 264, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 7 82 164 265 49 46 78 142 270), lower := (rows 7 82 164 265 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 25 16 0 65 129 257), good := (rows 463 90 132 457 475 0 64 128 256) }] }

theorem u6889 : Upper (D 5) (R 5) [6,80,160,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6889
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6890 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 265 50 45 77 141 269), lower := (rows 7 82 164 265 50 32 64 128 256), losses := [] }

theorem u6890 : Upper (D 5) (R 5) [6,80,160,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6890
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6891 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 82 164 265 52 43 75 139 267), lower := (rows 7 82 164 265 52 32 64 128 256), losses := [] }

theorem u6891 : Upper (D 5) (R 5) [6,80,160,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6891
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6892 : Route 9 := (fun mask => (mask,id))

def c6892 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6892 : Upper (D 5) (R 5) [6,80,160,257,40] 13 := by
  apply FastRouting.sound _ _ [6,80,160,257,40] 13 (by decide) (choices 1) [1,2,4,8] r6892 c6892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3417
  · exact u3418
  · exact u3419
  · exact u3420

def b6893 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 82 164 266 21 41 105 169 297), lower := (rows 7 82 164 266 21 32 64 128 256), losses := [] }

theorem u6893 : Upper (D 5) (R 5) [6,80,160,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6893
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6894 : Route 9 := (fun mask => (mask,id))

def c6894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6894 : Upper (D 5) (R 5) [6,80,160,258,9] 13 := by
  apply FastRouting.sound _ _ [6,80,160,258,9] 13 (by decide) (choices 1) [1,4,8] r6894 c6894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3421
  · exact u3422
  · exact u3423

def r6895 : Route 9 := (fun mask => (mask,id))

def c6895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6895 : Upper (D 5) (R 5) [6,80,160,258,12] 13 := by
  apply FastRouting.sound _ _ [6,80,160,258,12] 13 (by decide) (choices 1) [1,8] r6895 c6895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3424
  · exact u3425

def b6896 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 264, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 7 82 164 266 49 45 77 141 269), lower := (rows 7 82 164 266 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 25 16 0 65 129 257), good := (rows 463 90 132 266 475 0 64 128 256) }] }

theorem u6896 : Upper (D 5) (R 5) [6,80,160,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6896
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6897 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 82 164 266 52 41 73 137 265), lower := (rows 7 82 164 266 52 32 64 128 256), losses := [] }

theorem u6897 : Upper (D 5) (R 5) [6,80,160,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6897
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6898 : Route 9 := (fun mask => (mask,id))

def c6898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6898 : Upper (D 5) (R 5) [6,80,160,258,40] 13 := by
  apply FastRouting.sound _ _ [6,80,160,258,40] 13 (by decide) (choices 1) [1,4,8] r6898 c6898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3426
  · exact u3427
  · exact u3428

def b6899 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 82 164 268 19 41 105 169 297), lower := (rows 7 82 164 268 19 32 64 128 256), losses := [] }

theorem u6899 : Upper (D 5) (R 5) [6,80,160,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6899
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u6899
end Delivery.IrregularNine14.P05
