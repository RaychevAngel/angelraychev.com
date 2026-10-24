import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0057

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6900 : Route 9 := (fun mask => (mask,id))

def c6900 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6900 : Upper (D 5) (R 5) [6,80,160,260,9] 13 := by
  apply FastRouting.sound _ _ [6,80,160,260,9] 13 (by decide) (choices 1) [1,2,8] r6900 c6900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3429
  · exact u3430
  · exact u3431

def b6901 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 268 26 41 105 169 297), lower := (rows 7 82 164 268 26 32 64 128 256), losses := [] }

theorem u6901 : Upper (D 5) (R 5) [6,80,160,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6901
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6902 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 264, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 7 82 164 268 49 43 75 139 267), lower := (rows 7 82 164 268 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 9 16 0 81 145 273), good := (rows 463 466 132 268 475 0 64 128 256) }] }

theorem u6902 : Upper (D 5) (R 5) [6,80,160,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6902
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6903 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 268 50 41 73 137 265), lower := (rows 7 82 164 268 50 32 64 128 256), losses := [] }

theorem u6903 : Upper (D 5) (R 5) [6,80,160,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6903
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6904 : Route 9 := (fun mask => (mask,id))

def c6904 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6904 : Upper (D 5) (R 5) [6,80,160,260,40] 13 := by
  apply FastRouting.sound _ _ [6,80,160,260,40] 13 (by decide) (choices 1) [1,2,8] r6904 c6904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3432
  · exact u3433
  · exact u3434

def b6905 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 82 164 296 19 45 77 141 269), lower := (rows 7 82 164 296 19 32 64 128 256), losses := [] }

theorem u6905 : Upper (D 5) (R 5) [6,80,160,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6905
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6906 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 82 164 296 21 43 75 139 267), lower := (rows 7 82 164 296 21 32 64 128 256), losses := [] }

theorem u6906 : Upper (D 5) (R 5) [6,80,160,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6906
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6907 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 296 22 41 73 137 265), lower := (rows 7 82 164 296 22 32 64 128 256), losses := [] }

theorem u6907 : Upper (D 5) (R 5) [6,80,160,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6907
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6908 : Route 9 := (fun mask => (mask,id))

def c6908 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6908 : Upper (D 5) (R 5) [6,80,160,288,9] 13 := by
  apply FastRouting.sound _ _ [6,80,160,288,9] 13 (by decide) (choices 1) [1,2,4,8] r6908 c6908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3435
  · exact u3436
  · exact u3437
  · exact u3438

def b6909 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 296 26 45 77 141 269), lower := (rows 7 82 164 296 26 32 64 128 256), losses := [] }

theorem u6909 : Upper (D 5) (R 5) [6,80,160,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6909
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6910 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 82 164 296 28 43 75 139 267), lower := (rows 7 82 164 296 28 32 64 128 256), losses := [] }

theorem u6910 : Upper (D 5) (R 5) [6,80,160,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6910
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6911 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 82 388 41 19 44 108 172 300), lower := (rows 7 82 388 41 19 32 64 128 256), losses := [] }

theorem u6911 : Upper (D 5) (R 5) [6,80,384,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6911
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6912 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 82 388 41 21 42 106 170 298), lower := (rows 7 82 388 41 21 32 64 128 256), losses := [] }

theorem u6912 : Upper (D 5) (R 5) [6,80,384,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6912
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6913 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 388 41 22 41 105 169 297), lower := (rows 7 82 388 41 22 32 64 128 256), losses := [] }

theorem u6913 : Upper (D 5) (R 5) [6,80,384,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6913
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6914 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 82 388 41 25 46 110 174 302), lower := (rows 7 82 388 41 25 32 64 128 256), losses := [] }

theorem u6914 : Upper (D 5) (R 5) [6,80,384,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6914
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6915 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 388 41 26 45 109 173 301), lower := (rows 7 82 388 41 26 32 64 128 256), losses := [] }

theorem u6915 : Upper (D 5) (R 5) [6,80,384,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6915
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6916 : Route 9 := (fun mask => (mask,id))

def c6916 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6916 : Upper (D 5) (R 5) [6,80,384,33,12] 13 := by
  apply FastRouting.sound _ _ [6,80,384,33,12] 13 (by decide) (choices 1) [1,2,8] r6916 c6916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3439
  · exact u3440
  · exact u3441

def b6917 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 82 388 41 49 46 78 142 270), lower := (rows 7 82 388 41 49 32 64 128 256), losses := [] }

theorem u6917 : Upper (D 5) (R 5) [6,80,384,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6917
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6918 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 388 41 50 45 77 141 269), lower := (rows 7 82 388 41 50 32 64 128 256), losses := [] }

theorem u6918 : Upper (D 5) (R 5) [6,80,384,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6918
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6919 : Route 9 := (fun mask => (mask,id))

def c6919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6919 : Upper (D 5) (R 5) [6,80,384,33,36] 13 := by
  apply FastRouting.sound _ _ [6,80,384,33,36] 13 (by decide) (choices 1) [1,2,8] r6919 c6919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3442
  · exact u3443
  · exact u3444

def b6920 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 82 388 41 56 47 79 143 271), lower := (rows 7 82 388 41 56 32 64 128 256), losses := [] }

theorem u6920 : Upper (D 5) (R 5) [6,80,384,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6920
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6921 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 82 388 42 21 41 105 169 297), lower := (rows 7 82 388 42 21 32 64 128 256), losses := [] }

theorem u6921 : Upper (D 5) (R 5) [6,80,384,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6921
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6922 : Route 9 := (fun mask => (mask,id))

def c6922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6922 : Upper (D 5) (R 5) [6,80,384,34,9] 13 := by
  apply FastRouting.sound _ _ [6,80,384,34,9] 13 (by decide) (choices 1) [1,4,8] r6922 c6922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3445
  · exact u3446
  · exact u3447

def r6923 : Route 9 := (fun mask => (mask,id))

def c6923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6923 : Upper (D 5) (R 5) [6,80,384,34,12] 13 := by
  apply FastRouting.sound _ _ [6,80,384,34,12] 13 (by decide) (choices 1) [1,8] r6923 c6923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3448
  · exact u3449

def b6924 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 389, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 82 388 42 49 45 77 141 269), lower := (rows 7 82 388 42 49 32 64 128 256), losses := [] }

theorem u6924 : Upper (D 5) (R 5) [6,80,384,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6924
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6925 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 389, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 82 388 42 52 41 73 137 265), lower := (rows 7 82 388 42 52 32 64 128 256), losses := [] }

theorem u6925 : Upper (D 5) (R 5) [6,80,384,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6925
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6926 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 82 388 42 56 45 77 141 269), lower := (rows 7 82 388 42 56 32 64 128 256), losses := [] }

theorem u6926 : Upper (D 5) (R 5) [6,80,384,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6926
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6927 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 82 388 44 19 41 105 169 297), lower := (rows 7 82 388 44 19 32 64 128 256), losses := [] }

theorem u6927 : Upper (D 5) (R 5) [6,80,384,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6927
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6928 : Route 9 := (fun mask => (mask,id))

def c6928 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6928 : Upper (D 5) (R 5) [6,80,384,36,9] 13 := by
  apply FastRouting.sound _ _ [6,80,384,36,9] 13 (by decide) (choices 1) [1,2,8] r6928 c6928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3450
  · exact u3451
  · exact u3452

def b6929 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 388 44 26 41 105 169 297), lower := (rows 7 82 388 44 26 32 64 128 256), losses := [] }

theorem u6929 : Upper (D 5) (R 5) [6,80,384,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6929
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6930 : Route 9 := (fun mask => (mask,id))

def c6930 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6930 : Upper (D 5) (R 5) [6,80,384,36,33] 13 := by
  apply FastRouting.sound _ _ [6,80,384,36,33] 13 (by decide) (choices 1) [1,2,8] r6930 c6930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3453
  · exact u3454
  · exact u3455

def b6931 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 388 44 50 41 73 137 265), lower := (rows 7 82 388 44 50 32 64 128 256), losses := [] }

theorem u6931 : Upper (D 5) (R 5) [6,80,384,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6931
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6932 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 82 388 44 56 43 75 139 267), lower := (rows 7 82 388 44 56 32 64 128 256), losses := [] }

theorem u6932 : Upper (D 5) (R 5) [6,80,384,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6932
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6933 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 98 388 25 19 44 108 172 300), lower := (rows 7 98 388 25 19 32 64 128 256), losses := [] }

theorem u6933 : Upper (D 5) (R 5) [6,96,384,17,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6933
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6934 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 98 388 25 21 42 106 170 298), lower := (rows 7 98 388 25 21 32 64 128 256), losses := [] }

theorem u6934 : Upper (D 5) (R 5) [6,96,384,17,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6934
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6935 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 388 25 22 41 105 169 297), lower := (rows 7 98 388 25 22 32 64 128 256), losses := [] }

theorem u6935 : Upper (D 5) (R 5) [6,96,384,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6935
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6936 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 388 25 25 46 110 174 302), lower := (rows 7 98 388 25 25 32 64 128 256), losses := [] }

theorem u6936 : Upper (D 5) (R 5) [6,96,384,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6936
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6937 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 98 388 25 26 45 109 173 301), lower := (rows 7 98 388 25 26 32 64 128 256), losses := [] }

theorem u6937 : Upper (D 5) (R 5) [6,96,384,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6937
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6938 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 98 388 25 28 43 107 171 299), lower := (rows 7 98 388 25 28 32 64 128 256), losses := [] }

theorem u6938 : Upper (D 5) (R 5) [6,96,384,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6938
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6939 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 8, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 388 25 49 46 78 142 270), lower := (rows 7 98 388 25 49 32 64 128 256), losses := [] }

theorem u6939 : Upper (D 5) (R 5) [6,96,384,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6939
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6940 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 98 388 25 50 45 77 141 269), lower := (rows 7 98 388 25 50 32 64 128 256), losses := [] }

theorem u6940 : Upper (D 5) (R 5) [6,96,384,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6940
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6941 : Route 9 := (fun mask => (mask,id))

def c6941 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6941 : Upper (D 5) (R 5) [6,96,384,17,36] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,36] 13 (by decide) (choices 1) [1,2,8] r6941 c6941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3456
  · exact u3457
  · exact u3458

def r6942 : Route 9 := (fun mask => (mask,id))

def c6942 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6942 : Upper (D 5) (R 5) [6,96,384,17,40] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,40] 13 (by decide) (choices 1) [1,2,4,8] r6942 c6942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3459
  · exact u3460
  · exact u3461
  · exact u3462

def b6943 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 98 388 26 21 41 105 169 297), lower := (rows 7 98 388 26 21 32 64 128 256), losses := [] }

theorem u6943 : Upper (D 5) (R 5) [6,96,384,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6943
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6944 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 98 388 26 25 45 109 173 301), lower := (rows 7 98 388 26 25 32 64 128 256), losses := [] }

theorem u6944 : Upper (D 5) (R 5) [6,96,384,18,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6944
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6945 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 98 388 26 28 41 105 169 297), lower := (rows 7 98 388 26 28 32 64 128 256), losses := [] }

theorem u6945 : Upper (D 5) (R 5) [6,96,384,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6945
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6946 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 389, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 388 26 49 45 77 141 269), lower := (rows 7 98 388 26 49 32 64 128 256), losses := [] }

theorem u6946 : Upper (D 5) (R 5) [6,96,384,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6946
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6947 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 389, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 388 26 52 41 73 137 265), lower := (rows 7 98 388 26 52 32 64 128 256), losses := [] }

theorem u6947 : Upper (D 5) (R 5) [6,96,384,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6947
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6948 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 98 388 26 56 45 77 141 269), lower := (rows 7 98 388 26 56 32 64 128 256), losses := [] }

theorem u6948 : Upper (D 5) (R 5) [6,96,384,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6948
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6949 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 98 388 28 19 41 105 169 297), lower := (rows 7 98 388 28 19 32 64 128 256), losses := [] }

theorem u6949 : Upper (D 5) (R 5) [6,96,384,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6949
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6950 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 98 388 28 25 43 107 171 299), lower := (rows 7 98 388 28 25 32 64 128 256), losses := [] }

theorem u6950 : Upper (D 5) (R 5) [6,96,384,20,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6950
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6951 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 98 388 28 26 41 105 169 297), lower := (rows 7 98 388 28 26 32 64 128 256), losses := [] }

theorem u6951 : Upper (D 5) (R 5) [6,96,384,20,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6951
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6952 : Route 9 := (fun mask => (mask,id))

def c6952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6952 : Upper (D 5) (R 5) [6,96,384,20,33] 13 := by
  apply FastRouting.sound _ _ [6,96,384,20,33] 13 (by decide) (choices 1) [1,2,8] r6952 c6952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3463
  · exact u3464
  · exact u3465

def b6953 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 98 388 28 50 41 73 137 265), lower := (rows 7 98 388 28 50 32 64 128 256), losses := [] }

theorem u6953 : Upper (D 5) (R 5) [6,96,384,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6953
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6954 : Route 9 := (fun mask => (mask,id))

def c6954 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6954 : Upper (D 5) (R 5) [6,96,384,20,40] 13 := by
  apply FastRouting.sound _ _ [6,96,384,20,40] 13 (by decide) (choices 1) [1,2,8] r6954 c6954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3466
  · exact u3467
  · exact u3468

def b6955 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 98 388 41 19 60 92 156 284), lower := (rows 7 98 388 41 19 32 64 128 256), losses := [] }

theorem u6955 : Upper (D 5) (R 5) [6,96,384,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6955
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6956 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 98 388 41 21 58 90 154 282), lower := (rows 7 98 388 41 21 32 64 128 256), losses := [] }

theorem u6956 : Upper (D 5) (R 5) [6,96,384,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6956
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6957 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 98 388 41 22 57 89 153 281), lower := (rows 7 98 388 41 22 32 64 128 256), losses := [] }

theorem u6957 : Upper (D 5) (R 5) [6,96,384,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6957
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6958 : PairBound 9 := { available := 30, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 98 388 41 25 62 94 158 286), lower := (rows 7 98 388 41 25 32 64 128 256), losses := [] }

theorem u6958 : Upper (D 5) (R 5) [6,96,384,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6958
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6959 : PairBound 9 := { available := 29, camps := [{ cop := 4, region := 389, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 388 41 26 61 93 157 285), lower := (rows 7 98 388 41 26 32 64 128 256), losses := [] }

theorem u6959 : Upper (D 5) (R 5) [6,96,384,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6959
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u6959
end Delivery.IrregularNine14.P05
