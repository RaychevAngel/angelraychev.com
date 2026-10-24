import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0190
import IrregularNine14P06C0191
import IrregularNine14P06C0192

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r29880 : Route 9 := (fun mask => (mask,id))

def c29880 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29880 : Upper (D 6) (R 6) [10,17,96,33,132] 13 := by
  apply FastRouting.sound _ _ [10,17,96,33,132] 13 (by decide) (choices 1) [2,4,64,256] r29880 c29880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11454
  · exact u11455
  · exact u11456
  · exact u11457

def r29881 : Route 9 := (fun mask => (mask,id))

def c29881 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29881 : Upper (D 6) (R 6) [10,17,96,33,192] 13 := by
  apply FastRouting.sound _ _ [10,17,96,33,192] 13 (by decide) (choices 1) [2,4,256] r29881 c29881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11458
  · exact u11459
  · exact u11460

def r29882 : Route 9 := (fun mask => (mask,id))

def c29882 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29882 : Upper (D 6) (R 6) [10,17,96,33,384] 13 := by
  apply FastRouting.sound _ _ [10,17,96,33,384] 13 (by decide) (choices 1) [2,4,64] r29882 c29882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11461
  · exact u11462
  · exact u11463

def b29883 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 42 148 357 325 453 325), lower := (rows 11 19 100 42 148 32 64 128 256), losses := [] }

theorem u29883 : Upper (D 6) (R 6) [10,17,96,34,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29883
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29884 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 42 208 293 325 389 261), lower := (rows 11 19 100 42 208 32 64 128 256), losses := [] }

theorem u29884 : Upper (D 6) (R 6) [10,17,96,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29884
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29885 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 42 400 101 69 197 325), lower := (rows 11 19 100 42 400 32 64 128 256), losses := [] }

theorem u29885 : Upper (D 6) (R 6) [10,17,96,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29885
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29886 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 100 44 146 357 325 453 325), lower := (rows 11 19 100 44 146 32 64 128 256), losses := [] }

theorem u29886 : Upper (D 6) (R 6) [10,17,96,36,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29886
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29887 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 100 44 148 355 323 451 323), lower := (rows 11 19 100 44 148 32 64 128 256), losses := [] }

theorem u29887 : Upper (D 6) (R 6) [10,17,96,36,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29887
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29888 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 100 44 208 295 327 391 263), lower := (rows 11 19 100 44 208 32 64 128 256), losses := [] }

theorem u29888 : Upper (D 6) (R 6) [10,17,96,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29888
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29889 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 100 44 400 103 71 199 327), lower := (rows 11 19 100 44 400 32 64 128 256), losses := [] }

theorem u29889 : Upper (D 6) (R 6) [10,17,96,36,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29889
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29890 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 8, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 19 100 104 146 293 325 389 261), lower := (rows 11 19 100 104 146 32 64 128 256), losses := [] }

theorem u29890 : Upper (D 6) (R 6) [10,17,96,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29890
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29891 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 8, targets := 3 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 19 100 104 148 295 327 391 263), lower := (rows 11 19 100 104 148 32 64 128 256), losses := [] }

theorem u29891 : Upper (D 6) (R 6) [10,17,96,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29891
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29892 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 8, targets := 3 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 19 100 104 400 39 71 135 263), lower := (rows 11 19 100 104 400 32 64 128 256), losses := [] }

theorem u29892 : Upper (D 6) (R 6) [10,17,96,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29892
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29893 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 137 274 100 100 228 356), lower := (rows 11 19 100 137 274 32 64 128 256), losses := [] }

theorem u29893 : Upper (D 6) (R 6) [10,17,96,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29893
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29894 : Route 9 := (fun mask => (mask,id))

def c29894 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29894 : Upper (D 6) (R 6) [10,17,96,129,260] 13 := by
  apply FastRouting.sound _ _ [10,17,96,129,260] 13 (by decide) (choices 1) [2,4,64] r29894 c29894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11464
  · exact u11465
  · exact u11466

def r29895 : Route 9 := (fun mask => (mask,id))

def c29895 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29895 : Upper (D 6) (R 6) [10,17,96,129,288] 13 := by
  apply FastRouting.sound _ _ [10,17,96,129,288] 13 (by decide) (choices 1) [2,4,64] r29895 c29895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11467
  · exact u11468
  · exact u11469

def b29896 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 138 276 101 101 229 357), lower := (rows 11 19 100 138 276 32 64 128 256), losses := [] }

theorem u29896 : Upper (D 6) (R 6) [10,17,96,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29896
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29897 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 138 304 101 69 197 325), lower := (rows 11 19 100 138 304 32 64 128 256), losses := [] }

theorem u29897 : Upper (D 6) (R 6) [10,17,96,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29897
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m29898_2 : Upper (D 6) (R 6) [10,17,96,132,260,2] 13 :=
  permutation_upper _ _ _ [10,17,96,132,260,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11470

def r29898 : Route 9 := (fun mask => (mask,id))

def c29898 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29898 : Upper (D 6) (R 6) [10,17,96,132,260] 13 := by
  apply FastRouting.sound _ _ [10,17,96,132,260] 13 (by decide) (choices 1) [1,2,64] r29898 c29898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11470
  · exact m29898_2
  · exact u11471

def r29899 : Route 9 := (fun mask => (mask,id))

def c29899 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29899 : Upper (D 6) (R 6) [10,17,96,132,288] 13 := by
  apply FastRouting.sound _ _ [10,17,96,132,288] 13 (by decide) (choices 1) [1,2,4,64] r29899 c29899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11472
  · exact u11473
  · exact u11474
  · exact u11475

def r29900 : Route 9 := (fun mask => (mask,id))

def c29900 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29900 : Upper (D 6) (R 6) [10,17,96,160,320] 13 := by
  apply FastRouting.sound _ _ [10,17,96,160,320] 13 (by decide) (choices 1) [1,2,4] r29900 c29900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11476
  · exact u11477
  · exact u11478

def b29901 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 19, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 133 44 22 352 352 480 352), lower := (rows 11 19 133 44 22 32 64 128 256), losses := [] }

theorem u29901 : Upper (D 6) (R 6) [10,17,129,36,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29901
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29902 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 133 44 50 356 324 452 324), lower := (rows 11 19 133 44 50 32 64 128 256), losses := [] }

theorem u29902 : Upper (D 6) (R 6) [10,17,129,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29902
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29903 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 19 133 44 52 354 322 450 322), lower := (rows 11 19 133 44 52 32 64 128 256), losses := [] }

theorem u29903 : Upper (D 6) (R 6) [10,17,129,36,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29903
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29904 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 360, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 19 133 44 82 356 356 484 356), lower := (rows 11 19 133 44 82 32 64 128 256), losses := [] }

theorem u29904 : Upper (D 6) (R 6) [10,17,129,36,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29904
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29905 : Route 9 := (fun mask => (mask,id))

def c29905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29905 : Upper (D 6) (R 6) [10,17,129,36,68] 13 := by
  apply FastRouting.sound _ _ [10,17,129,36,68] 13 (by decide) (choices 1) [2,64,256] r29905 c29905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11479
  · exact u11480
  · exact u11481

def r29906 : Route 9 := (fun mask => (mask,id))

def c29906 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29906 : Upper (D 6) (R 6) [10,17,129,36,96] 13 := by
  apply FastRouting.sound _ _ [10,17,129,36,96] 13 (by decide) (choices 1) [2,4,64,256] r29906 c29906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11482
  · exact u11483
  · exact u11484
  · exact u11485

def b29907 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 104, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 19 133 44 274 100 100 228 356), lower := (rows 11 19 133 44 274 32 64 128 256), losses := [] }

theorem u29907 : Upper (D 6) (R 6) [10,17,129,36,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29907
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29908 : Route 9 := (fun mask => (mask,id))

def c29908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29908 : Upper (D 6) (R 6) [10,17,129,36,260] 13 := by
  apply FastRouting.sound _ _ [10,17,129,36,260] 13 (by decide) (choices 1) [2,64] r29908 c29908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11486
  · exact u11487

def r29909 : Route 9 := (fun mask => (mask,id))

def c29909 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29909 : Upper (D 6) (R 6) [10,17,129,36,288] 13 := by
  apply FastRouting.sound _ _ [10,17,129,36,288] 13 (by decide) (choices 1) [2,4,64] r29909 c29909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11488
  · exact u11489
  · exact u11490

def r29910 : Route 9 := (fun mask => (mask,id))

def c29910 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29910 : Upper (D 6) (R 6) [10,17,129,36,320] 13 := by
  apply FastRouting.sound _ _ [10,17,129,36,320] 13 (by decide) (choices 1) [2,4,64] r29910 c29910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11491
  · exact u11492
  · exact u11493

def b29911 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 19 133 104 22 356 356 484 356), lower := (rows 11 19 133 104 22 32 64 128 256), losses := [] }

theorem u29911 : Upper (D 6) (R 6) [10,17,129,96,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29911
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29912 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 133 104 50 356 324 452 324), lower := (rows 11 19 133 104 50 32 64 128 256), losses := [] }

theorem u29912 : Upper (D 6) (R 6) [10,17,129,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29912
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29913 : Route 9 := (fun mask => (mask,id))

def c29913 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29913 : Upper (D 6) (R 6) [10,17,129,96,36] 13 := by
  apply FastRouting.sound _ _ [10,17,129,96,36] 13 (by decide) (choices 1) [2,4,64,256] r29913 c29913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11494
  · exact u11495
  · exact u11496
  · exact u11497

def b29914 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 19, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 19 133 104 112 294 326 390 262), lower := (rows 11 19 133 104 112 32 64 128 256), losses := [] }

theorem u29914 : Upper (D 6) (R 6) [10,17,129,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29914
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29915 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 104, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 19 133 104 274 100 100 228 356), lower := (rows 11 19 133 104 274 32 64 128 256), losses := [] }

theorem u29915 : Upper (D 6) (R 6) [10,17,129,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29915
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29916 : Route 9 := (fun mask => (mask,id))

def c29916 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29916 : Upper (D 6) (R 6) [10,17,129,96,260] 13 := by
  apply FastRouting.sound _ _ [10,17,129,96,260] 13 (by decide) (choices 1) [2,4,64] r29916 c29916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11498
  · exact u11499
  · exact u11500

def r29917 : Route 9 := (fun mask => (mask,id))

def c29917 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29917 : Upper (D 6) (R 6) [10,17,129,96,288] 13 := by
  apply FastRouting.sound _ _ [10,17,129,96,288] 13 (by decide) (choices 1) [2,4,64] r29917 c29917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11501
  · exact u11502
  · exact u11503

def b29918 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 19, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 133 268 22 96 96 224 352), lower := (rows 11 19 133 268 22 32 64 128 256), losses := [] }

theorem u29918 : Upper (D 6) (R 6) [10,17,129,260,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29918
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29919 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 360, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 19 133 268 50 100 100 228 356), lower := (rows 11 19 133 268 50 32 64 128 256), losses := [] }

theorem u29919 : Upper (D 6) (R 6) [10,17,129,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29919
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29920 : Route 9 := (fun mask => (mask,id))

def c29920 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29920 : Upper (D 6) (R 6) [10,17,129,260,36] 13 := by
  apply FastRouting.sound _ _ [10,17,129,260,36] 13 (by decide) (choices 1) [2,64] r29920 c29920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11504
  · exact u11505

def r29921 : Route 9 := (fun mask => (mask,id))

def c29921 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29921 : Upper (D 6) (R 6) [10,17,129,260,96] 13 := by
  apply FastRouting.sound _ _ [10,17,129,260,96] 13 (by decide) (choices 1) [2,4,64] r29921 c29921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11506
  · exact u11507
  · exact u11508

def b29922 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 19 133 296 22 100 100 228 356), lower := (rows 11 19 133 296 22 32 64 128 256), losses := [] }

theorem u29922 : Upper (D 6) (R 6) [10,17,129,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29922
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29923 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 133 296 50 100 68 196 324), lower := (rows 11 19 133 296 50 32 64 128 256), losses := [] }

theorem u29923 : Upper (D 6) (R 6) [10,17,129,288,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29923
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29924 : Route 9 := (fun mask => (mask,id))

def c29924 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29924 : Upper (D 6) (R 6) [10,17,129,288,36] 13 := by
  apply FastRouting.sound _ _ [10,17,129,288,36] 13 (by decide) (choices 1) [2,4,64] r29924 c29924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11509
  · exact u11510
  · exact u11511

def b29925 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 360, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 19 133 296 82 100 100 228 356), lower := (rows 11 19 133 296 82 32 64 128 256), losses := [] }

theorem u29925 : Upper (D 6) (R 6) [10,17,129,288,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29925
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29926 : Route 9 := (fun mask => (mask,id))

def c29926 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29926 : Upper (D 6) (R 6) [10,17,129,288,68] 13 := by
  apply FastRouting.sound _ _ [10,17,129,288,68] 13 (by decide) (choices 1) [2,4,64] r29926 c29926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11512
  · exact u11513
  · exact u11514

def r29927 : Route 9 := (fun mask => (mask,id))

def c29927 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29927 : Upper (D 6) (R 6) [10,17,129,288,96] 13 := by
  apply FastRouting.sound _ _ [10,17,129,288,96] 13 (by decide) (choices 1) [2,4,64] r29927 c29927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11515
  · exact u11516
  · exact u11517

def b29928 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 11 84 356 356 484 356), lower := (rows 11 19 164 11 84 32 64 128 256), losses := [] }

theorem u29928 : Upper (D 6) (R 6) [10,17,160,3,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29928
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29929 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 11 112 356 324 452 324), lower := (rows 11 19 164 11 112 32 64 128 256), losses := [] }

theorem u29929 : Upper (D 6) (R 6) [10,17,160,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29929
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29930 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 11 276 100 100 228 356), lower := (rows 11 19 164 11 276 32 64 128 256), losses := [] }

theorem u29930 : Upper (D 6) (R 6) [10,17,160,3,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29930
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29931 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 11 304 100 68 196 324), lower := (rows 11 19 164 11 304 32 64 128 256), losses := [] }

theorem u29931 : Upper (D 6) (R 6) [10,17,160,3,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29931
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29932 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 11 336 100 100 228 356), lower := (rows 11 19 164 11 336 32 64 128 256), losses := [] }

theorem u29932 : Upper (D 6) (R 6) [10,17,160,3,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29932
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29933 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 27, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 164 13 22 352 352 480 352), lower := (rows 11 19 164 13 22 32 64 128 256), losses := [] }

theorem u29933 : Upper (D 6) (R 6) [10,17,160,5,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29933
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29934 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 164 13 50 356 324 452 324), lower := (rows 11 19 164 13 50 32 64 128 256), losses := [] }

theorem u29934 : Upper (D 6) (R 6) [10,17,160,5,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29934
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29935 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 164 13 52 354 322 450 322), lower := (rows 11 19 164 13 52 32 64 128 256), losses := [] }

theorem u29935 : Upper (D 6) (R 6) [10,17,160,5,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29935
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29936 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 13 82 356 356 484 356), lower := (rows 11 19 164 13 82 32 64 128 256), losses := [] }

theorem u29936 : Upper (D 6) (R 6) [10,17,160,5,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29936
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29937 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 164 13 84 354 354 482 354), lower := (rows 11 19 164 13 84 32 64 128 256), losses := [] }

theorem u29937 : Upper (D 6) (R 6) [10,17,160,5,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29937
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29938 : Route 9 := (fun mask => (mask,id))

def c29938 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29938 : Upper (D 6) (R 6) [10,17,160,5,96] 13 := by
  apply FastRouting.sound _ _ [10,17,160,5,96] 13 (by decide) (choices 1) [2,4,64,256] r29938 c29938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11518
  · exact u11519
  · exact u11520
  · exact u11521

def b29939 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 13 274 100 100 228 356), lower := (rows 11 19 164 13 274 32 64 128 256), losses := [] }

theorem u29939 : Upper (D 6) (R 6) [10,17,160,5,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29939
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29939
end Delivery.IrregularNine14.P06
