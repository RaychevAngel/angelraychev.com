import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0039
import IrregularNine14P05C0040

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5880 : Route 9 := (fun mask => (mask,id))

def c5880 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5880 : Upper (D 5) (R 5) [6,33,192,272,9] 13 := by
  apply FastRouting.sound _ _ [6,33,192,272,9] 13 (by decide) (choices 1) [2,4,8] r5880 c5880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2377
  · exact u2378
  · exact u2379

def r5881 : Route 9 := (fun mask => (mask,id))

def c5881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5881 : Upper (D 5) (R 5) [6,33,192,272,10] 13 := by
  apply FastRouting.sound _ _ [6,33,192,272,10] 13 (by decide) (choices 1) [1,4,8] r5881 c5881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2380
  · exact u2381
  · exact u2382

def r5882 : Route 9 := (fun mask => (mask,id))

def c5882 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5882 : Upper (D 5) (R 5) [6,33,192,272,12] 13 := by
  apply FastRouting.sound _ _ [6,33,192,272,12] 13 (by decide) (choices 1) [1,2,8] r5882 c5882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2383
  · exact u2384
  · exact u2385

def b5883 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 196 280 49 46 78 142 270), lower := (rows 7 35 196 280 49 32 64 128 256), losses := [] }

theorem u5883 : Upper (D 5) (R 5) [6,33,192,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5883
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5884 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 196 280 50 45 77 141 269), lower := (rows 7 35 196 280 50 32 64 128 256), losses := [] }

theorem u5884 : Upper (D 5) (R 5) [6,33,192,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5884
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5885 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 196 280 52 43 75 139 267), lower := (rows 7 35 196 280 52 32 64 128 256), losses := [] }

theorem u5885 : Upper (D 5) (R 5) [6,33,192,272,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5885
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5886 : Route 9 := (fun mask => (mask,id))

def c5886 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5886 : Upper (D 5) (R 5) [6,33,192,272,40] 13 := by
  apply FastRouting.sound _ _ [6,33,192,272,40] 13 (by decide) (choices 1) [1,2,4,8] r5886 c5886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2386
  · exact u2387
  · exact u2388
  · exact u2389

def b5887 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 296 19 60 92 156 284), lower := (rows 7 35 196 296 19 32 64 128 256), losses := [] }

theorem u5887 : Upper (D 5) (R 5) [6,33,192,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5887
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5888 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 196 296 21 58 90 154 282), lower := (rows 7 35 196 296 21 32 64 128 256), losses := [] }

theorem u5888 : Upper (D 5) (R 5) [6,33,192,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5888
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5889 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 35 196 296 22 57 89 153 281), lower := (rows 7 35 196 296 22 32 64 128 256), losses := [] }

theorem u5889 : Upper (D 5) (R 5) [6,33,192,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5889
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5890 : Route 9 := (fun mask => (mask,id))

def c5890 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5890 : Upper (D 5) (R 5) [6,33,192,288,9] 13 := by
  apply FastRouting.sound _ _ [6,33,192,288,9] 13 (by decide) (choices 1) [2,4,8,16] r5890 c5890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2390
  · exact u2391
  · exact u2392
  · exact u2393

def b5891 : PairBound 9 := { available := 29, camps := [{ cop := 4, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 296 26 61 93 157 285), lower := (rows 7 35 196 296 26 32 64 128 256), losses := [] }

theorem u5891 : Upper (D 5) (R 5) [6,33,192,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5891
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5892 : Route 9 := (fun mask => (mask,id))

def c5892 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5892 : Upper (D 5) (R 5) [6,33,192,288,12] 13 := by
  apply FastRouting.sound _ _ [6,33,192,288,12] 13 (by decide) (choices 1) [1,2,8,16] r5892 c5892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2394
  · exact u2395
  · exact u2396
  · exact u2397

def b5893 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 69 25 22 424 488 424 424), lower := (rows 7 42 69 25 22 32 64 128 256), losses := [] }

theorem u5893 : Upper (D 5) (R 5) [6,40,65,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5893
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5894 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 69 25 26 420 484 420 420), lower := (rows 7 42 69 25 26 32 64 128 256), losses := [] }

theorem u5894 : Upper (D 5) (R 5) [6,40,65,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5894
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5895 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 42 69 25 28 418 482 418 418), lower := (rows 7 42 69 25 28 32 64 128 256), losses := [] }

theorem u5895 : Upper (D 5) (R 5) [6,40,65,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5895
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5896 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 25 50 428 460 396 396), lower := (rows 7 42 69 25 50 32 64 128 256), losses := [] }

theorem u5896 : Upper (D 5) (R 5) [6,40,65,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5896
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5897 : PairBound 9 := { available := 394, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 25 52 426 458 394 394), lower := (rows 7 42 69 25 52 32 64 128 256), losses := [] }

theorem u5897 : Upper (D 5) (R 5) [6,40,65,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5897
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5898 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 25 56 422 454 390 390), lower := (rows 7 42 69 25 56 32 64 128 256), losses := [] }

theorem u5898 : Upper (D 5) (R 5) [6,40,65,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5898
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5899 : Route 9 := (fun mask => (mask,id))

def c5899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5899 : Upper (D 5) (R 5) [6,40,65,17,130] 13 := by
  apply FastRouting.sound _ _ [6,40,65,17,130] 13 (by decide) (choices 1) [4,8,256] r5899 c5899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2398
  · exact u2399
  · exact u2400

def b5900 : PairBound 9 := { available := 298, camps := [{ cop := 3, region := 290, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 25 148 298 362 426 298), lower := (rows 7 42 69 25 148 32 64 128 256), losses := [] }

theorem u5900 : Upper (D 5) (R 5) [6,40,65,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5900
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5901 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 325, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 25 152 294 358 422 294), lower := (rows 7 42 69 25 152 32 64 128 256), losses := [] }

theorem u5901 : Upper (D 5) (R 5) [6,40,65,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5901
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5902 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 25 176 302 334 398 270), lower := (rows 7 42 69 25 176 32 64 128 256), losses := [] }

theorem u5902 : Upper (D 5) (R 5) [6,40,65,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5902
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5903 : Route 9 := (fun mask => (mask,id))

def c5903 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5903 : Upper (D 5) (R 5) [6,40,65,17,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,17,384] 13 (by decide) (choices 1) [2,4,8] r5903 c5903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2401
  · exact u2402
  · exact u2403

def b5904 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 426, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 26 21 424 488 424 424), lower := (rows 7 42 69 26 21 32 64 128 256), losses := [] }

theorem u5904 : Upper (D 5) (R 5) [6,40,65,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5904
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5905 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 69 26 25 420 484 420 420), lower := (rows 7 42 69 26 25 32 64 128 256), losses := [] }

theorem u5905 : Upper (D 5) (R 5) [6,40,65,18,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5905
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5906 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 42 69 26 28 417 481 417 417), lower := (rows 7 42 69 26 28 32 64 128 256), losses := [] }

theorem u5906 : Upper (D 5) (R 5) [6,40,65,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5906
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5907 : PairBound 9 := { available := 396, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 26 49 428 460 396 396), lower := (rows 7 42 69 26 49 32 64 128 256), losses := [] }

theorem u5907 : Upper (D 5) (R 5) [6,40,65,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5907
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5908 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 26 52 425 457 393 393), lower := (rows 7 42 69 26 52 32 64 128 256), losses := [] }

theorem u5908 : Upper (D 5) (R 5) [6,40,65,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5908
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5909 : PairBound 9 := { available := 389, camps := [{ cop := 5, region := 26, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 26 56 421 453 389 389), lower := (rows 7 42 69 26 56 32 64 128 256), losses := [] }

theorem u5909 : Upper (D 5) (R 5) [6,40,65,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5909
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5910 : Route 9 := (fun mask => (mask,id))

def c5910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5910 : Upper (D 5) (R 5) [6,40,65,18,129] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,129] 13 (by decide) (choices 1) [4,8,256] r5910 c5910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2404
  · exact u2405
  · exact u2406

def r5911 : Route 9 := (fun mask => (mask,id))

def c5911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5911 : Upper (D 5) (R 5) [6,40,65,18,132] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,132] 13 (by decide) (choices 1) [1,8,256] r5911 c5911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2407
  · exact u2408
  · exact u2409

def b5912 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 356, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 42 69 26 152 293 357 421 293), lower := (rows 7 42 69 26 152 32 64 128 256), losses := [] }

theorem u5912 : Upper (D 5) (R 5) [6,40,65,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5912
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5913 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 26 176 301 333 397 269), lower := (rows 7 42 69 26 176 32 64 128 256), losses := [] }

theorem u5913 : Upper (D 5) (R 5) [6,40,65,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5913
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5914 : Route 9 := (fun mask => (mask,id))

def c5914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5914 : Upper (D 5) (R 5) [6,40,65,18,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,384] 13 (by decide) (choices 1) [1,4,8] r5914 c5914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2410
  · exact u2411
  · exact u2412

def b5915 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 69 28 19 424 488 424 424), lower := (rows 7 42 69 28 19 32 64 128 256), losses := [] }

theorem u5915 : Upper (D 5) (R 5) [6,40,65,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5915
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5916 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 42 69 28 25 418 482 418 418), lower := (rows 7 42 69 28 25 32 64 128 256), losses := [] }

theorem u5916 : Upper (D 5) (R 5) [6,40,65,20,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5916
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5917 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 28 26 417 481 417 417), lower := (rows 7 42 69 28 26 32 64 128 256), losses := [] }

theorem u5917 : Upper (D 5) (R 5) [6,40,65,20,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5917
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5918 : PairBound 9 := { available := 394, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 28 49 426 458 394 394), lower := (rows 7 42 69 28 49 32 64 128 256), losses := [] }

theorem u5918 : Upper (D 5) (R 5) [6,40,65,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5918
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5919 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 28 50 425 457 393 393), lower := (rows 7 42 69 28 50 32 64 128 256), losses := [] }

theorem u5919 : Upper (D 5) (R 5) [6,40,65,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5919
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5920 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 28 56 419 451 387 387), lower := (rows 7 42 69 28 56 32 64 128 256), losses := [] }

theorem u5920 : Upper (D 5) (R 5) [6,40,65,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5920
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5921 : PairBound 9 := { available := 298, camps := [{ cop := 3, region := 290, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 28 145 298 362 426 298), lower := (rows 7 42 69 28 145 32 64 128 256), losses := [] }

theorem u5921 : Upper (D 5) (R 5) [6,40,65,20,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5921
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5922 : Route 9 := (fun mask => (mask,id))

def c5922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5922 : Upper (D 5) (R 5) [6,40,65,20,130] 13 := by
  apply FastRouting.sound _ _ [6,40,65,20,130] 13 (by decide) (choices 1) [1,8,256] r5922 c5922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2413
  · exact u2414
  · exact u2415

def b5923 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 325, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 28 152 291 355 419 291), lower := (rows 7 42 69 28 152 32 64 128 256), losses := [] }

theorem u5923 : Upper (D 5) (R 5) [6,40,65,20,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5923
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5924 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 28 176 299 331 395 267), lower := (rows 7 42 69 28 176 32 64 128 256), losses := [] }

theorem u5924 : Upper (D 5) (R 5) [6,40,65,20,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5924
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5925 : Route 9 := (fun mask => (mask,id))

def c5925 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5925 : Upper (D 5) (R 5) [6,40,65,20,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,20,384] 13 (by decide) (choices 1) [1,2,8] r5925 c5925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2416
  · exact u2417
  · exact u2418

def b5926 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 42 69 137 22 312 376 440 312), lower := (rows 7 42 69 137 22 32 64 128 256), losses := [] }

theorem u5926 : Upper (D 5) (R 5) [6,40,65,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5926
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5927 : PairBound 9 := { available := 308, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 137 26 308 372 436 308), lower := (rows 7 42 69 137 26 32 64 128 256), losses := [] }

theorem u5927 : Upper (D 5) (R 5) [6,40,65,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5927
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5928 : PairBound 9 := { available := 306, camps := [{ cop := 4, region := 290, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 137 28 306 370 434 306), lower := (rows 7 42 69 137 28 32 64 128 256), losses := [] }

theorem u5928 : Upper (D 5) (R 5) [6,40,65,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5928
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5929 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 137 50 316 348 412 284), lower := (rows 7 42 69 137 50 32 64 128 256), losses := [] }

theorem u5929 : Upper (D 5) (R 5) [6,40,65,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5929
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5930 : Route 9 := (fun mask => (mask,id))

def c5930 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5930 : Upper (D 5) (R 5) [6,40,65,129,36] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,36] 13 (by decide) (choices 1) [2,8,16,256] r5930 c5930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2419
  · exact u2420
  · exact u2421
  · exact u2422

def b5931 : PairBound 9 := { available := 278, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 137 56 310 342 406 278), lower := (rows 7 42 69 137 56 32 64 128 256), losses := [] }

theorem u5931 : Upper (D 5) (R 5) [6,40,65,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5931
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5932 : Route 9 := (fun mask => (mask,id))

def c5932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5932 : Upper (D 5) (R 5) [6,40,65,129,258] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,258] 13 (by decide) (choices 1) [4,8,16] r5932 c5932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2423
  · exact u2424
  · exact u2425

def r5933 : Route 9 := (fun mask => (mask,id))

def c5933 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5933 : Upper (D 5) (R 5) [6,40,65,129,260] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,260] 13 (by decide) (choices 1) [2,8,16] r5933 c5933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2426
  · exact u2427
  · exact u2428

def r5934 : Route 9 := (fun mask => (mask,id))

def c5934 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5934 : Upper (D 5) (R 5) [6,40,65,129,264] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,264] 13 (by decide) (choices 1) [2,4,16] r5934 c5934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2429
  · exact u2430
  · exact u2431

def r5935 : Route 9 := (fun mask => (mask,id))

def c5935 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5935 : Upper (D 5) (R 5) [6,40,65,129,288] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,288] 13 (by decide) (choices 1) [2,4,8,16] r5935 c5935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2432
  · exact u2433
  · exact u2434
  · exact u2435

def b5936 : PairBound 9 := { available := 312, camps := [{ cop := 4, region := 426, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 138 21 312 376 440 312), lower := (rows 7 42 69 138 21 32 64 128 256), losses := [] }

theorem u5936 : Upper (D 5) (R 5) [6,40,65,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5936
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5937 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 356, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 42 69 138 25 308 372 436 308), lower := (rows 7 42 69 138 25 32 64 128 256), losses := [] }

theorem u5937 : Upper (D 5) (R 5) [6,40,65,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5937
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5938 : Route 9 := (fun mask => (mask,id))

def c5938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5938 : Upper (D 5) (R 5) [6,40,65,130,12] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,12] 13 (by decide) (choices 1) [1,16,256] r5938 c5938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2436
  · exact u2437
  · exact u2438

def r5939 : Route 9 := (fun mask => (mask,id))

def c5939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5939 : Upper (D 5) (R 5) [6,40,65,130,33] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,33] 13 (by decide) (choices 1) [4,8,16,256] r5939 c5939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2439
  · exact u2440
  · exact u2441
  · exact u2442

#print axioms u5939
end Delivery.IrregularNine14.P05
