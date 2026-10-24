import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0027
import IrregularNine14P00C0028

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2880 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 113 14 52 328 147 163 195 131 387), lower := (rows 113 14 52 328 16 32 64 128 256), losses := [] }

theorem u2880 : Upper (D 0) (R 0) [112,12,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2880
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2881 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 113 14 52 392 211 227 195 195 451), lower := (rows 113 14 52 392 16 32 64 128 256), losses := [] }

theorem u2881 : Upper (D 0) (R 0) [112,12,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2881
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2882 : PairBound 9 := { available := 370, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 133 137 370 370 370 498 370), lower := (rows 113 14 133 137 16 32 64 128 256), losses := [] }

theorem u2882 : Upper (D 0) (R 0) [112,12,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2882
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2883 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 113 14 133 138 369 369 369 497 369), lower := (rows 113 14 133 138 16 32 64 128 256), losses := [] }

theorem u2883 : Upper (D 0) (R 0) [112,12,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2883
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2884 : PairBound 9 := { available := 355, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 133 152 371 355 355 483 355), lower := (rows 113 14 133 152 16 32 64 128 256), losses := [] }

theorem u2884 : Upper (D 0) (R 0) [112,12,129,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2884
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2885 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2885 : Upper (D 0) (R 0) [112,12,129,257] 13 := by
  apply FastRouting.sound _ _ [112,12,129,257] 13 (by decide) (choices 1) [2,32,128] r2885 c2885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1656
  · exact u1657
  · exact u1658

def r2886 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2886 : Upper (D 0) (R 0) [112,12,129,258] 13 := by
  apply FastRouting.sound _ _ [112,12,129,258] 13 (by decide) (choices 1) [1,32,128] r2886 c2886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1659
  · exact u1660
  · exact u1661

def r2887 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2887 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2887 : Upper (D 0) (R 0) [112,12,129,272] 13 := by
  apply FastRouting.sound _ _ [112,12,129,272] 13 (by decide) (choices 1) [1,2,32,128] r2887 c2887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1662
  · exact u1663
  · exact u1664
  · exact u1665

def b2888 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 133 392 115 115 115 243 371), lower := (rows 113 14 133 392 16 32 64 128 256), losses := [] }

theorem u2888 : Upper (D 0) (R 0) [112,12,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2888
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2889 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 113 14 134 152 369 353 353 481 353), lower := (rows 113 14 134 152 16 32 64 128 256), losses := [] }

theorem u2889 : Upper (D 0) (R 0) [112,12,130,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2889
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2890 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2890 : Upper (D 0) (R 0) [112,12,130,257] 13 := by
  apply FastRouting.sound _ _ [112,12,130,257] 13 (by decide) (choices 1) [1,32,128] r2890 c2890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1666
  · exact u1667
  · exact u1668

def r2891 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2891 : Upper (D 0) (R 0) [112,12,130,272] 13 := by
  apply FastRouting.sound _ _ [112,12,130,272] 13 (by decide) (choices 1) [1,32,128] r2891 c2891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1669
  · exact u1670
  · exact u1671

def b2892 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 113 14 134 392 113 113 113 241 369), lower := (rows 113 14 134 392 16 32 64 128 256), losses := [] }

theorem u2892 : Upper (D 0) (R 0) [112,12,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2892
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2893 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 148 168 339 355 323 451 323), lower := (rows 113 14 148 168 16 32 64 128 256), losses := [] }

theorem u2893 : Upper (D 0) (R 0) [112,12,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2893
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2894 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2894 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2894 : Upper (D 0) (R 0) [112,12,144,257] 13 := by
  apply FastRouting.sound _ _ [112,12,144,257] 13 (by decide) (choices 1) [1,2,32,128] r2894 c2894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1672
  · exact u1673
  · exact u1674
  · exact u1675

def r2895 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2895 : Upper (D 0) (R 0) [112,12,144,258] 13 := by
  apply FastRouting.sound _ _ [112,12,144,258] 13 (by decide) (choices 1) [1,32,128] r2895 c2895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1676
  · exact u1677
  · exact u1678

def r2896 : Route 9 := (fun mask => (mask,id))

def c2896 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2896 : Upper (D 0) (R 0) [112,12,144,288] 13 := by
  apply FastRouting.sound _ _ [112,12,144,288] 13 (by decide) (choices 1) [1,2,64,128] r2896 c2896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1679
  · exact u1680
  · exact u1681
  · exact u1682

def b2897 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 148 392 115 99 99 227 355), lower := (rows 113 14 148 392 16 32 64 128 256), losses := [] }

theorem u2897 : Upper (D 0) (R 0) [112,12,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2897
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2898 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 113 19 38 76 409 425 457 393 393), lower := (rows 113 19 38 76 16 32 64 128 256), losses := [] }

theorem u2898 : Upper (D 0) (R 0) [112,17,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2898
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2899 : PairBound 9 := { available := 460, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 19 38 137 476 492 460 460 460), lower := (rows 113 19 38 137 16 32 64 128 256), losses := [] }

theorem u2899 : Upper (D 0) (R 0) [112,17,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2899
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2900 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 19 38 140 473 489 457 457 457), lower := (rows 113 19 38 140 16 32 64 128 256), losses := [] }

theorem u2900 : Upper (D 0) (R 0) [112,17,34,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2900
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2901 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 19 38 200 413 429 461 397 397), lower := (rows 113 19 38 200 16 32 64 128 256), losses := [] }

theorem u2901 : Upper (D 0) (R 0) [112,17,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2901
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2902 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 19 38 265 220 236 204 204 460), lower := (rows 113 19 38 265 16 32 64 128 256), losses := [] }

theorem u2902 : Upper (D 0) (R 0) [112,17,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2902
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2903 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 19 38 268 217 233 201 201 457), lower := (rows 113 19 38 268 16 32 64 128 256), losses := [] }

theorem u2903 : Upper (D 0) (R 0) [112,17,34,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2903
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2904 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 19 38 328 157 173 205 141 397), lower := (rows 113 19 38 328 16 32 64 128 256), losses := [] }

theorem u2904 : Upper (D 0) (R 0) [112,17,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2904
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2905 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 19 38 392 221 237 205 205 461), lower := (rows 113 19 38 392 16 32 64 128 256), losses := [] }

theorem u2905 : Upper (D 0) (R 0) [112,17,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2905
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2906 : PairBound 9 := { available := 454, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 44 137 470 486 454 454 454), lower := (rows 113 19 44 137 16 32 64 128 256), losses := [] }

theorem u2906 : Upper (D 0) (R 0) [112,17,40,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2906
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2907 : PairBound 9 := { available := 453, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 44 138 469 485 453 453 453), lower := (rows 113 19 44 138 16 32 64 128 256), losses := [] }

theorem u2907 : Upper (D 0) (R 0) [112,17,40,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2907
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2908 : PairBound 9 := { available := 391, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 44 200 407 423 455 391 391), lower := (rows 113 19 44 200 16 32 64 128 256), losses := [] }

theorem u2908 : Upper (D 0) (R 0) [112,17,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2908
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2909 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 44 265 214 230 198 198 454), lower := (rows 113 19 44 265 16 32 64 128 256), losses := [] }

theorem u2909 : Upper (D 0) (R 0) [112,17,40,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2909
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2910 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 44 266 213 229 197 197 453), lower := (rows 113 19 44 266 16 32 64 128 256), losses := [] }

theorem u2910 : Upper (D 0) (R 0) [112,17,40,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2910
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2911 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 44 328 151 167 199 135 391), lower := (rows 113 19 44 328 16 32 64 128 256), losses := [] }

theorem u2911 : Upper (D 0) (R 0) [112,17,40,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2911
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2912 : PairBound 9 := { available := 199, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 44 392 215 231 199 199 455), lower := (rows 113 19 44 392 16 32 64 128 256), losses := [] }

theorem u2912 : Upper (D 0) (R 0) [112,17,40,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2912
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2913 : PairBound 9 := { available := 364, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 133 138 380 364 364 492 364), lower := (rows 113 19 133 138 16 32 64 128 256), losses := [] }

theorem u2913 : Upper (D 0) (R 0) [112,17,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2913
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2914 : PairBound 9 := { available := 334, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 133 168 350 366 334 462 334), lower := (rows 113 19 133 168 16 32 64 128 256), losses := [] }

theorem u2914 : Upper (D 0) (R 0) [112,17,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2914
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2915 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 133 266 252 236 236 236 492), lower := (rows 113 19 133 266 16 32 64 128 256), losses := [] }

theorem u2915 : Upper (D 0) (R 0) [112,17,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2915
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2916 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 133 268 250 234 234 234 490), lower := (rows 113 19 133 268 16 32 64 128 256), losses := [] }

theorem u2916 : Upper (D 0) (R 0) [112,17,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2916
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2917 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 133 296 222 238 206 206 462), lower := (rows 113 19 133 296 16 32 64 128 256), losses := [] }

theorem u2917 : Upper (D 0) (R 0) [112,17,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2917
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2918 : PairBound 9 := { available := 110, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 133 392 126 110 110 238 366), lower := (rows 113 19 133 392 16 32 64 128 256), losses := [] }

theorem u2918 : Upper (D 0) (R 0) [112,17,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2918
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2919 : PairBound 9 := { available := 333, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 134 168 349 365 333 461 333), lower := (rows 113 19 134 168 16 32 64 128 256), losses := [] }

theorem u2919 : Upper (D 0) (R 0) [112,17,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2919
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2920 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 134 265 252 236 236 236 492), lower := (rows 113 19 134 265 16 32 64 128 256), losses := [] }

theorem u2920 : Upper (D 0) (R 0) [112,17,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2920
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2921 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 134 268 249 233 233 233 489), lower := (rows 113 19 134 268 16 32 64 128 256), losses := [] }

theorem u2921 : Upper (D 0) (R 0) [112,17,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2921
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2922 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 134 296 221 237 205 205 461), lower := (rows 113 19 134 296 16 32 64 128 256), losses := [] }

theorem u2922 : Upper (D 0) (R 0) [112,17,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2922
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2923 : PairBound 9 := { available := 109, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 134 392 125 109 109 237 365), lower := (rows 113 19 134 392 16 32 64 128 256), losses := [] }

theorem u2923 : Upper (D 0) (R 0) [112,17,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2923
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2924 : PairBound 9 := { available := 230, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 140 265 246 230 230 230 486), lower := (rows 113 19 140 265 16 32 64 128 256), losses := [] }

theorem u2924 : Upper (D 0) (R 0) [112,17,136,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2924
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2925 : PairBound 9 := { available := 229, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 140 266 245 229 229 229 485), lower := (rows 113 19 140 266 16 32 64 128 256), losses := [] }

theorem u2925 : Upper (D 0) (R 0) [112,17,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2925
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2926 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 140 268 243 227 227 227 483), lower := (rows 113 19 140 268 16 32 64 128 256), losses := [] }

theorem u2926 : Upper (D 0) (R 0) [112,17,136,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2926
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2927 : PairBound 9 := { available := 199, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 140 296 215 231 199 199 455), lower := (rows 113 19 140 296 16 32 64 128 256), losses := [] }

theorem u2927 : Upper (D 0) (R 0) [112,17,136,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2927
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2928 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 164 200 287 303 335 399 271), lower := (rows 113 19 164 200 16 32 64 128 256), losses := [] }

theorem u2928 : Upper (D 0) (R 0) [112,17,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2928
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2929 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 164 265 222 238 206 206 462), lower := (rows 113 19 164 265 16 32 64 128 256), losses := [] }

theorem u2929 : Upper (D 0) (R 0) [112,17,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2929
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2930 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 164 266 221 237 205 205 461), lower := (rows 113 19 164 266 16 32 64 128 256), losses := [] }

theorem u2930 : Upper (D 0) (R 0) [112,17,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2930
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2931 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 164 268 219 235 203 203 459), lower := (rows 113 19 164 268 16 32 64 128 256), losses := [] }

theorem u2931 : Upper (D 0) (R 0) [112,17,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2931
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2932 : PairBound 9 := { available := 143, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 164 328 159 175 207 143 399), lower := (rows 113 19 164 328 16 32 64 128 256), losses := [] }

theorem u2932 : Upper (D 0) (R 0) [112,17,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2932
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2933 : PairBound 9 := { available := 79, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 164 392 95 111 79 207 335), lower := (rows 113 19 164 392 16 32 64 128 256), losses := [] }

theorem u2933 : Upper (D 0) (R 0) [112,17,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2933
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2934 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 38 137 473 489 457 457 457), lower := (rows 113 22 38 137 16 32 64 128 256), losses := [] }

theorem u2934 : Upper (D 0) (R 0) [112,20,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2934
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2935 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 38 200 409 425 457 393 393), lower := (rows 113 22 38 200 16 32 64 128 256), losses := [] }

theorem u2935 : Upper (D 0) (R 0) [112,20,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2935
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2936 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 38 265 217 233 201 201 457), lower := (rows 113 22 38 265 16 32 64 128 256), losses := [] }

theorem u2936 : Upper (D 0) (R 0) [112,20,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2936
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2937 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 38 328 153 169 201 137 393), lower := (rows 113 22 38 328 16 32 64 128 256), losses := [] }

theorem u2937 : Upper (D 0) (R 0) [112,20,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2937
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2938 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 38 392 217 233 201 201 457), lower := (rows 113 22 38 392 16 32 64 128 256), losses := [] }

theorem u2938 : Upper (D 0) (R 0) [112,20,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2938
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2939 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 44 74 401 417 449 385 385), lower := (rows 113 22 44 74 16 32 64 128 256), losses := [] }

theorem u2939 : Upper (D 0) (R 0) [112,20,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2939
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u2939
end Delivery.IrregularNine14.P00
