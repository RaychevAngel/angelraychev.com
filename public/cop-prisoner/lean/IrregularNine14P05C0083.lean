import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0029

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4980 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 49 70 140 296 21 34 75 139 267), lower := (rows 49 70 140 296 21 34 64 128 256), losses := [] }

theorem u4980 : Upper (D 5) (R 5) [48,68,136,288,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4980
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4981 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 49 70 140 296 21 40 67 131 259), lower := (rows 49 70 140 296 21 40 64 128 256), losses := [] }

theorem u4981 : Upper (D 5) (R 5) [48,68,136,288,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4981
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4982 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 70 140 296 26 33 71 135 263), lower := (rows 49 70 140 296 26 33 64 128 256), losses := [] }

theorem u4982 : Upper (D 5) (R 5) [48,68,136,288,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4982
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4983 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 49 70 140 296 26 34 69 133 261), lower := (rows 49 70 140 296 26 34 64 128 256), losses := [] }

theorem u4983 : Upper (D 5) (R 5) [48,68,136,288,10,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4983
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4984 : PairBound 9 := { available := 3, camps := [], pairs := [(0,1),(0,3)], upper := (rows 49 70 140 296 26 36 67 131 259), lower := (rows 49 70 140 296 26 36 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 8 16 38 64 128 256), good := (rows 49 100 172 296 57 36 64 128 256) },{ target := 3, region := (rows 17 2 4 0 16 38 80 144 272), good := (rows 497 102 164 288 499 36 64 128 256) }] }

theorem u4984 : Upper (D 5) (R 5) [48,68,136,288,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4984
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4985 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 49 70 164 268 19 33 74 138 266), lower := (rows 49 70 164 268 19 33 64 128 256), losses := [] }

theorem u4985 : Upper (D 5) (R 5) [48,68,160,260,3,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4985
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4986 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 49 70 164 268 19 34 73 137 265), lower := (rows 49 70 164 268 19 34 64 128 256), losses := [] }

theorem u4986 : Upper (D 5) (R 5) [48,68,160,260,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4986
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4987 : Route 9 := (fun mask => (mask,id))

def c4987 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4987 : Upper (D 5) (R 5) [48,68,160,260,3,8] 13 := by
  apply FastRouting.sound _ _ [48,68,160,260,3,8] 13 (by decide) (choices 1) [1,2,8] r4987 c4987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1762
  · exact u1763
  · exact u1764

def b4988 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 33, targets := 10 }], pairs := [(0,1),(0,3)], upper := (rows 49 70 164 268 26 33 75 139 267), lower := (rows 49 70 164 268 26 33 64 128 256), losses := [] }

theorem u4988 : Upper (D 5) (R 5) [48,68,160,260,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4988
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4989 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 49 70 164 268 26 34 73 137 265), lower := (rows 49 70 164 268 26 34 64 128 256), losses := [] }

theorem u4989 : Upper (D 5) (R 5) [48,68,160,260,10,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4989
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4990 : PairBound 9 := { available := 396, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 52 104 19 428 460 396 396), lower := (rows 7 11 52 104 19 32 64 128 256), losses := [] }

theorem u4990 : Upper (D 5) (R 5) [6,9,48,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4990
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4991 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 11 52 104 21 426 458 394 394), lower := (rows 7 11 52 104 21 32 64 128 256), losses := [] }

theorem u4991 : Upper (D 5) (R 5) [6,9,48,96,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4991
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4992 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 490, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 52 104 22 425 457 393 393), lower := (rows 7 11 52 104 22 32 64 128 256), losses := [] }

theorem u4992 : Upper (D 5) (R 5) [6,9,48,96,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4992
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4993 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 11 52 104 25 422 454 390 390), lower := (rows 7 11 52 104 25 32 64 128 256), losses := [] }

theorem u4993 : Upper (D 5) (R 5) [6,9,48,96,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4993
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4994 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 52 104 26 421 453 389 389), lower := (rows 7 11 52 104 26 32 64 128 256), losses := [] }

theorem u4994 : Upper (D 5) (R 5) [6,9,48,96,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4994
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4995 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 20, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 52 104 28 419 451 387 387), lower := (rows 7 11 52 104 28 32 64 128 256), losses := [] }

theorem u4995 : Upper (D 5) (R 5) [6,9,48,96,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4995
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4996 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 360, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 11 52 104 145 302 334 398 270), lower := (rows 7 11 52 104 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 60 104 508 32 64 128 256) }] }

theorem u4996 : Upper (D 5) (R 5) [6,9,48,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4996
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4997 : Route 9 := (fun mask => (mask,id))

def c4997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u4997 : Upper (D 5) (R 5) [6,9,48,96,130] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,130] 13 (by decide) (choices 1) [1,4,8,256] r4997 c4997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1765
  · exact u1766
  · exact u1767
  · exact u1768

def b4998 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 52 104 148 299 331 395 267), lower := (rows 7 11 52 104 148 32 64 128 256), losses := [] }

theorem u4998 : Upper (D 5) (R 5) [6,9,48,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4998
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4999 : Route 9 := (fun mask => (mask,id))

def c4999 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u4999 : Upper (D 5) (R 5) [6,9,48,96,136] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,136] 13 (by decide) (choices 1) [1,2,4,256] r4999 c4999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1769
  · exact u1770
  · exact u1771
  · exact u1772

def r5000 : Route 9 := (fun mask => (mask,id))

def c5000 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5000 : Upper (D 5) (R 5) [6,9,48,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,384] 13 (by decide) (choices 1) [1,2,4,8] r5000 c5000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1773
  · exact u1774
  · exact u1775
  · exact u1776

def b5001 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 52 200 19 300 364 428 300), lower := (rows 7 11 52 200 19 32 64 128 256), losses := [] }

theorem u5001 : Upper (D 5) (R 5) [6,9,48,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5001
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5002 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 11 52 200 21 298 362 426 298), lower := (rows 7 11 52 200 21 32 64 128 256), losses := [] }

theorem u5002 : Upper (D 5) (R 5) [6,9,48,192,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5002
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5003 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 490, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 52 200 22 297 361 425 297), lower := (rows 7 11 52 200 22 32 64 128 256), losses := [] }

theorem u5003 : Upper (D 5) (R 5) [6,9,48,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5003
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5004 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 11 52 200 25 294 358 422 294), lower := (rows 7 11 52 200 25 32 64 128 256), losses := [] }

theorem u5004 : Upper (D 5) (R 5) [6,9,48,192,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5004
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5005 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 52 200 26 293 357 421 293), lower := (rows 7 11 52 200 26 32 64 128 256), losses := [] }

theorem u5005 : Upper (D 5) (R 5) [6,9,48,192,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5005
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5006 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 490, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 52 200 28 291 355 419 291), lower := (rows 7 11 52 200 28 32 64 128 256), losses := [] }

theorem u5006 : Upper (D 5) (R 5) [6,9,48,192,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5006
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5007 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 52 200 49 302 334 398 270), lower := (rows 7 11 52 200 49 32 64 128 256), losses := [] }

theorem u5007 : Upper (D 5) (R 5) [6,9,48,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5007
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5008 : PairBound 9 := { available := 269, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 52 200 50 301 333 397 269), lower := (rows 7 11 52 200 50 32 64 128 256), losses := [] }

theorem u5008 : Upper (D 5) (R 5) [6,9,48,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5008
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5009 : PairBound 9 := { available := 267, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 52 200 52 299 331 395 267), lower := (rows 7 11 52 200 52 32 64 128 256), losses := [] }

theorem u5009 : Upper (D 5) (R 5) [6,9,48,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5009
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5010 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 52 200 56 295 327 391 263), lower := (rows 7 11 52 200 56 32 64 128 256), losses := [] }

theorem u5010 : Upper (D 5) (R 5) [6,9,48,192,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5010
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5011 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 232, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 11 52 200 273 46 110 174 302), lower := (rows 7 11 52 200 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 60 200 508 32 64 128 256) }] }

theorem u5011 : Upper (D 5) (R 5) [6,9,48,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5011
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5012 : Route 9 := (fun mask => (mask,id))

def c5012 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5012 : Upper (D 5) (R 5) [6,9,48,192,258] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,258] 13 (by decide) (choices 1) [1,4,8] r5012 c5012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1777
  · exact u1778
  · exact u1779

def b5013 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 52 200 276 43 107 171 299), lower := (rows 7 11 52 200 276 32 64 128 256), losses := [] }

theorem u5013 : Upper (D 5) (R 5) [6,9,48,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5013
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5014 : Route 9 := (fun mask => (mask,id))

def c5014 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5014 : Upper (D 5) (R 5) [6,9,48,192,264] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,264] 13 (by decide) (choices 1) [1,2,4] r5014 c5014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1780
  · exact u1781
  · exact u1782

def b5015 : PairBound 9 := { available := 15, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 52 200 304 47 79 143 271), lower := (rows 7 11 52 200 304 32 64 128 256), losses := [] }

theorem u5015 : Upper (D 5) (R 5) [6,9,48,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5015
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5016 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 84 168 19 300 364 428 300), lower := (rows 7 11 84 168 19 32 64 128 256), losses := [] }

theorem u5016 : Upper (D 5) (R 5) [6,9,80,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5016
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5017 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 11 84 168 21 298 362 426 298), lower := (rows 7 11 84 168 21 32 64 128 256), losses := [] }

theorem u5017 : Upper (D 5) (R 5) [6,9,80,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5017
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5018 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 84 168 22 297 361 425 297), lower := (rows 7 11 84 168 22 32 64 128 256), losses := [] }

theorem u5018 : Upper (D 5) (R 5) [6,9,80,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5018
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5019 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 11 84 168 25 294 358 422 294), lower := (rows 7 11 84 168 25 32 64 128 256), losses := [] }

theorem u5019 : Upper (D 5) (R 5) [6,9,80,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5019
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5020 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 84 168 26 293 357 421 293), lower := (rows 7 11 84 168 26 32 64 128 256), losses := [] }

theorem u5020 : Upper (D 5) (R 5) [6,9,80,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5020
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5021 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 84 168 28 291 355 419 291), lower := (rows 7 11 84 168 28 32 64 128 256), losses := [] }

theorem u5021 : Upper (D 5) (R 5) [6,9,80,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5021
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5022 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 424, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 11 84 168 49 302 334 398 270), lower := (rows 7 11 84 168 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 92 168 508 32 64 128 256) }] }

theorem u5022 : Upper (D 5) (R 5) [6,9,80,160,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5022
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5023 : Route 9 := (fun mask => (mask,id))

def c5023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5023 : Upper (D 5) (R 5) [6,9,80,160,34] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,34] 13 (by decide) (choices 1) [1,4,8,256] r5023 c5023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1783
  · exact u1784
  · exact u1785
  · exact u1786

def b5024 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 84 168 52 299 331 395 267), lower := (rows 7 11 84 168 52 32 64 128 256), losses := [] }

theorem u5024 : Upper (D 5) (R 5) [6,9,80,160,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5024
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5025 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 84 168 56 295 327 391 263), lower := (rows 7 11 84 168 56 32 64 128 256), losses := [] }

theorem u5025 : Upper (D 5) (R 5) [6,9,80,160,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5025
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5026 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 168, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 11 84 168 273 46 110 174 302), lower := (rows 7 11 84 168 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 92 168 508 32 64 128 256) }] }

theorem u5026 : Upper (D 5) (R 5) [6,9,80,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5026
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5027 : Route 9 := (fun mask => (mask,id))

def c5027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5027 : Upper (D 5) (R 5) [6,9,80,160,258] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,258] 13 (by decide) (choices 1) [1,4,8] r5027 c5027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1787
  · exact u1788
  · exact u1789

def b5028 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 170, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 84 168 276 43 107 171 299), lower := (rows 7 11 84 168 276 32 64 128 256), losses := [] }

theorem u5028 : Upper (D 5) (R 5) [6,9,80,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5028
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5029 : Route 9 := (fun mask => (mask,id))

def c5029 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5029 : Upper (D 5) (R 5) [6,9,80,160,264] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,264] 13 (by decide) (choices 1) [1,2,4] r5029 c5029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1790
  · exact u1791
  · exact u1792

def r5030 : Route 9 := (fun mask => (mask,id))

def c5030 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5030 : Upper (D 5) (R 5) [6,9,80,160,288] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,288] 13 (by decide) (choices 1) [1,2,4,8] r5030 c5030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1793
  · exact u1794
  · exact u1795
  · exact u1796

def b5031 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 84 392 19 44 108 172 300), lower := (rows 7 11 84 392 19 32 64 128 256), losses := [] }

theorem u5031 : Upper (D 5) (R 5) [6,9,80,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5031
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5032 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 11 84 392 21 42 106 170 298), lower := (rows 7 11 84 392 21 32 64 128 256), losses := [] }

theorem u5032 : Upper (D 5) (R 5) [6,9,80,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5032
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5033 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 84 392 22 41 105 169 297), lower := (rows 7 11 84 392 22 32 64 128 256), losses := [] }

theorem u5033 : Upper (D 5) (R 5) [6,9,80,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5033
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5034 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 11 84 392 25 38 102 166 294), lower := (rows 7 11 84 392 25 32 64 128 256), losses := [] }

theorem u5034 : Upper (D 5) (R 5) [6,9,80,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5034
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5035 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 84 392 26 37 101 165 293), lower := (rows 7 11 84 392 26 32 64 128 256), losses := [] }

theorem u5035 : Upper (D 5) (R 5) [6,9,80,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5035
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5036 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 84 392 28 35 99 163 291), lower := (rows 7 11 84 392 28 32 64 128 256), losses := [] }

theorem u5036 : Upper (D 5) (R 5) [6,9,80,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5036
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5037 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 424, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 11 84 392 49 46 110 174 302), lower := (rows 7 11 84 392 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 92 392 508 32 64 128 256) }] }

theorem u5037 : Upper (D 5) (R 5) [6,9,80,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5037
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5038 : Route 9 := (fun mask => (mask,id))

def c5038 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5038 : Upper (D 5) (R 5) [6,9,80,384,34] 13 := by
  apply FastRouting.sound _ _ [6,9,80,384,34] 13 (by decide) (choices 1) [1,4,8] r5038 c5038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1797
  · exact u1798
  · exact u1799

def b5039 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 84 392 52 43 107 171 299), lower := (rows 7 11 84 392 52 32 64 128 256), losses := [] }

theorem u5039 : Upper (D 5) (R 5) [6,9,80,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5039
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5039
end Delivery.IrregularNine14.P05
