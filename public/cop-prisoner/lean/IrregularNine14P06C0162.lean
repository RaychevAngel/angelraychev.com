import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0018

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9720 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 140 74 112 48 325 389 261), lower := (rows 7 35 140 74 112 48 64 128 256), losses := [] }

theorem u9720 : Upper (D 6) (R 6) [6,33,136,66,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9720
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9721 : Route 9 := (fun mask => (mask,id))

def c9721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9721 : Upper (D 6) (R 6) [6,33,136,66,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,136,66,96,256] 13 (by decide) (choices 1) [1,4,16] r9721 c9721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1088
  · exact u1089
  · exact u1090

def b9722 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 74 273 36 112 240 368), lower := (rows 7 35 140 74 273 36 64 128 256), losses := [] }

theorem u9722 : Upper (D 6) (R 6) [6,33,136,66,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9722
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9723 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 140 74 273 48 100 228 356), lower := (rows 7 35 140 74 273 48 64 128 256), losses := [] }

theorem u9723 : Upper (D 6) (R 6) [6,33,136,66,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9723
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9724 : Route 9 := (fun mask => (mask,id))

def c9724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9724 : Upper (D 6) (R 6) [6,33,136,66,257,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,66,257,64] 13 (by decide) (choices 1) [4,16,32] r9724 c9724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1091
  · exact u1092
  · exact u1093

def b9725 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 74 276 33 112 240 368), lower := (rows 7 35 140 74 276 33 64 128 256), losses := [] }

theorem u9725 : Upper (D 6) (R 6) [6,33,136,66,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9725
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9726 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 74 276 48 97 225 353), lower := (rows 7 35 140 74 276 48 64 128 256), losses := [] }

theorem u9726 : Upper (D 6) (R 6) [6,33,136,66,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9726
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9727 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 368, targets := 2 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 7 35 140 74 276 96 113 177 305), lower := (rows 7 35 140 74 276 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 107 67 131 259), good := (rows 501 497 188 508 276 96 96 128 256) },{ target := 6, region := (rows 9 2 12 8 25 32 0 130 258), good := (rows 407 435 157 415 276 32 0 128 256) }] }

theorem u9727 : Upper (D 6) (R 6) [6,33,136,66,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9727
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9728 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 74 304 33 84 212 340), lower := (rows 7 35 140 74 304 33 64 128 256), losses := [] }

theorem u9728 : Upper (D 6) (R 6) [6,33,136,66,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9728
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9729 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 74 304 36 81 209 337), lower := (rows 7 35 140 74 304 36 64 128 256), losses := [] }

theorem u9729 : Upper (D 6) (R 6) [6,33,136,66,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9729
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9730 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 140 74 304 48 69 197 325), lower := (rows 7 35 140 74 304 48 64 128 256), losses := [] }

theorem u9730 : Upper (D 6) (R 6) [6,33,136,66,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9730
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9731 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 368, targets := 2 }], pairs := [(0,6),(2,6),(4,1)], upper := (rows 7 35 140 74 304 96 85 149 277), lower := (rows 7 35 140 74 304 96 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 18 32 0 137 265), good := (rows 407 435 397 415 304 32 0 128 256) }] }

theorem u9731 : Upper (D 6) (R 6) [6,33,136,66,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9731
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9732 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 74 336 33 116 180 308), lower := (rows 7 35 140 74 336 33 64 128 256), losses := [] }

theorem u9732 : Upper (D 6) (R 6) [6,33,136,66,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9732
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9733 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 74 336 36 113 177 305), lower := (rows 7 35 140 74 336 36 64 128 256), losses := [] }

theorem u9733 : Upper (D 6) (R 6) [6,33,136,66,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9733
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9734 : Route 9 := (fun mask => (mask,id))

def c9734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9734 : Upper (D 6) (R 6) [6,33,136,66,320,16] 13 := by
  apply FastRouting.sound _ _ [6,33,136,66,320,16] 13 (by decide) (choices 1) [1,4,32] r9734 c9734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1094
  · exact u1095
  · exact u1096

def b9735 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 76 82 33 368 432 304), lower := (rows 7 35 140 76 82 33 64 128 256), losses := [] }

theorem u9735 : Upper (D 6) (R 6) [6,33,136,68,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9735
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9736 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 140 76 82 48 353 417 289), lower := (rows 7 35 140 76 82 48 64 128 256), losses := [] }

theorem u9736 : Upper (D 6) (R 6) [6,33,136,68,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9736
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9737 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 140 76 82 288 113 177 305), lower := (rows 7 35 140 76 82 288 64 128 256), losses := [] }

theorem u9737 : Upper (D 6) (R 6) [6,33,136,68,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9737
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9738 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 76 112 33 338 402 274), lower := (rows 7 35 140 76 112 33 64 128 256), losses := [] }

theorem u9738 : Upper (D 6) (R 6) [6,33,136,68,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9738
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9739 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 76 112 34 337 401 273), lower := (rows 7 35 140 76 112 34 64 128 256), losses := [] }

theorem u9739 : Upper (D 6) (R 6) [6,33,136,68,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9739
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9740 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 140 76 112 48 323 387 259), lower := (rows 7 35 140 76 112 48 64 128 256), losses := [] }

theorem u9740 : Upper (D 6) (R 6) [6,33,136,68,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9740
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9741 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 140 76 112 288 83 147 275), lower := (rows 7 35 140 76 112 288 64 128 256), losses := [] }

theorem u9741 : Upper (D 6) (R 6) [6,33,136,68,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9741
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9742 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 76 273 34 112 240 368), lower := (rows 7 35 140 76 273 34 64 128 256), losses := [] }

theorem u9742 : Upper (D 6) (R 6) [6,33,136,68,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9742
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9743 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 140 76 273 48 98 226 354), lower := (rows 7 35 140 76 273 48 64 128 256), losses := [] }

theorem u9743 : Upper (D 6) (R 6) [6,33,136,68,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9743
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9744 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 1, region := 272, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 140 76 273 96 114 178 306), lower := (rows 7 35 140 76 273 96 64 128 256), losses := [] }

theorem u9744 : Upper (D 6) (R 6) [6,33,136,68,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9744
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9745 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 76 274 33 112 240 368), lower := (rows 7 35 140 76 274 33 64 128 256), losses := [] }

theorem u9745 : Upper (D 6) (R 6) [6,33,136,68,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9745
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9746 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 140 76 274 48 97 225 353), lower := (rows 7 35 140 76 274 48 64 128 256), losses := [] }

theorem u9746 : Upper (D 6) (R 6) [6,33,136,68,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9746
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9747 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 1, region := 272, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 140 76 274 96 113 177 305), lower := (rows 7 35 140 76 274 96 64 128 256), losses := [] }

theorem u9747 : Upper (D 6) (R 6) [6,33,136,68,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9747
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9748 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 76 304 33 82 210 338), lower := (rows 7 35 140 76 304 33 64 128 256), losses := [] }

theorem u9748 : Upper (D 6) (R 6) [6,33,136,68,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9748
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9749 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 76 304 34 81 209 337), lower := (rows 7 35 140 76 304 34 64 128 256), losses := [] }

theorem u9749 : Upper (D 6) (R 6) [6,33,136,68,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9749
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9750 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 140 76 304 48 67 195 323), lower := (rows 7 35 140 76 304 48 64 128 256), losses := [] }

theorem u9750 : Upper (D 6) (R 6) [6,33,136,68,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9750
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9751 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 1, region := 272, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 140 76 304 96 83 147 275), lower := (rows 7 35 140 76 304 96 64 128 256), losses := [] }

theorem u9751 : Upper (D 6) (R 6) [6,33,136,68,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9751
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9752 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 76 336 33 114 178 306), lower := (rows 7 35 140 76 336 33 64 128 256), losses := [] }

theorem u9752 : Upper (D 6) (R 6) [6,33,136,68,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9752
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9753 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 76 336 34 113 177 305), lower := (rows 7 35 140 76 336 34 64 128 256), losses := [] }

theorem u9753 : Upper (D 6) (R 6) [6,33,136,68,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9753
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9754 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 140 76 336 48 99 163 291), lower := (rows 7 35 140 76 336 48 64 128 256), losses := [] }

theorem u9754 : Upper (D 6) (R 6) [6,33,136,68,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9754
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9755 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 88 273 34 100 228 356), lower := (rows 7 35 140 88 273 34 64 128 256), losses := [] }

theorem u9755 : Upper (D 6) (R 6) [6,33,136,80,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9755
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9756 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 88 273 36 98 226 354), lower := (rows 7 35 140 88 273 36 64 128 256), losses := [] }

theorem u9756 : Upper (D 6) (R 6) [6,33,136,80,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9756
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9757 : Route 9 := (fun mask => (mask,id))

def c9757 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9757 : Upper (D 6) (R 6) [6,33,136,80,257,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,80,257,64] 13 (by decide) (choices 1) [2,4,32] r9757 c9757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1097
  · exact u1098
  · exact u1099

def b9758 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 88 274 33 100 228 356), lower := (rows 7 35 140 88 274 33 64 128 256), losses := [] }

theorem u9758 : Upper (D 6) (R 6) [6,33,136,80,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9758
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9759 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 88 274 36 97 225 353), lower := (rows 7 35 140 88 274 36 64 128 256), losses := [] }

theorem u9759 : Upper (D 6) (R 6) [6,33,136,80,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9759
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9760 : Route 9 := (fun mask => (mask,id))

def c9760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9760 : Upper (D 6) (R 6) [6,33,136,80,258,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,80,258,64] 13 (by decide) (choices 1) [1,4,32] r9760 c9760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1100
  · exact u1101
  · exact u1102

def b9761 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 88 276 33 98 226 354), lower := (rows 7 35 140 88 276 33 64 128 256), losses := [] }

theorem u9761 : Upper (D 6) (R 6) [6,33,136,80,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9761
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9762 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 88 276 34 97 225 353), lower := (rows 7 35 140 88 276 34 64 128 256), losses := [] }

theorem u9762 : Upper (D 6) (R 6) [6,33,136,80,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9762
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9763 : Route 9 := (fun mask => (mask,id))

def c9763 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9763 : Upper (D 6) (R 6) [6,33,136,80,260,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,80,260,64] 13 (by decide) (choices 1) [1,2,32] r9763 c9763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1103
  · exact u1104
  · exact u1105

def b9764 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 88 304 33 70 198 326), lower := (rows 7 35 140 88 304 33 64 128 256), losses := [] }

theorem u9764 : Upper (D 6) (R 6) [6,33,136,80,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9764
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9765 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 88 304 34 69 197 325), lower := (rows 7 35 140 88 304 34 64 128 256), losses := [] }

theorem u9765 : Upper (D 6) (R 6) [6,33,136,80,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9765
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9766 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 88 304 36 67 195 323), lower := (rows 7 35 140 88 304 36 64 128 256), losses := [] }

theorem u9766 : Upper (D 6) (R 6) [6,33,136,80,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9766
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9767 : Route 9 := (fun mask => (mask,id))

def c9767 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9767 : Upper (D 6) (R 6) [6,33,136,80,288,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,80,288,64] 13 (by decide) (choices 1) [1,2,4] r9767 c9767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1106
  · exact u1107
  · exact u1108

def b9768 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 104 81 34 340 404 276), lower := (rows 7 35 140 104 81 34 64 128 256), losses := [] }

theorem u9768 : Upper (D 6) (R 6) [6,33,136,96,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9768
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9769 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 140 104 81 36 338 402 274), lower := (rows 7 35 140 104 81 36 64 128 256), losses := [] }

theorem u9769 : Upper (D 6) (R 6) [6,33,136,96,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9769
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9770 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 104 81 48 326 390 262), lower := (rows 7 35 140 104 81 48 64 128 256), losses := [] }

theorem u9770 : Upper (D 6) (R 6) [6,33,136,96,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9770
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9771 : Route 9 := (fun mask => (mask,id))

def c9771 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9771 : Upper (D 6) (R 6) [6,33,136,96,65,256] 13 := by
  apply FastRouting.sound _ _ [6,33,136,96,65,256] 13 (by decide) (choices 1) [2,4,16] r9771 c9771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1109
  · exact u1110
  · exact u1111

def b9772 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 104 82 33 340 404 276), lower := (rows 7 35 140 104 82 33 64 128 256), losses := [] }

theorem u9772 : Upper (D 6) (R 6) [6,33,136,96,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9772
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9773 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 140 104 82 36 337 401 273), lower := (rows 7 35 140 104 82 36 64 128 256), losses := [] }

theorem u9773 : Upper (D 6) (R 6) [6,33,136,96,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9773
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9774 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 104 82 48 325 389 261), lower := (rows 7 35 140 104 82 48 64 128 256), losses := [] }

theorem u9774 : Upper (D 6) (R 6) [6,33,136,96,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9774
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9775 : Route 9 := (fun mask => (mask,id))

def c9775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9775 : Upper (D 6) (R 6) [6,33,136,96,66,256] 13 := by
  apply FastRouting.sound _ _ [6,33,136,96,66,256] 13 (by decide) (choices 1) [1,4,16] r9775 c9775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1112
  · exact u1113
  · exact u1114

def b9776 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 104 273 34 84 212 340), lower := (rows 7 35 140 104 273 34 64 128 256), losses := [] }

theorem u9776 : Upper (D 6) (R 6) [6,33,136,96,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9776
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9777 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 140 104 273 36 82 210 338), lower := (rows 7 35 140 104 273 36 64 128 256), losses := [] }

theorem u9777 : Upper (D 6) (R 6) [6,33,136,96,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9777
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9778 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 140 104 273 48 70 198 326), lower := (rows 7 35 140 104 273 48 64 128 256), losses := [] }

theorem u9778 : Upper (D 6) (R 6) [6,33,136,96,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9778
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9779 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 104 273 96 86 150 278), lower := (rows 7 35 140 104 273 96 64 128 256), losses := [] }

theorem u9779 : Upper (D 6) (R 6) [6,33,136,96,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9779
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9779
end Delivery.IrregularNine14.P06
