import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0031

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r4980 : Route 9 := (fun mask => (mask,id))

def c4980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4980 : Upper (D 3) (R 3) [258,5,96,48,192] 13 := by
  apply FastRouting.sound _ _ [258,5,96,48,192] 13 (by decide) (choices 1) [1,8,128] r4980 c4980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1890
  · exact u1891
  · exact u1892

def b4981 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 104 145 185 217 153 409), lower := (rows 259 7 100 104 145 32 64 128 256), losses := [] }

theorem u4981 : Upper (D 3) (R 3) [258,5,96,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4981
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4982 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 104 152 177 209 145 401), lower := (rows 259 7 100 104 152 32 64 128 256), losses := [] }

theorem u4982 : Upper (D 3) (R 3) [258,5,96,96,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4982
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4983 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 7 100 137 145 120 120 248 376), lower := (rows 259 7 100 137 145 32 64 128 256), losses := [] }

theorem u4983 : Upper (D 3) (R 3) [258,5,96,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4983
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4984 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 7 100 137 152 113 113 241 369), lower := (rows 259 7 100 137 152 32 64 128 256), losses := [] }

theorem u4984 : Upper (D 3) (R 3) [258,5,96,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4984
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4985 : Route 9 := (fun mask => (mask,id))

def c4985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4985 : Upper (D 3) (R 3) [258,5,96,129,160] 13 := by
  apply FastRouting.sound _ _ [258,5,96,129,160] 13 (by decide) (choices 1) [1,8,16,64] r4985 c4985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1893
  · exact u1894
  · exact u1895
  · exact u1896

def b4986 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 152 152 97 97 225 353), lower := (rows 259 7 100 152 152 32 64 128 256), losses := [] }

theorem u4986 : Upper (D 3) (R 3) [258,5,96,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4986
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4987 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 152 176 105 73 201 329), lower := (rows 259 7 100 152 176 32 64 128 256), losses := [] }

theorem u4987 : Upper (D 3) (R 3) [258,5,96,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4987
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4988 : Route 9 := (fun mask => (mask,id))

def c4988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4988 : Upper (D 3) (R 3) [258,5,96,160,192] 13 := by
  apply FastRouting.sound _ _ [258,5,96,160,192] 13 (by decide) (choices 1) [1,8,16] r4988 c4988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1897
  · exact u1898
  · exact u1899

def b4989 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 22, targets := 64 }], pairs := [(1,6)], upper := (rows 259 14 21 41 49 224 192 192 448), lower := (rows 259 14 21 41 49 32 64 128 256), losses := [] }

theorem u4989 : Upper (D 3) (R 3) [258,12,17,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4989
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4990 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 14 21 41 81 224 224 224 480), lower := (rows 259 14 21 41 81 32 64 128 256), losses := [] }

theorem u4990 : Upper (D 3) (R 3) [258,12,17,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4990
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4991 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 14 21 41 112 225 193 193 449), lower := (rows 259 14 21 41 112 32 64 128 256), losses := [] }

theorem u4991 : Upper (D 3) (R 3) [258,12,17,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4991
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4992 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c4992 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4992 : Upper (D 3) (R 3) [258,12,17,33,192] 13 := by
  apply FastRouting.sound _ _ [258,12,17,33,192] 13 (by decide) (choices 1) [1,64] r4992 c4992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1900
  · exact u1901

def b4993 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 14 21 104 49 225 193 193 449), lower := (rows 259 14 21 104 49 32 64 128 256), losses := [] }

theorem u4993 : Upper (D 3) (R 3) [258,12,17,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4993
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4994 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 21 104 112 161 193 129 385), lower := (rows 259 14 21 104 112 32 64 128 256), losses := [] }

theorem u4994 : Upper (D 3) (R 3) [258,12,17,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4994
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4995 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 14 21 104 145 225 225 225 481), lower := (rows 259 14 21 104 145 32 64 128 256), losses := [] }

theorem u4995 : Upper (D 3) (R 3) [258,12,17,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4995
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4996 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 14 21 104 176 225 193 193 449), lower := (rows 259 14 21 104 176 32 64 128 256), losses := [] }

theorem u4996 : Upper (D 3) (R 3) [258,12,17,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4996
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4997 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 14 37 73 49 240 208 208 464), lower := (rows 259 14 37 73 49 32 64 128 256), losses := [] }

theorem u4997 : Upper (D 3) (R 3) [258,12,33,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4997
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4998 : Route 9 := (fun mask => (mask,id))

def c4998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4998 : Upper (D 3) (R 3) [258,12,33,65,96] 13 := by
  apply FastRouting.sound _ _ [258,12,33,65,96] 13 (by decide) (choices 1) [1,16,128] r4998 c4998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1902
  · exact u1903
  · exact u1904

def r4999 : Route 9 := (fun mask => (mask,id))

def c4999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4999 : Upper (D 3) (R 3) [258,12,33,65,129] 13 := by
  apply FastRouting.sound _ _ [258,12,33,65,129] 13 (by decide) (choices 1) [16,64,128] r4999 c4999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1905
  · exact u1906
  · exact u1907

def r5000 : Route 9 := (fun mask => (mask,id))

def c5000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5000 : Upper (D 3) (R 3) [258,12,33,65,160] 13 := by
  apply FastRouting.sound _ _ [258,12,33,65,160] 13 (by decide) (choices 1) [1,16,64,128] r5000 c5000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1908
  · exact u1909
  · exact u1910
  · exact u1911

def b5001 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 14 37 88 49 225 193 193 449), lower := (rows 259 14 37 88 49 32 64 128 256), losses := [] }

theorem u5001 : Upper (D 3) (R 3) [258,12,33,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5001
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5002 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 37 88 81 161 225 161 417), lower := (rows 259 14 37 88 81 32 64 128 256), losses := [] }

theorem u5002 : Upper (D 3) (R 3) [258,12,33,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5002
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5003 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 37 88 112 161 193 129 385), lower := (rows 259 14 37 88 112 32 64 128 256), losses := [] }

theorem u5003 : Upper (D 3) (R 3) [258,12,33,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5003
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5004 : Route 9 := (fun mask => (mask,id))

def c5004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5004 : Upper (D 3) (R 3) [258,12,33,80,129] 13 := by
  apply FastRouting.sound _ _ [258,12,33,80,129] 13 (by decide) (choices 1) [1,64,128] r5004 c5004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1912
  · exact u1913
  · exact u1914

def b5005 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 14 37 88 176 225 193 193 449), lower := (rows 259 14 37 88 176 32 64 128 256), losses := [] }

theorem u5005 : Upper (D 3) (R 3) [258,12,33,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5005
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5006 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 37 88 208 161 225 161 417), lower := (rows 259 14 37 88 208 32 64 128 256), losses := [] }

theorem u5006 : Upper (D 3) (R 3) [258,12,33,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5006
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5007 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 14 37 200 49 241 209 209 465), lower := (rows 259 14 37 200 49 32 64 128 256), losses := [] }

theorem u5007 : Upper (D 3) (R 3) [258,12,33,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5007
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5008 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 259 14 37 200 81 177 241 177 433), lower := (rows 259 14 37 200 81 32 64 128 256), losses := [] }

theorem u5008 : Upper (D 3) (R 3) [258,12,33,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5008
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5009 : Route 9 := (fun mask => (mask,id))

def c5009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5009 : Upper (D 3) (R 3) [258,12,33,192,96] 13 := by
  apply FastRouting.sound _ _ [258,12,33,192,96] 13 (by decide) (choices 1) [1,16,128] r5009 c5009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1915
  · exact u1916
  · exact u1917

def b5010 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 37 200 208 49 113 177 305), lower := (rows 259 14 37 200 208 32 64 128 256), losses := [] }

theorem u5010 : Upper (D 3) (R 3) [258,12,33,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5010
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5011 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 259 14 52 200 49 225 193 193 449), lower := (rows 259 14 52 200 49 32 64 128 256), losses := [] }

theorem u5011 : Upper (D 3) (R 3) [258,12,48,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5011
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5012 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 52 200 81 161 225 161 417), lower := (rows 259 14 52 200 81 32 64 128 256), losses := [] }

theorem u5012 : Upper (D 3) (R 3) [258,12,48,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5012
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5013 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 259 14 52 200 112 161 193 129 385), lower := (rows 259 14 52 200 112 32 64 128 256), losses := [] }

theorem u5013 : Upper (D 3) (R 3) [258,12,48,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5013
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5014 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 52 200 208 33 97 161 289), lower := (rows 259 14 52 200 208 32 64 128 256), losses := [] }

theorem u5014 : Upper (D 3) (R 3) [258,12,48,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5014
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5015 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 13 112 240 208 208 464), lower := (rows 259 35 13 13 112 32 64 128 256), losses := [] }

theorem u5015 : Upper (D 3) (R 3) [258,33,9,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5015
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5016 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 13 208 240 240 240 496), lower := (rows 259 35 13 13 208 32 64 128 256), losses := [] }

theorem u5016 : Upper (D 3) (R 3) [258,33,9,5,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5016
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5017 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 13 25 52 224 192 192 448), lower := (rows 259 35 13 25 52 32 64 128 256), losses := [] }

theorem u5017 : Upper (D 3) (R 3) [258,33,9,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5017
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5018 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 25 84 224 224 224 480), lower := (rows 259 35 13 25 84 32 64 128 256), losses := [] }

theorem u5018 : Upper (D 3) (R 3) [258,33,9,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5018
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5019 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 13 25 112 228 196 196 452), lower := (rows 259 35 13 25 112 32 64 128 256), losses := [] }

theorem u5019 : Upper (D 3) (R 3) [258,33,9,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5019
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5020 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 25 208 228 228 228 484), lower := (rows 259 35 13 25 208 32 64 128 256), losses := [] }

theorem u5020 : Upper (D 3) (R 3) [258,33,9,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5020
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5021 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 13 28 49 224 192 192 448), lower := (rows 259 35 13 28 49 32 64 128 256), losses := [] }

theorem u5021 : Upper (D 3) (R 3) [258,33,9,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5021
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5022 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 28 81 224 224 224 480), lower := (rows 259 35 13 28 81 32 64 128 256), losses := [] }

theorem u5022 : Upper (D 3) (R 3) [258,33,9,20,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5022
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5023 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 35 13 28 112 225 193 193 449), lower := (rows 259 35 13 28 112 32 64 128 256), losses := [] }

theorem u5023 : Upper (D 3) (R 3) [258,33,9,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5023
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5024 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5024 : Upper (D 3) (R 3) [258,33,9,20,192] 13 := by
  apply FastRouting.sound _ _ [258,33,9,20,192] 13 (by decide) (choices 1) [1,64] r5024 c5024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1918
  · exact u1919

def b5025 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 13 41 84 240 208 208 464), lower := (rows 259 35 13 41 84 32 64 128 256), losses := [] }

theorem u5025 : Upper (D 3) (R 3) [258,33,9,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5025
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5026 : PairBound 9 := { available := 212, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 13 41 208 244 212 212 468), lower := (rows 259 35 13 41 208 32 64 128 256), losses := [] }

theorem u5026 : Upper (D 3) (R 3) [258,33,9,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5026
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5027 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 13 44 81 240 208 208 464), lower := (rows 259 35 13 44 81 32 64 128 256), losses := [] }

theorem u5027 : Upper (D 3) (R 3) [258,33,9,36,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5027
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5028 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 13 44 208 241 209 209 465), lower := (rows 259 35 13 44 208 32 64 128 256), losses := [] }

theorem u5028 : Upper (D 3) (R 3) [258,33,9,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5028
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5029 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 35 13 56 81 228 196 196 452), lower := (rows 259 35 13 56 81 32 64 128 256), losses := [] }

theorem u5029 : Upper (D 3) (R 3) [258,33,9,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5029
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5030 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 35 13 56 84 225 193 193 449), lower := (rows 259 35 13 56 84 32 64 128 256), losses := [] }

theorem u5030 : Upper (D 3) (R 3) [258,33,9,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5030
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5031 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 35 13 56 208 229 197 197 453), lower := (rows 259 35 13 56 208 32 64 128 256), losses := [] }

theorem u5031 : Upper (D 3) (R 3) [258,33,9,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5031
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5032 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 73 52 240 208 208 464), lower := (rows 259 35 13 73 52 32 64 128 256), losses := [] }

theorem u5032 : Upper (D 3) (R 3) [258,33,9,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5032
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5033 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 73 84 176 240 176 432), lower := (rows 259 35 13 73 84 32 64 128 256), losses := [] }

theorem u5033 : Upper (D 3) (R 3) [258,33,9,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5033
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5034 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 73 112 180 212 148 404), lower := (rows 259 35 13 73 112 32 64 128 256), losses := [] }

theorem u5034 : Upper (D 3) (R 3) [258,33,9,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5034
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5035 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 73 148 240 240 240 496), lower := (rows 259 35 13 73 148 32 64 128 256), losses := [] }

theorem u5035 : Upper (D 3) (R 3) [258,33,9,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5035
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5036 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 73 176 244 212 212 468), lower := (rows 259 35 13 73 176 32 64 128 256), losses := [] }

theorem u5036 : Upper (D 3) (R 3) [258,33,9,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5036
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5037 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 73 208 180 244 180 436), lower := (rows 259 35 13 73 208 32 64 128 256), losses := [] }

theorem u5037 : Upper (D 3) (R 3) [258,33,9,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5037
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5038 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 35 13 76 49 240 208 208 464), lower := (rows 259 35 13 76 49 32 64 128 256), losses := [] }

theorem u5038 : Upper (D 3) (R 3) [258,33,9,68,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5038
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5039 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 76 81 176 240 176 432), lower := (rows 259 35 13 76 81 32 64 128 256), losses := [] }

theorem u5039 : Upper (D 3) (R 3) [258,33,9,68,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5039
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5039
end Delivery.IrregularNine14.P03
