import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0020
import IrregularNine14P05C0021

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3900 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 140 273 33 104 168 296), lower := (rows 19 70 38 140 273 33 64 128 256), losses := [] }

theorem u3900 : Upper (D 5) (R 5) [18,68,34,132,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3900
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3901 : Route 9 := (fun mask => (mask,id))

def c3901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3901 : Upper (D 5) (R 5) [18,68,34,132,257,8] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132,257,8] 13 (by decide) (choices 1) [1,8,32] r3901 c3901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1245
  · exact u1246
  · exact u1247

def r3902 : Route 9 := (fun mask => (mask,id))

def c3902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3902 : Upper (D 5) (R 5) [18,68,34,132,264,1] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132,264,1] 13 (by decide) (choices 1) [1,8,32] r3902 c3902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1248
  · exact u1249
  · exact u1250

def b3903 : PairBound 9 := { available := 33, camps := [], pairs := [(0,2),(2,0)], upper := (rows 19 70 38 140 280 40 97 161 289), lower := (rows 19 70 38 140 280 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 56 64 128 256), good := (rows 54 70 38 172 312 40 64 128 256) },{ target := 2, region := (rows 5 2 0 8 56 56 77 141 269), good := (rows 499 451 499 505 504 504 64 128 256) }] }

theorem u3903 : Upper (D 5) (R 5) [18,68,34,132,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3903
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3904 : Route 9 := (fun mask => (mask,id))

def c3904 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3904 : Upper (D 5) (R 5) [18,68,34,132,288,1] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132,288,1] 13 (by decide) (choices 1) [1,8] r3904 c3904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1251
  · exact u1252

def b3905 : PairBound 9 := { available := 9, camps := [], pairs := [(0,2),(4,2)], upper := (rows 19 70 38 140 304 40 73 137 265), lower := (rows 19 70 38 140 304 40 64 128 256), losses := [{ target := 2, region := (rows 5 2 0 8 56 40 72 136 264), good := (rows 19 67 51 505 304 504 64 128 256) }] }

theorem u3905 : Upper (D 5) (R 5) [18,68,34,132,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3905
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3906 : PairBound 9 := { available := 268, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 168 25 33 332 396 268), lower := (rows 19 70 38 168 25 33 64 128 256), losses := [] }

theorem u3906 : Upper (D 5) (R 5) [18,68,34,160,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3906
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3907 : PairBound 9 := { available := 265, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 168 25 36 329 393 265), lower := (rows 19 70 38 168 25 36 64 128 256), losses := [] }

theorem u3907 : Upper (D 5) (R 5) [18,68,34,160,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3907
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3908 : PairBound 9 := { available := 261, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 38 168 25 40 325 389 261), lower := (rows 19 70 38 168 25 40 64 128 256), losses := [] }

theorem u3908 : Upper (D 5) (R 5) [18,68,34,160,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3908
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3909 : Route 9 := (fun mask => (mask,id))

def c3909 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3909 : Upper (D 5) (R 5) [18,68,34,160,9,256] 13 := by
  apply FastRouting.sound _ _ [18,68,34,160,9,256] 13 (by decide) (choices 1) [1,4,8] r3909 c3909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1253
  · exact u1254
  · exact u1255

def b3910 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 168 273 33 76 140 268), lower := (rows 19 70 38 168 273 33 64 128 256), losses := [] }

theorem u3910 : Upper (D 5) (R 5) [18,68,34,160,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3910
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3911 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 168 273 36 73 137 265), lower := (rows 19 70 38 168 273 36 64 128 256), losses := [] }

theorem u3911 : Upper (D 5) (R 5) [18,68,34,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3911
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3912 : PairBound 9 := { available := 13, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 38 168 273 40 77 141 269), lower := (rows 19 70 38 168 273 40 64 128 256), losses := [] }

theorem u3912 : Upper (D 5) (R 5) [18,68,34,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3912
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3913 : Route 9 := (fun mask => (mask,id))

def c3913 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3913 : Upper (D 5) (R 5) [18,68,34,160,264,1] 13 := by
  apply FastRouting.sound _ _ [18,68,34,160,264,1] 13 (by decide) (choices 1) [1,4,8] r3913 c3913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1256
  · exact u1257
  · exact u1258

def b3914 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 168 280 36 73 137 265), lower := (rows 19 70 38 168 280 36 64 128 256), losses := [] }

theorem u3914 : Upper (D 5) (R 5) [18,68,34,160,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3914
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3915 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 38 168 280 40 69 133 261), lower := (rows 19 70 38 168 280 40 64 128 256), losses := [] }

theorem u3915 : Upper (D 5) (R 5) [18,68,34,160,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3915
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3916 : PairBound 9 := { available := 44, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 392 25 33 108 172 300), lower := (rows 19 70 38 392 25 33 64 128 256), losses := [] }

theorem u3916 : Upper (D 5) (R 5) [18,68,34,384,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3916
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3917 : PairBound 9 := { available := 41, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 392 25 36 105 169 297), lower := (rows 19 70 38 392 25 36 64 128 256), losses := [] }

theorem u3917 : Upper (D 5) (R 5) [18,68,34,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3917
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3918 : Route 9 := (fun mask => (mask,id))

def c3918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3918 : Upper (D 5) (R 5) [18,68,34,384,9,8] 13 := by
  apply FastRouting.sound _ _ [18,68,34,384,9,8] 13 (by decide) (choices 1) [1,4,32] r3918 c3918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1259
  · exact u1260
  · exact u1261

def r3919 : Route 9 := (fun mask => (mask,id))

def c3919 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3919 : Upper (D 5) (R 5) [18,68,34,384,40,1] 13 := by
  apply FastRouting.sound _ _ [18,68,34,384,40,1] 13 (by decide) (choices 1) [1,4,8] r3919 c3919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1262
  · exact u1263
  · exact u1264

def b3920 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 392 56 36 73 137 265), lower := (rows 19 70 38 392 56 36 64 128 256), losses := [] }

theorem u3920 : Upper (D 5) (R 5) [18,68,34,384,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3920
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3921 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 38 392 56 40 69 133 261), lower := (rows 19 70 38 392 56 40 64 128 256), losses := [] }

theorem u3921 : Upper (D 5) (R 5) [18,68,34,384,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3921
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3922 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 19 70 44 137 276 33 106 170 298), lower := (rows 19 70 44 137 276 33 64 128 256), losses := [] }

theorem u3922 : Upper (D 5) (R 5) [18,68,40,129,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3922
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3923 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 168, targets := 4 }], pairs := [(2,0),(3,2)], upper := (rows 19 70 44 137 276 34 105 169 297), lower := (rows 19 70 44 137 276 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 35 64 128 256), good := (rows 50 102 44 172 276 34 64 128 256) }] }

theorem u3923 : Upper (D 5) (R 5) [18,68,40,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3923
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3924 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 44 137 276 40 99 163 291), lower := (rows 19 70 44 137 276 40 64 128 256), losses := [] }

theorem u3924 : Upper (D 5) (R 5) [18,68,40,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3924
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3925 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 19 70 44 137 280 33 102 166 294), lower := (rows 19 70 44 137 280 33 64 128 256), losses := [] }

theorem u3925 : Upper (D 5) (R 5) [18,68,40,129,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3925
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3926 : Route 9 := (fun mask => (mask,id))

def c3926 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3926 : Upper (D 5) (R 5) [18,68,40,129,264,2] 13 := by
  apply FastRouting.sound _ _ [18,68,40,129,264,2] 13 (by decide) (choices 1) [1,4,32] r3926 c3926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1265
  · exact u1266
  · exact u1267

def b3927 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 44 137 280 36 99 163 291), lower := (rows 19 70 44 137 280 36 64 128 256), losses := [] }

theorem u3927 : Upper (D 5) (R 5) [18,68,40,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3927
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3928 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 19 70 44 137 304 33 78 142 270), lower := (rows 19 70 44 137 304 33 64 128 256), losses := [] }

theorem u3928 : Upper (D 5) (R 5) [18,68,40,129,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3928
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3929 : Route 9 := (fun mask => (mask,id))

def c3929 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3929 : Upper (D 5) (R 5) [18,68,40,129,288,2] 13 := by
  apply FastRouting.sound _ _ [18,68,40,129,288,2] 13 (by decide) (choices 1) [1,4,8] r3929 c3929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1268
  · exact u1269
  · exact u1270

def b3930 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 19 70 44 137 304 36 75 139 267), lower := (rows 19 70 44 137 304 36 64 128 256), losses := [] }

theorem u3930 : Upper (D 5) (R 5) [18,68,40,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3930
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3931 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 44 137 304 40 71 135 263), lower := (rows 19 70 44 137 304 40 64 128 256), losses := [] }

theorem u3931 : Upper (D 5) (R 5) [18,68,40,129,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3931
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3932 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 138 49 33 332 396 268), lower := (rows 19 70 44 138 49 33 64 128 256), losses := [] }

theorem u3932 : Upper (D 5) (R 5) [18,68,40,130,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3932
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3933 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 392, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 19 70 44 138 49 36 329 393 265), lower := (rows 19 70 44 138 49 36 64 128 256), losses := [] }

theorem u3933 : Upper (D 5) (R 5) [18,68,40,130,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3933
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3934 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 44 138 49 40 325 389 261), lower := (rows 19 70 44 138 49 40 64 128 256), losses := [] }

theorem u3934 : Upper (D 5) (R 5) [18,68,40,130,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3934
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3935 : Route 9 := (fun mask => (mask,id))

def c3935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3935 : Upper (D 5) (R 5) [18,68,40,130,33,256] 13 := by
  apply FastRouting.sound _ _ [18,68,40,130,33,256] 13 (by decide) (choices 1) [1,4,8] r3935 c3935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1271
  · exact u1272
  · exact u1273

def b3936 : PairBound 9 := { available := 44, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 44 138 273 33 108 172 300), lower := (rows 19 70 44 138 273 33 64 128 256), losses := [] }

theorem u3936 : Upper (D 5) (R 5) [18,68,40,130,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3936
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3937 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 44 138 273 36 105 169 297), lower := (rows 19 70 44 138 273 36 64 128 256), losses := [] }

theorem u3937 : Upper (D 5) (R 5) [18,68,40,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3937
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3938 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 44 138 273 40 101 165 293), lower := (rows 19 70 44 138 273 40 64 128 256), losses := [] }

theorem u3938 : Upper (D 5) (R 5) [18,68,40,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3938
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3939 : Route 9 := (fun mask => (mask,id))

def c3939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3939 : Upper (D 5) (R 5) [18,68,40,130,260,1] 13 := by
  apply FastRouting.sound _ _ [18,68,40,130,260,1] 13 (by decide) (choices 1) [1,8,32] r3939 c3939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1274
  · exact u1275
  · exact u1276

def b3940 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 44 138 276 40 97 161 289), lower := (rows 19 70 44 138 276 40 64 128 256), losses := [] }

theorem u3940 : Upper (D 5) (R 5) [18,68,40,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3940
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3941 : Route 9 := (fun mask => (mask,id))

def c3941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3941 : Upper (D 5) (R 5) [18,68,40,130,264,1] 13 := by
  apply FastRouting.sound _ _ [18,68,40,130,264,1] 13 (by decide) (choices 1) [1,4,32] r3941 c3941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1277
  · exact u1278
  · exact u1279

def b3942 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 44 138 280 36 97 161 289), lower := (rows 19 70 44 138 280 36 64 128 256), losses := [] }

theorem u3942 : Upper (D 5) (R 5) [18,68,40,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3942
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3943 : Route 9 := (fun mask => (mask,id))

def c3943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3943 : Upper (D 5) (R 5) [18,68,40,130,288,1] 13 := by
  apply FastRouting.sound _ _ [18,68,40,130,288,1] 13 (by decide) (choices 1) [1,4,8] r3943 c3943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1280
  · exact u1281
  · exact u1282

def b3944 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 19 70 44 138 304 36 73 137 265), lower := (rows 19 70 44 138 304 36 64 128 256), losses := [] }

theorem u3944 : Upper (D 5) (R 5) [18,68,40,130,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3944
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3945 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 44 138 304 40 69 133 261), lower := (rows 19 70 44 138 304 40 64 128 256), losses := [] }

theorem u3945 : Upper (D 5) (R 5) [18,68,40,130,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3945
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3946 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 44 140 25 33 354 418 290), lower := (rows 19 70 44 140 25 33 64 128 256), losses := [] }

theorem u3946 : Upper (D 5) (R 5) [18,68,40,132,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3946
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3947 : Route 9 := (fun mask => (mask,id))

def c3947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3947 : Upper (D 5) (R 5) [18,68,40,132,9,2] 13 := by
  apply FastRouting.sound _ _ [18,68,40,132,9,2] 13 (by decide) (choices 1) [1,32,256] r3947 c3947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1283
  · exact u1284
  · exact u1285

def r3948 : Route 9 := (fun mask => (mask,id))

def c3948 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3948 : Upper (D 5) (R 5) [18,68,40,132,9,256] 13 := by
  apply FastRouting.sound _ _ [18,68,40,132,9,256] 13 (by decide) (choices 1) [1,2,32] r3948 c3948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1286
  · exact u1287
  · exact u1288

def b3949 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 140 49 33 330 394 266), lower := (rows 19 70 44 140 49 33 64 128 256), losses := [] }

theorem u3949 : Upper (D 5) (R 5) [18,68,40,132,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3949
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3950 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 140 49 34 329 393 265), lower := (rows 19 70 44 140 49 34 64 128 256), losses := [] }

theorem u3950 : Upper (D 5) (R 5) [18,68,40,132,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3950
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3951 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 44 140 49 40 323 387 259), lower := (rows 19 70 44 140 49 40 64 128 256), losses := [] }

theorem u3951 : Upper (D 5) (R 5) [18,68,40,132,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3951
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3952 : Route 9 := (fun mask => (mask,id))

def c3952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3952 : Upper (D 5) (R 5) [18,68,40,132,33,256] 13 := by
  apply FastRouting.sound _ _ [18,68,40,132,33,256] 13 (by decide) (choices 1) [1,2,8] r3952 c3952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1289
  · exact u1290
  · exact u1291

def b3953 : PairBound 9 := { available := 42, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 44 140 273 33 106 170 298), lower := (rows 19 70 44 140 273 33 64 128 256), losses := [] }

theorem u3953 : Upper (D 5) (R 5) [18,68,40,132,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3953
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3954 : PairBound 9 := { available := 41, camps := [], pairs := [(0,2),(4,2)], upper := (rows 19 70 44 140 273 34 105 169 297), lower := (rows 19 70 44 140 273 34 64 128 256), losses := [{ target := 2, region := (rows 35 2 0 8 22 35 68 132 260), good := (rows 51 499 505 472 305 51 64 128 256) }] }

theorem u3954 : Upper (D 5) (R 5) [18,68,40,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3954
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3955 : PairBound 9 := { available := 35, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 44 140 273 40 99 163 291), lower := (rows 19 70 44 140 273 40 64 128 256), losses := [] }

theorem u3955 : Upper (D 5) (R 5) [18,68,40,132,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3955
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3956 : Route 9 := (fun mask => (mask,id))

def c3956 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3956 : Upper (D 5) (R 5) [18,68,40,132,264,1] 13 := by
  apply FastRouting.sound _ _ [18,68,40,132,264,1] 13 (by decide) (choices 1) [1,2,32] r3956 c3956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1292
  · exact u1293
  · exact u1294

def b3957 : PairBound 9 := { available := 33, camps := [], pairs := [(0,2),(4,2)], upper := (rows 19 70 44 140 280 34 97 161 289), lower := (rows 19 70 44 140 280 34 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 20 35 99 163 291), good := (rows 499 499 504 152 280 483 64 128 256) }] }

theorem u3957 : Upper (D 5) (R 5) [18,68,40,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3957
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3958 : Route 9 := (fun mask => (mask,id))

def c3958 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3958 : Upper (D 5) (R 5) [18,68,40,132,288,1] 13 := by
  apply FastRouting.sound _ _ [18,68,40,132,288,1] 13 (by decide) (choices 1) [1,2,8] r3958 c3958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1295
  · exact u1296
  · exact u1297

def b3959 : PairBound 9 := { available := 9, camps := [], pairs := [(0,2),(4,2)], upper := (rows 19 70 44 140 304 34 73 137 265), lower := (rows 19 70 44 140 304 34 64 128 256), losses := [{ target := 2, region := (rows 35 2 0 8 22 35 68 132 260), good := (rows 51 499 505 472 305 51 64 128 256) }] }

theorem u3959 : Upper (D 5) (R 5) [18,68,40,132,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3959
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u3959
end Delivery.IrregularNine14.P05
