import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0003

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b960 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 305 22 100 200 17 34 201 137 393), lower := (rows 305 22 100 200 17 34 64 128 256), losses := [] }

theorem u960 : Upper (D 0) (R 0) [304,20,96,192,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b960
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b961 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 22 100 200 17 40 195 131 387), lower := (rows 305 22 100 200 17 40 64 128 256), losses := [] }

theorem u961 : Upper (D 0) (R 0) [304,20,96,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b961
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b962 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 305 22 100 200 17 160 75 139 267), lower := (rows 305 22 100 200 17 160 64 128 256), losses := [] }

theorem u962 : Upper (D 0) (R 0) [304,20,96,192,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b962
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r963 : Route 9 := (fun mask => (mask,id))

def c963 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u963 : Upper (D 0) (R 0) [304,20,96,192,128,1] 13 := by
  apply FastRouting.sound _ _ [304,20,96,192,128,1] 13 (by decide) (choices 1) [1,2,8] r963 c963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u208
  · exact u209
  · exact u210

def b964 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 305 22 100 200 144 34 73 137 265), lower := (rows 305 22 100 200 144 34 64 128 256), losses := [] }

theorem u964 : Upper (D 0) (R 0) [304,20,96,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b964
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b965 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 22 100 200 144 40 67 131 259), lower := (rows 305 22 100 200 144 40 64 128 256), losses := [] }

theorem u965 : Upper (D 0) (R 0) [304,20,96,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b965
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b966 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 305 22 196 73 17 34 232 168 424), lower := (rows 305 22 196 73 17 34 64 128 256), losses := [] }

theorem u966 : Upper (D 0) (R 0) [304,20,192,65,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b966
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b967 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 22 196 73 17 40 226 162 418), lower := (rows 305 22 196 73 17 40 64 128 256), losses := [] }

theorem u967 : Upper (D 0) (R 0) [304,20,192,65,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b967
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r968 : Route 9 := (fun mask => (mask,id))

def c968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u968 : Upper (D 0) (R 0) [304,20,192,65,1,128] 13 := by
  apply FastRouting.sound _ _ [304,20,192,65,1,128] 13 (by decide) (choices 1) [2,8,32] r968 c968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u211
  · exact u212
  · exact u213

def b969 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 196 104 17 33 202 138 394), lower := (rows 305 22 196 104 17 33 64 128 256), losses := [] }

theorem u969 : Upper (D 0) (R 0) [304,20,192,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b969
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b970 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 305 22 196 104 17 34 201 137 393), lower := (rows 305 22 196 104 17 34 64 128 256), losses := [] }

theorem u970 : Upper (D 0) (R 0) [304,20,192,96,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b970
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b971 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 22 196 104 17 40 195 131 387), lower := (rows 305 22 196 104 17 40 64 128 256), losses := [] }

theorem u971 : Upper (D 0) (R 0) [304,20,192,96,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b971
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b972 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 305 22 196 104 17 160 75 139 267), lower := (rows 305 22 196 104 17 160 64 128 256), losses := [] }

theorem u972 : Upper (D 0) (R 0) [304,20,192,96,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b972
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b973 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 305 67 76 137 18 160 116 180 308), lower := (rows 305 67 76 137 18 160 64 128 256), losses := [] }

theorem u973 : Upper (D 0) (R 0) [304,65,72,129,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b973
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b974 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 305 67 76 137 20 160 114 178 306), lower := (rows 305 67 76 137 20 160 64 128 256), losses := [] }

theorem u974 : Upper (D 0) (R 0) [304,65,72,129,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b974
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b975 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 76 137 48 160 86 150 278), lower := (rows 305 67 76 137 48 160 64 128 256), losses := [] }

theorem u975 : Upper (D 0) (R 0) [304,65,72,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b975
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b976 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 305 67 76 152 17 34 228 164 420), lower := (rows 305 67 76 152 17 34 64 128 256), losses := [] }

theorem u976 : Upper (D 0) (R 0) [304,65,72,144,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b976
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b977 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 67 76 152 17 36 226 162 418), lower := (rows 305 67 76 152 17 36 64 128 256), losses := [] }

theorem u977 : Upper (D 0) (R 0) [304,65,72,144,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b977
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r978 : Route 9 := (fun mask => (mask,id))

def c978 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u978 : Upper (D 0) (R 0) [304,65,72,144,1,128] 13 := by
  apply FastRouting.sound _ _ [304,65,72,144,1,128] 13 (by decide) (choices 1) [2,4,32] r978 c978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u214
  · exact u215
  · exact u216

def b979 : PairBound 9 := { available := 44, camps := [], pairs := [], upper := (rows 305 67 84 137 144 34 108 172 300), lower := (rows 305 67 84 137 144 34 64 128 256), losses := [] }

theorem u979 : Upper (D 0) (R 0) [304,65,80,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b979
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b980 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 305 67 84 137 144 36 106 170 298), lower := (rows 305 67 84 137 144 36 64 128 256), losses := [] }

theorem u980 : Upper (D 0) (R 0) [304,65,80,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b980
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b981 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 305 67 84 137 144 40 102 166 294), lower := (rows 305 67 84 137 144 40 64 128 256), losses := [] }

theorem u981 : Upper (D 0) (R 0) [304,65,80,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b981
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r982 : Route 9 := (fun mask => (mask,id))

def c982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u982 : Upper (D 0) (R 0) [304,65,80,130,128,1] 13 := by
  apply FastRouting.sound _ _ [304,65,80,130,128,1] 13 (by decide) (choices 1) [4,8,32] r982 c982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u217
  · exact u218
  · exact u219

def b983 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 305 67 84 138 144 36 105 169 297), lower := (rows 305 67 84 138 144 36 64 128 256), losses := [] }

theorem u983 : Upper (D 0) (R 0) [304,65,80,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b983
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b984 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 305 67 84 138 144 40 101 165 293), lower := (rows 305 67 84 138 144 40 64 128 256), losses := [] }

theorem u984 : Upper (D 0) (R 0) [304,65,80,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b984
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r985 : Route 9 := (fun mask => (mask,id))

def c985 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u985 : Upper (D 0) (R 0) [304,65,80,132,128,1] 13 := by
  apply FastRouting.sound _ _ [304,65,80,132,128,1] 13 (by decide) (choices 1) [2,8,32] r985 c985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u220
  · exact u221
  · exact u222

def b986 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 305 67 84 140 144 34 105 169 297), lower := (rows 305 67 84 140 144 34 64 128 256), losses := [] }

theorem u986 : Upper (D 0) (R 0) [304,65,80,132,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b986
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b987 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 305 67 84 140 144 40 99 163 291), lower := (rows 305 67 84 140 144 40 64 128 256), losses := [] }

theorem u987 : Upper (D 0) (R 0) [304,65,80,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b987
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r988 : Route 9 := (fun mask => (mask,id))

def c988 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u988 : Upper (D 0) (R 0) [304,65,80,160,128,1] 13 := by
  apply FastRouting.sound _ _ [304,65,80,160,128,1] 13 (by decide) (choices 1) [2,4,8] r988 c988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u223
  · exact u224
  · exact u225

def b989 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 305 67 84 168 144 34 77 141 269), lower := (rows 305 67 84 168 144 34 64 128 256), losses := [] }

theorem u989 : Upper (D 0) (R 0) [304,65,80,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b989
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b990 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 305 67 84 168 144 36 75 139 267), lower := (rows 305 67 84 168 144 36 64 128 256), losses := [] }

theorem u990 : Upper (D 0) (R 0) [304,65,80,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b990
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b991 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 305 67 84 168 144 40 71 135 263), lower := (rows 305 67 84 168 144 40 64 128 256), losses := [] }

theorem u991 : Upper (D 0) (R 0) [304,65,80,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b991
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b992 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 305 67 134 200 17 36 120 184 312), lower := (rows 305 67 134 200 17 36 64 128 256), losses := [] }

theorem u992 : Upper (D 0) (R 0) [304,65,130,192,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b992
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b993 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 305 67 134 200 17 40 116 180 308), lower := (rows 305 67 134 200 17 40 64 128 256), losses := [] }

theorem u993 : Upper (D 0) (R 0) [304,65,130,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b993
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b994 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 206, targets := 16 }], pairs := [(1,4)], upper := (rows 305 67 134 200 17 48 108 172 300), lower := (rows 305 67 134 200 17 48 64 128 256), losses := [] }

theorem u994 : Upper (D 0) (R 0) [304,65,130,192,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b994
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b995 : PairBound 9 := { available := 76, camps := [], pairs := [], upper := (rows 305 67 148 168 17 34 76 204 332), lower := (rows 305 67 148 168 17 34 64 128 256), losses := [] }

theorem u995 : Upper (D 0) (R 0) [304,65,144,160,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b995
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b996 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 305 67 148 168 17 36 74 202 330), lower := (rows 305 67 148 168 17 36 64 128 256), losses := [] }

theorem u996 : Upper (D 0) (R 0) [304,65,144,160,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b996
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b997 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 305 67 148 168 17 40 70 198 326), lower := (rows 305 67 148 168 17 40 64 128 256), losses := [] }

theorem u997 : Upper (D 0) (R 0) [304,65,144,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b997
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r998 : Route 9 := (fun mask => (mask,id))

def c998 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u998 : Upper (D 0) (R 0) [304,65,144,160,1,64] 13 := by
  apply FastRouting.sound _ _ [304,65,144,160,1,64] 13 (by decide) (choices 1) [2,4,8] r998 c998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u226
  · exact u227
  · exact u228

def b999 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 305 67 148 168 18 96 77 141 269), lower := (rows 305 67 148 168 18 96 64 128 256), losses := [] }

theorem u999 : Upper (D 0) (R 0) [304,65,144,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b999
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1000 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 305 67 148 168 20 96 75 139 267), lower := (rows 305 67 148 168 20 96 64 128 256), losses := [] }

theorem u1000 : Upper (D 0) (R 0) [304,65,144,160,4,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1000
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1001 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 305 67 148 168 24 96 71 135 263), lower := (rows 305 67 148 168 24 96 64 128 256), losses := [] }

theorem u1001 : Upper (D 0) (R 0) [304,65,144,160,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1001
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1002 : PairBound 9 := { available := 44, camps := [], pairs := [], upper := (rows 305 67 148 200 17 34 108 172 300), lower := (rows 305 67 148 200 17 34 64 128 256), losses := [] }

theorem u1002 : Upper (D 0) (R 0) [304,65,144,192,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1002
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1003 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 305 67 148 200 17 36 106 170 298), lower := (rows 305 67 148 200 17 36 64 128 256), losses := [] }

theorem u1003 : Upper (D 0) (R 0) [304,65,144,192,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1003
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1004 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 305 67 148 200 17 40 102 166 294), lower := (rows 305 67 148 200 17 40 64 128 256), losses := [] }

theorem u1004 : Upper (D 0) (R 0) [304,65,144,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1004
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1005 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 305 70 148 104 17 33 202 138 394), lower := (rows 305 70 148 104 17 33 64 128 256), losses := [] }

theorem u1005 : Upper (D 0) (R 0) [304,68,144,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1005
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1006 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 305 70 148 104 17 34 201 137 393), lower := (rows 305 70 148 104 17 34 64 128 256), losses := [] }

theorem u1006 : Upper (D 0) (R 0) [304,68,144,96,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1006
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1007 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 70 148 104 17 40 195 131 387), lower := (rows 305 70 148 104 17 40 64 128 256), losses := [] }

theorem u1007 : Upper (D 0) (R 0) [304,68,144,96,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1007
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1008 : PairBound 9 := { available := 11, camps := [], pairs := [(3,0)], upper := (rows 305 70 148 104 17 160 75 139 267), lower := (rows 305 70 148 104 17 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 164 64 128 256), good := (rows 304 110 180 104 16 160 64 160 256) }] }

theorem u1008 : Upper (D 0) (R 0) [304,68,144,96,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1008
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1009 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 305 70 148 168 17 33 74 202 330), lower := (rows 305 70 148 168 17 33 64 128 256), losses := [] }

theorem u1009 : Upper (D 0) (R 0) [304,68,144,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1009
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1010 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 305 70 148 168 17 34 73 201 329), lower := (rows 305 70 148 168 17 34 64 128 256), losses := [] }

theorem u1010 : Upper (D 0) (R 0) [304,68,144,160,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1010
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1011 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 305 70 148 168 17 40 67 195 323), lower := (rows 305 70 148 168 17 40 64 128 256), losses := [] }

theorem u1011 : Upper (D 0) (R 0) [304,68,144,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1011
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1012 : Route 9 := (fun mask => (mask,id))

def c1012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1012 : Upper (D 0) (R 0) [304,68,144,160,1,64] 13 := by
  apply FastRouting.sound _ _ [304,68,144,160,1,64] 13 (by decide) (choices 1) [1,2,8] r1012 c1012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u229
  · exact u230
  · exact u231

def r1013 : Route 9 := (fun mask => (mask,id))

def c1013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1013 : Upper (D 0) (R 0) [304,68,144,160,64,1] 13 := by
  apply FastRouting.sound _ _ [304,68,144,160,64,1] 13 (by decide) (choices 1) [1,2,8] r1013 c1013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u232
  · exact u233
  · exact u234

def b1014 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 305 70 148 168 80 34 73 137 265), lower := (rows 305 70 148 168 80 34 64 128 256), losses := [] }

theorem u1014 : Upper (D 0) (R 0) [304,68,144,160,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1014
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1015 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 70 148 168 80 40 67 131 259), lower := (rows 305 70 148 168 80 40 64 128 256), losses := [] }

theorem u1015 : Upper (D 0) (R 0) [304,68,144,160,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1015
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1016 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 305 70 148 200 17 33 106 170 298), lower := (rows 305 70 148 200 17 33 64 128 256), losses := [] }

theorem u1016 : Upper (D 0) (R 0) [304,68,144,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1016
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1017 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 305 70 148 200 17 34 105 169 297), lower := (rows 305 70 148 200 17 34 64 128 256), losses := [] }

theorem u1017 : Upper (D 0) (R 0) [304,68,144,192,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1017
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1018 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 305 70 148 200 17 40 99 163 291), lower := (rows 305 70 148 200 17 40 64 128 256), losses := [] }

theorem u1018 : Upper (D 0) (R 0) [304,68,144,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1018
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1019 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 305 82 164 200 17 33 78 142 270), lower := (rows 305 82 164 200 17 33 64 128 256), losses := [] }

theorem u1019 : Upper (D 0) (R 0) [304,80,160,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1019
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1019
end Delivery.IrregularNine14.P00
