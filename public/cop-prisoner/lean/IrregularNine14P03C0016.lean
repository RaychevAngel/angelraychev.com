import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0002

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b960 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 140 336 160 113 177 305), lower := (rows 35 67 13 140 336 160 64 128 256), losses := [] }

theorem u960 : Upper (D 3) (R 3) [34,65,9,132,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b960
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b961 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 67 13 152 273 36 224 224 480), lower := (rows 35 67 13 152 273 36 64 128 256), losses := [] }

theorem u961 : Upper (D 3) (R 3) [34,65,9,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b961
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b962 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 152 273 96 228 164 420), lower := (rows 35 67 13 152 273 96 64 128 256), losses := [] }

theorem u962 : Upper (D 3) (R 3) [34,65,9,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b962
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r963 : Route 9 := (fun mask => (mask,id))

def c963 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u963 : Upper (D 3) (R 3) [34,65,9,144,257,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,257,128] 13 (by decide) (choices 1) [4,32] r963 c963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u143
  · exact u144

def b964 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 152 276 33 224 224 480), lower := (rows 35 67 13 152 276 33 64 128 256), losses := [] }

theorem u964 : Upper (D 3) (R 3) [34,65,9,144,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b964
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b965 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 152 276 96 225 161 417), lower := (rows 35 67 13 152 276 96 64 128 256), losses := [] }

theorem u965 : Upper (D 3) (R 3) [34,65,9,144,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b965
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b966 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 152 276 160 97 225 353), lower := (rows 35 67 13 152 276 160 64 128 256), losses := [] }

theorem u966 : Upper (D 3) (R 3) [34,65,9,144,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b966
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b967 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 152 336 33 228 164 420), lower := (rows 35 67 13 152 336 33 64 128 256), losses := [] }

theorem u967 : Upper (D 3) (R 3) [34,65,9,144,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b967
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b968 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 13 152 336 36 225 161 417), lower := (rows 35 67 13 152 336 36 64 128 256), losses := [] }

theorem u968 : Upper (D 3) (R 3) [34,65,9,144,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b968
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r969 : Route 9 := (fun mask => (mask,id))

def c969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u969 : Upper (D 3) (R 3) [34,65,9,144,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,320,128] 13 (by decide) (choices 1) [1,4,32] r969 c969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u145
  · exact u146
  · exact u147

def b970 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 67 13 268 145 48 224 224 480), lower := (rows 35 67 13 268 145 48 64 128 256), losses := [] }

theorem u970 : Upper (D 3) (R 3) [34,65,9,260,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b970
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b971 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 268 145 96 240 176 432), lower := (rows 35 67 13 268 145 96 64 128 256), losses := [] }

theorem u971 : Upper (D 3) (R 3) [34,65,9,260,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b971
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r972 : Route 9 := (fun mask => (mask,id))

def c972 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u972 : Upper (D 3) (R 3) [34,65,9,260,129,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,260,129,128] 13 (by decide) (choices 1) [16,32] r972 c972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u148
  · exact u149

def b973 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 268 176 33 208 208 464), lower := (rows 35 67 13 268 176 33 64 128 256), losses := [] }

theorem u973 : Upper (D 3) (R 3) [34,65,9,260,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b973
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b974 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 13 268 176 48 193 193 449), lower := (rows 35 67 13 268 176 48 64 128 256), losses := [] }

theorem u974 : Upper (D 3) (R 3) [34,65,9,260,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b974
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b975 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 268 176 96 209 145 401), lower := (rows 35 67 13 268 176 96 64 128 256), losses := [] }

theorem u975 : Upper (D 3) (R 3) [34,65,9,260,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b975
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b976 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 268 176 160 81 209 337), lower := (rows 35 67 13 268 176 160 64 128 256), losses := [] }

theorem u976 : Upper (D 3) (R 3) [34,65,9,260,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b976
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b977 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 268 208 33 240 176 432), lower := (rows 35 67 13 268 208 33 64 128 256), losses := [] }

theorem u977 : Upper (D 3) (R 3) [34,65,9,260,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b977
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b978 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 13 268 208 48 225 161 417), lower := (rows 35 67 13 268 208 48 64 128 256), losses := [] }

theorem u978 : Upper (D 3) (R 3) [34,65,9,260,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b978
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r979 : Route 9 := (fun mask => (mask,id))

def c979 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u979 : Upper (D 3) (R 3) [34,65,9,260,192,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,260,192,128] 13 (by decide) (choices 1) [1,16,32] r979 c979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u150
  · exact u151
  · exact u152

def b980 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 67 13 280 145 36 224 224 480), lower := (rows 35 67 13 280 145 36 64 128 256), losses := [] }

theorem u980 : Upper (D 3) (R 3) [34,65,9,272,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b980
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b981 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 280 145 96 228 164 420), lower := (rows 35 67 13 280 145 96 64 128 256), losses := [] }

theorem u981 : Upper (D 3) (R 3) [34,65,9,272,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b981
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r982 : Route 9 := (fun mask => (mask,id))

def c982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u982 : Upper (D 3) (R 3) [34,65,9,272,129,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,129,128] 13 (by decide) (choices 1) [4,32] r982 c982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u153
  · exact u154

def b983 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 280 148 33 224 224 480), lower := (rows 35 67 13 280 148 33 64 128 256), losses := [] }

theorem u983 : Upper (D 3) (R 3) [34,65,9,272,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b983
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b984 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 280 148 96 225 161 417), lower := (rows 35 67 13 280 148 96 64 128 256), losses := [] }

theorem u984 : Upper (D 3) (R 3) [34,65,9,272,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b984
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b985 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 280 148 160 97 225 353), lower := (rows 35 67 13 280 148 160 64 128 256), losses := [] }

theorem u985 : Upper (D 3) (R 3) [34,65,9,272,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b985
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b986 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 280 208 33 228 164 420), lower := (rows 35 67 13 280 208 33 64 128 256), losses := [] }

theorem u986 : Upper (D 3) (R 3) [34,65,9,272,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b986
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b987 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 13 280 208 36 225 161 417), lower := (rows 35 67 13 280 208 36 64 128 256), losses := [] }

theorem u987 : Upper (D 3) (R 3) [34,65,9,272,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b987
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r988 : Route 9 := (fun mask => (mask,id))

def c988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u988 : Upper (D 3) (R 3) [34,65,9,272,192,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,192,128] 13 (by decide) (choices 1) [1,4,32] r988 c988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u155
  · exact u156
  · exact u157

def b989 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 392 52 33 208 208 464), lower := (rows 35 67 13 392 52 33 64 128 256), losses := [] }

theorem u989 : Upper (D 3) (R 3) [34,65,9,384,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b989
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b990 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 13 392 52 48 193 193 449), lower := (rows 35 67 13 392 52 48 64 128 256), losses := [] }

theorem u990 : Upper (D 3) (R 3) [34,65,9,384,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b990
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b991 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 392 52 96 209 145 401), lower := (rows 35 67 13 392 52 96 64 128 256), losses := [] }

theorem u991 : Upper (D 3) (R 3) [34,65,9,384,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b991
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b992 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 392 52 160 81 209 337), lower := (rows 35 67 13 392 52 160 64 128 256), losses := [] }

theorem u992 : Upper (D 3) (R 3) [34,65,9,384,36,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b992
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b993 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 392 84 33 240 176 432), lower := (rows 35 67 13 392 84 33 64 128 256), losses := [] }

theorem u993 : Upper (D 3) (R 3) [34,65,9,384,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b993
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b994 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 13 392 84 48 225 161 417), lower := (rows 35 67 13 392 84 48 64 128 256), losses := [] }

theorem u994 : Upper (D 3) (R 3) [34,65,9,384,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b994
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r995 : Route 9 := (fun mask => (mask,id))

def c995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u995 : Upper (D 3) (R 3) [34,65,9,384,68,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,68,128] 13 (by decide) (choices 1) [1,16,32] r995 c995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u158
  · exact u159
  · exact u160

def b996 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 35 67 13 392 145 36 112 240 368), lower := (rows 35 67 13 392 145 36 64 128 256), losses := [] }

theorem u996 : Upper (D 3) (R 3) [34,65,9,384,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b996
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b997 : PairBound 9 := { available := 100, camps := [], pairs := [], upper := (rows 35 67 13 392 145 48 100 228 356), lower := (rows 35 67 13 392 145 48 64 128 256), losses := [] }

theorem u997 : Upper (D 3) (R 3) [34,65,9,384,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b997
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b998 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 392 145 96 116 180 308), lower := (rows 35 67 13 392 145 96 64 128 256), losses := [] }

theorem u998 : Upper (D 3) (R 3) [34,65,9,384,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b998
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b999 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 392 176 33 84 212 340), lower := (rows 35 67 13 392 176 33 64 128 256), losses := [] }

theorem u999 : Upper (D 3) (R 3) [34,65,9,384,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b999
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1000 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 67 13 392 176 36 81 209 337), lower := (rows 35 67 13 392 176 36 64 128 256), losses := [] }

theorem u1000 : Upper (D 3) (R 3) [34,65,9,384,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1000
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1001 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 35 67 13 392 176 48 69 197 325), lower := (rows 35 67 13 392 176 48 64 128 256), losses := [] }

theorem u1001 : Upper (D 3) (R 3) [34,65,9,384,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1001
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1002 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 392 176 96 85 149 277), lower := (rows 35 67 13 392 176 96 64 128 256), losses := [] }

theorem u1002 : Upper (D 3) (R 3) [34,65,9,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1002
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1003 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 392 208 33 116 180 308), lower := (rows 35 67 13 392 208 33 64 128 256), losses := [] }

theorem u1003 : Upper (D 3) (R 3) [34,65,9,384,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1003
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1004 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 13 392 208 36 113 177 305), lower := (rows 35 67 13 392 208 36 64 128 256), losses := [] }

theorem u1004 : Upper (D 3) (R 3) [34,65,9,384,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1004
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1005 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 13 392 208 48 101 165 293), lower := (rows 35 67 13 392 208 48 64 128 256), losses := [] }

theorem u1005 : Upper (D 3) (R 3) [34,65,9,384,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1005
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1006 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 67 28 137 273 36 224 224 480), lower := (rows 35 67 28 137 273 36 64 128 256), losses := [] }

theorem u1006 : Upper (D 3) (R 3) [34,65,24,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1006
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1007 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 28 137 273 96 228 164 420), lower := (rows 35 67 28 137 273 96 64 128 256), losses := [] }

theorem u1007 : Upper (D 3) (R 3) [34,65,24,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1007
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1008 : Route 9 := (fun mask => (mask,id))

def c1008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1008 : Upper (D 3) (R 3) [34,65,24,129,257,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,257,128] 13 (by decide) (choices 1) [4,32] r1008 c1008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u161
  · exact u162

def b1009 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 137 276 33 224 224 480), lower := (rows 35 67 28 137 276 33 64 128 256), losses := [] }

theorem u1009 : Upper (D 3) (R 3) [34,65,24,129,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1009
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1010 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 28 137 276 96 225 161 417), lower := (rows 35 67 28 137 276 96 64 128 256), losses := [] }

theorem u1010 : Upper (D 3) (R 3) [34,65,24,129,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1010
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1011 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 137 276 160 97 225 353), lower := (rows 35 67 28 137 276 160 64 128 256), losses := [] }

theorem u1011 : Upper (D 3) (R 3) [34,65,24,129,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1011
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1012 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 137 304 33 196 196 452), lower := (rows 35 67 28 137 304 33 64 128 256), losses := [] }

theorem u1012 : Upper (D 3) (R 3) [34,65,24,129,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1012
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1013 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 28 137 304 36 193 193 449), lower := (rows 35 67 28 137 304 36 64 128 256), losses := [] }

theorem u1013 : Upper (D 3) (R 3) [34,65,24,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1013
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1014 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 28 137 304 96 197 133 389), lower := (rows 35 67 28 137 304 96 64 128 256), losses := [] }

theorem u1014 : Upper (D 3) (R 3) [34,65,24,129,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1014
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1015 : Route 9 := (fun mask => (mask,id))

def c1015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1015 : Upper (D 3) (R 3) [34,65,24,129,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,288,128] 13 (by decide) (choices 1) [1,4] r1015 c1015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u163
  · exact u164

def b1016 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 137 336 33 228 164 420), lower := (rows 35 67 28 137 336 33 64 128 256), losses := [] }

theorem u1016 : Upper (D 3) (R 3) [34,65,24,129,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1016
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1017 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 28 137 336 36 225 161 417), lower := (rows 35 67 28 137 336 36 64 128 256), losses := [] }

theorem u1017 : Upper (D 3) (R 3) [34,65,24,129,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1017
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1018 : Route 9 := (fun mask => (mask,id))

def c1018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1018 : Upper (D 3) (R 3) [34,65,24,129,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,320,128] 13 (by decide) (choices 1) [1,4,32] r1018 c1018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u165
  · exact u166
  · exact u167

def b1019 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 140 273 33 224 224 480), lower := (rows 35 67 28 140 273 33 64 128 256), losses := [] }

theorem u1019 : Upper (D 3) (R 3) [34,65,24,132,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1019
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1019
end Delivery.IrregularNine14.P03
