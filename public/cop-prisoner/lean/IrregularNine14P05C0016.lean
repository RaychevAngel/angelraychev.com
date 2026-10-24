import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0000

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b960 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 56 276 33 72 131 259), lower := (rows 7 74 164 56 276 33 72 128 256), losses := [] }

theorem u960 : Upper (D 5) (R 5) [6,72,160,48,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b960
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r961 : Route 9 := (fun mask => (mask,id))

def c961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u961 : Upper (D 5) (R 5) [6,72,160,48,260,2,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,260,2,1] 13 (by decide) (choices 1) [1,8] r961 c961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u54
  · exact u55

def b962 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 106, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 164 56 276 34 72 129 257), lower := (rows 7 74 164 56 276 34 72 128 256), losses := [] }

theorem u962 : Upper (D 5) (R 5) [6,72,160,48,260,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b962
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b963 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 164 265 28 33 66 176 304), lower := (rows 7 74 164 265 28 33 66 128 256), losses := [] }

theorem u963 : Upper (D 5) (R 5) [6,72,160,257,12,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b963
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b964 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3)], upper := (rows 7 74 164 265 28 33 80 162 290), lower := (rows 7 74 164 265 28 33 80 128 256), losses := [] }

theorem u964 : Upper (D 5) (R 5) [6,72,160,257,12,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b964
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b965 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 164 265 28 33 96 146 274), lower := (rows 7 74 164 265 28 33 96 128 256), losses := [] }

theorem u965 : Upper (D 5) (R 5) [6,72,160,257,12,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b965
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b966 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 180, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 74 164 265 28 34 65 176 304), lower := (rows 7 74 164 265 28 34 65 128 256), losses := [] }

theorem u966 : Upper (D 5) (R 5) [6,72,160,257,12,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b966
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b967 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3)], upper := (rows 7 74 164 265 28 34 80 161 289), lower := (rows 7 74 164 265 28 34 80 128 256), losses := [] }

theorem u967 : Upper (D 5) (R 5) [6,72,160,257,12,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b967
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b968 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 280, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 74 164 265 28 34 96 145 273), lower := (rows 7 74 164 265 28 34 96 128 256), losses := [] }

theorem u968 : Upper (D 5) (R 5) [6,72,160,257,12,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b968
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b969 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 265 28 48 65 162 290), lower := (rows 7 74 164 265 28 48 65 128 256), losses := [] }

theorem u969 : Upper (D 5) (R 5) [6,72,160,257,12,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b969
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b970 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1)], upper := (rows 7 74 164 265 28 48 66 161 289), lower := (rows 7 74 164 265 28 48 66 128 256), losses := [] }

theorem u970 : Upper (D 5) (R 5) [6,72,160,257,12,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b970
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b971 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 264, targets := 32 }], pairs := [(3,5)], upper := (rows 7 74 164 265 28 48 96 131 259), lower := (rows 7 74 164 265 28 48 96 128 256), losses := [] }

theorem u971 : Upper (D 5) (R 5) [6,72,160,257,12,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b971
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b972 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 266 28 33 65 176 304), lower := (rows 7 74 164 266 28 33 65 128 256), losses := [] }

theorem u972 : Upper (D 5) (R 5) [6,72,160,258,12,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b972
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b973 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 164, targets := 2 }], pairs := [(2,1)], upper := (rows 7 74 164 266 28 33 80 161 289), lower := (rows 7 74 164 266 28 33 80 128 256), losses := [] }

theorem u973 : Upper (D 5) (R 5) [6,72,160,258,12,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b973
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b974 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 164 266 28 33 96 145 273), lower := (rows 7 74 164 266 28 33 96 128 256), losses := [] }

theorem u974 : Upper (D 5) (R 5) [6,72,160,258,12,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b974
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b975 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 7 74 164 266 28 48 65 161 289), lower := (rows 7 74 164 266 28 48 65 128 256), losses := [] }

theorem u975 : Upper (D 5) (R 5) [6,72,160,258,12,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b975
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b976 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 264, targets := 32 }], pairs := [(3,5)], upper := (rows 7 74 164 266 28 48 96 129 257), lower := (rows 7 74 164 266 28 48 96 128 256), losses := [] }

theorem u976 : Upper (D 5) (R 5) [6,72,160,258,12,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b976
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b977 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 266 56 33 65 148 276), lower := (rows 7 74 164 266 56 33 65 128 256), losses := [] }

theorem u977 : Upper (D 5) (R 5) [6,72,160,258,40,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b977
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b978 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 266 56 33 68 145 273), lower := (rows 7 74 164 266 56 33 68 128 256), losses := [] }

theorem u978 : Upper (D 5) (R 5) [6,72,160,258,40,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b978
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b979 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 266 56 33 80 133 261), lower := (rows 7 74 164 266 56 33 80 128 256), losses := [] }

theorem u979 : Upper (D 5) (R 5) [6,72,160,258,40,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b979
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b980 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 164 268 25 33 66 176 304), lower := (rows 7 74 164 268 25 33 66 128 256), losses := [] }

theorem u980 : Upper (D 5) (R 5) [6,72,160,260,9,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b980
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b981 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5)], upper := (rows 7 74 164 268 25 33 80 162 290), lower := (rows 7 74 164 268 25 33 80 128 256), losses := [] }

theorem u981 : Upper (D 5) (R 5) [6,72,160,260,9,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b981
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b982 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 164 268 25 33 96 146 274), lower := (rows 7 74 164 268 25 33 96 128 256), losses := [] }

theorem u982 : Upper (D 5) (R 5) [6,72,160,260,9,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b982
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b983 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 268 56 33 65 146 274), lower := (rows 7 74 164 268 56 33 65 128 256), losses := [] }

theorem u983 : Upper (D 5) (R 5) [6,72,160,260,40,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b983
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b984 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 164 268 56 33 66 145 273), lower := (rows 7 74 164 268 56 33 66 128 256), losses := [] }

theorem u984 : Upper (D 5) (R 5) [6,72,160,260,40,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b984
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b985 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 268 56 33 80 131 259), lower := (rows 7 74 164 268 56 33 80 128 256), losses := [] }

theorem u985 : Upper (D 5) (R 5) [6,72,160,260,40,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b985
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b986 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 164 296 25 33 66 148 276), lower := (rows 7 74 164 296 25 33 66 128 256), losses := [] }

theorem u986 : Upper (D 5) (R 5) [6,72,160,288,9,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b986
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b987 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 296 25 33 68 146 274), lower := (rows 7 74 164 296 25 33 68 128 256), losses := [] }

theorem u987 : Upper (D 5) (R 5) [6,72,160,288,9,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b987
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b988 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3)], upper := (rows 7 74 164 296 25 33 80 134 262), lower := (rows 7 74 164 296 25 33 80 128 256), losses := [] }

theorem u988 : Upper (D 5) (R 5) [6,72,160,288,9,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b988
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b989 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 66, targets := 4 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,2),(1,5)], upper := (rows 7 74 164 296 25 34 65 148 276), lower := (rows 7 74 164 296 25 34 65 128 256), losses := [] }

theorem u989 : Upper (D 5) (R 5) [6,72,160,288,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b989
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b990 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 296 25 34 68 145 273), lower := (rows 7 74 164 296 25 34 68 128 256), losses := [] }

theorem u990 : Upper (D 5) (R 5) [6,72,160,288,9,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b990
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b991 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3)], upper := (rows 7 74 164 296 25 34 80 133 261), lower := (rows 7 74 164 296 25 34 80 128 256), losses := [] }

theorem u991 : Upper (D 5) (R 5) [6,72,160,288,9,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b991
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b992 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 388 42 28 33 65 176 304), lower := (rows 7 74 388 42 28 33 65 128 256), losses := [] }

theorem u992 : Upper (D 5) (R 5) [6,72,384,34,12,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b992
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b993 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 420, targets := 2 }], pairs := [(2,1)], upper := (rows 7 74 388 42 28 33 80 161 289), lower := (rows 7 74 388 42 28 33 80 128 256), losses := [] }

theorem u993 : Upper (D 5) (R 5) [6,72,384,34,12,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b993
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b994 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 74, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 388 42 28 33 96 145 273), lower := (rows 7 74 388 42 28 33 96 128 256), losses := [] }

theorem u994 : Upper (D 5) (R 5) [6,72,384,34,12,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b994
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b995 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 42 276 33 65 136 264), lower := (rows 7 82 164 42 276 33 65 128 256), losses := [] }

theorem u995 : Upper (D 5) (R 5) [6,80,160,34,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b995
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r996 : Route 9 := (fun mask => (mask,id))

def c996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u996 : Upper (D 5) (R 5) [6,80,160,34,260,1,8] 13 := by
  apply FastRouting.sound _ _ [6,80,160,34,260,1,8] 13 (by decide) (choices 1) [1,8] r996 c996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u56
  · exact u57

def b997 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 42 280 33 65 140 268), lower := (rows 7 82 164 42 280 33 65 128 256), losses := [] }

theorem u997 : Upper (D 5) (R 5) [6,80,160,34,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b997
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b998 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 82 164 42 280 33 68 137 265), lower := (rows 7 82 164 42 280 33 68 128 256), losses := [] }

theorem u998 : Upper (D 5) (R 5) [6,80,160,34,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b998
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b999 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 82 164 42 280 33 72 133 261), lower := (rows 7 82 164 42 280 33 72 128 256), losses := [] }

theorem u999 : Upper (D 5) (R 5) [6,80,160,34,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b999
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1000 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 82 164 265 28 40 65 162 290), lower := (rows 7 82 164 265 28 40 65 128 256), losses := [] }

theorem u1000 : Upper (D 5) (R 5) [6,80,160,257,12,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1000
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1001 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 82 164 265 28 40 66 161 289), lower := (rows 7 82 164 265 28 40 66 128 256), losses := [] }

theorem u1001 : Upper (D 5) (R 5) [6,80,160,257,12,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1001
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1002 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 82 164 265 28 40 96 131 259), lower := (rows 7 82 164 265 28 40 96 128 256), losses := [] }

theorem u1002 : Upper (D 5) (R 5) [6,80,160,257,12,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1002
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1003 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 82 164 266 25 33 68 168 296), lower := (rows 7 82 164 266 25 33 68 128 256), losses := [] }

theorem u1003 : Upper (D 5) (R 5) [6,80,160,258,9,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1003
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1004 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 266 25 33 72 164 292), lower := (rows 7 82 164 266 25 33 72 128 256), losses := [] }

theorem u1004 : Upper (D 5) (R 5) [6,80,160,258,9,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1004
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1005 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 82 164 266 25 33 96 140 268), lower := (rows 7 82 164 266 25 33 96 128 256), losses := [] }

theorem u1005 : Upper (D 5) (R 5) [6,80,160,258,9,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1005
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1006 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 266 25 40 65 164 292), lower := (rows 7 82 164 266 25 40 65 128 256), losses := [] }

theorem u1006 : Upper (D 5) (R 5) [6,80,160,258,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1006
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1007 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 82 164 266 25 40 68 161 289), lower := (rows 7 82 164 266 25 40 68 128 256), losses := [] }

theorem u1007 : Upper (D 5) (R 5) [6,80,160,258,9,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1007
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1008 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 82 164 266 25 40 96 133 261), lower := (rows 7 82 164 266 25 40 96 128 256), losses := [] }

theorem u1008 : Upper (D 5) (R 5) [6,80,160,258,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1008
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1009 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 82 164 266 28 33 65 168 296), lower := (rows 7 82 164 266 28 33 65 128 256), losses := [] }

theorem u1009 : Upper (D 5) (R 5) [6,80,160,258,12,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1009
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1010 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 164, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 82 164 266 28 33 72 161 289), lower := (rows 7 82 164 266 28 33 72 128 256), losses := [] }

theorem u1010 : Upper (D 5) (R 5) [6,80,160,258,12,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1010
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1011 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 82 164 266 28 33 96 137 265), lower := (rows 7 82 164 266 28 33 96 128 256), losses := [] }

theorem u1011 : Upper (D 5) (R 5) [6,80,160,258,12,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1011
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1012 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 82 164 266 28 40 65 161 289), lower := (rows 7 82 164 266 28 40 65 128 256), losses := [] }

theorem u1012 : Upper (D 5) (R 5) [6,80,160,258,12,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1012
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1013 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 82 164 266 28 40 96 129 257), lower := (rows 7 82 164 266 28 40 96 128 256), losses := [] }

theorem u1013 : Upper (D 5) (R 5) [6,80,160,258,12,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1013
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1014 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 266 56 33 65 140 268), lower := (rows 7 82 164 266 56 33 65 128 256), losses := [] }

theorem u1014 : Upper (D 5) (R 5) [6,80,160,258,40,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1014
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1015 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 82 164 266 56 33 68 137 265), lower := (rows 7 82 164 266 56 33 68 128 256), losses := [] }

theorem u1015 : Upper (D 5) (R 5) [6,80,160,258,40,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1015
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1016 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 82 164 266 56 33 72 133 261), lower := (rows 7 82 164 266 56 33 72 128 256), losses := [] }

theorem u1016 : Upper (D 5) (R 5) [6,80,160,258,40,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1016
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1017 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 268 25 33 66 168 296), lower := (rows 7 82 164 268 25 33 66 128 256), losses := [] }

theorem u1017 : Upper (D 5) (R 5) [6,80,160,260,9,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1017
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1018 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 82 164 268 25 33 72 162 290), lower := (rows 7 82 164 268 25 33 72 128 256), losses := [] }

theorem u1018 : Upper (D 5) (R 5) [6,80,160,260,9,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1018
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1019 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 82 164 268 25 33 96 138 266), lower := (rows 7 82 164 268 25 33 96 128 256), losses := [] }

theorem u1019 : Upper (D 5) (R 5) [6,80,160,260,9,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1019
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1019
end Delivery.IrregularNine14.P05
