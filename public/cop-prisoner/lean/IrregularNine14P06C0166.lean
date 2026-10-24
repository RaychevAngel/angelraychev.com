import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0019

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9960 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 44 336 33 90 154 282), lower := (rows 7 35 196 44 336 33 64 128 256), losses := [] }

theorem u9960 : Upper (D 6) (R 6) [6,33,192,36,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9960
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9961 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 44 336 34 89 153 281), lower := (rows 7 35 196 44 336 34 64 128 256), losses := [] }

theorem u9961 : Upper (D 6) (R 6) [6,33,192,36,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9961
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9962 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 44 336 40 83 147 275), lower := (rows 7 35 196 44 336 40 64 128 256), losses := [] }

theorem u9962 : Upper (D 6) (R 6) [6,33,192,36,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9962
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9963 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 44 336 48 75 139 267), lower := (rows 7 35 196 44 336 48 64 128 256), losses := [] }

theorem u9963 : Upper (D 6) (R 6) [6,33,192,36,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9963
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9964 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 35 196 56 81 34 332 396 268), lower := (rows 7 35 196 56 81 34 64 128 256), losses := [] }

theorem u9964 : Upper (D 6) (R 6) [6,33,192,48,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9964
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9965 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 56 81 36 330 394 266), lower := (rows 7 35 196 56 81 36 64 128 256), losses := [] }

theorem u9965 : Upper (D 6) (R 6) [6,33,192,48,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9965
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9966 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 35 196 56 81 40 326 390 262), lower := (rows 7 35 196 56 81 40 64 128 256), losses := [] }

theorem u9966 : Upper (D 6) (R 6) [6,33,192,48,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9966
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9967 : Route 9 := (fun mask => (mask,id))

def c9967 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9967 : Upper (D 6) (R 6) [6,33,192,48,65,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,65,256] 13 (by decide) (choices 1) [2,4,8] r9967 c9967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1148
  · exact u1149
  · exact u1150

def b9968 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 56 82 33 332 396 268), lower := (rows 7 35 196 56 82 33 64 128 256), losses := [] }

theorem u9968 : Upper (D 6) (R 6) [6,33,192,48,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9968
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9969 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 56 82 36 329 393 265), lower := (rows 7 35 196 56 82 36 64 128 256), losses := [] }

theorem u9969 : Upper (D 6) (R 6) [6,33,192,48,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9969
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9970 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 56 82 40 325 389 261), lower := (rows 7 35 196 56 82 40 64 128 256), losses := [] }

theorem u9970 : Upper (D 6) (R 6) [6,33,192,48,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9970
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9971 : Route 9 := (fun mask => (mask,id))

def c9971 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9971 : Upper (D 6) (R 6) [6,33,192,48,66,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,66,256] 13 (by decide) (choices 1) [1,4,8] r9971 c9971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1151
  · exact u1152
  · exact u1153

def b9972 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 35 196 56 273 34 76 204 332), lower := (rows 7 35 196 56 273 34 64 128 256), losses := [] }

theorem u9972 : Upper (D 6) (R 6) [6,33,192,48,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9972
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9973 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 56 273 36 74 202 330), lower := (rows 7 35 196 56 273 36 64 128 256), losses := [] }

theorem u9973 : Upper (D 6) (R 6) [6,33,192,48,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9973
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9974 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 35 196 56 273 40 70 198 326), lower := (rows 7 35 196 56 273 40 64 128 256), losses := [] }

theorem u9974 : Upper (D 6) (R 6) [6,33,192,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9974
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9975 : PairBound 9 := { available := 14, camps := [], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 35 196 56 273 96 78 142 270), lower := (rows 7 35 196 56 273 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 224 56 275 96 96 128 256) },{ target := 6, region := (rows 1 2 4 10 19 32 0 129 257), good := (rows 415 443 132 56 401 32 0 128 256) }] }

theorem u9975 : Upper (D 6) (R 6) [6,33,192,48,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9975
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9976 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 56 274 33 76 204 332), lower := (rows 7 35 196 56 274 33 64 128 256), losses := [] }

theorem u9976 : Upper (D 6) (R 6) [6,33,192,48,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9976
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9977 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 56 274 36 73 201 329), lower := (rows 7 35 196 56 274 36 64 128 256), losses := [] }

theorem u9977 : Upper (D 6) (R 6) [6,33,192,48,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9977
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9978 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 56 274 40 69 197 325), lower := (rows 7 35 196 56 274 40 64 128 256), losses := [] }

theorem u9978 : Upper (D 6) (R 6) [6,33,192,48,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9978
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9979 : PairBound 9 := { available := 13, camps := [], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 35 196 56 274 96 77 141 269), lower := (rows 7 35 196 56 274 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 224 56 274 96 96 128 256) },{ target := 6, region := (rows 1 2 4 10 19 32 0 129 257), good := (rows 415 443 132 56 282 32 0 128 256) }] }

theorem u9979 : Upper (D 6) (R 6) [6,33,192,48,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9979
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9980 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 56 276 33 74 202 330), lower := (rows 7 35 196 56 276 33 64 128 256), losses := [] }

theorem u9980 : Upper (D 6) (R 6) [6,33,192,48,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9980
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9981 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 56 276 34 73 201 329), lower := (rows 7 35 196 56 276 34 64 128 256), losses := [] }

theorem u9981 : Upper (D 6) (R 6) [6,33,192,48,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9981
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9982 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 56 276 40 67 195 323), lower := (rows 7 35 196 56 276 40 64 128 256), losses := [] }

theorem u9982 : Upper (D 6) (R 6) [6,33,192,48,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9982
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9983 : PairBound 9 := { available := 11, camps := [], pairs := [(1,2),(3,0),(3,1)], upper := (rows 7 35 196 56 276 96 75 139 267), lower := (rows 7 35 196 56 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 128 256), good := (rows 38 34 228 56 316 96 96 128 256) },{ target := 1, region := (rows 1 0 4 24 16 100 64 128 256), good := (rows 37 33 228 56 316 96 96 128 256) },{ target := 2, region := (rows 1 3 0 24 16 100 64 128 256), good := (rows 35 35 224 56 312 96 96 128 256) }] }

theorem u9983 : Upper (D 6) (R 6) [6,33,192,48,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9983
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9984 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 56 280 33 70 198 326), lower := (rows 7 35 196 56 280 33 64 128 256), losses := [] }

theorem u9984 : Upper (D 6) (R 6) [6,33,192,48,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9984
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9985 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 56 280 34 69 197 325), lower := (rows 7 35 196 56 280 34 64 128 256), losses := [] }

theorem u9985 : Upper (D 6) (R 6) [6,33,192,48,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9985
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9986 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 35 196 56 280 36 67 195 323), lower := (rows 7 35 196 56 280 36 64 128 256), losses := [] }

theorem u9986 : Upper (D 6) (R 6) [6,33,192,48,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9986
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9987 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(1,2),(2,5)], upper := (rows 7 35 196 56 280 96 71 135 263), lower := (rows 7 35 196 56 280 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 224 56 280 96 96 128 256) }] }

theorem u9987 : Upper (D 6) (R 6) [6,33,192,48,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9987
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9988 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 56 336 33 78 142 270), lower := (rows 7 35 196 56 336 33 64 128 256), losses := [] }

theorem u9988 : Upper (D 6) (R 6) [6,33,192,48,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9988
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9989 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 56 336 34 77 141 269), lower := (rows 7 35 196 56 336 34 64 128 256), losses := [] }

theorem u9989 : Upper (D 6) (R 6) [6,33,192,48,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9989
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9990 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 56 336 36 75 139 267), lower := (rows 7 35 196 56 336 36 64 128 256), losses := [] }

theorem u9990 : Upper (D 6) (R 6) [6,33,192,48,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9990
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9991 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 56 336 40 71 135 263), lower := (rows 7 35 196 56 336 40 64 128 256), losses := [] }

theorem u9991 : Upper (D 6) (R 6) [6,33,192,48,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9991
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9992 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 73 274 36 120 184 312), lower := (rows 7 35 196 73 274 36 64 128 256), losses := [] }

theorem u9992 : Upper (D 6) (R 6) [6,33,192,65,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9992
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9993 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 196 73 274 40 116 180 308), lower := (rows 7 35 196 73 274 40 64 128 256), losses := [] }

theorem u9993 : Upper (D 6) (R 6) [6,33,192,65,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9993
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9994 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 73 274 48 108 172 300), lower := (rows 7 35 196 73 274 48 64 128 256), losses := [] }

theorem u9994 : Upper (D 6) (R 6) [6,33,192,65,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9994
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9995 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 73 276 34 120 184 312), lower := (rows 7 35 196 73 276 34 64 128 256), losses := [] }

theorem u9995 : Upper (D 6) (R 6) [6,33,192,65,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9995
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9996 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 196 73 276 40 114 178 306), lower := (rows 7 35 196 73 276 40 64 128 256), losses := [] }

theorem u9996 : Upper (D 6) (R 6) [6,33,192,65,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9996
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9997 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 73 276 48 106 170 298), lower := (rows 7 35 196 73 276 48 64 128 256), losses := [] }

theorem u9997 : Upper (D 6) (R 6) [6,33,192,65,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9997
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9998 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 73 280 34 116 180 308), lower := (rows 7 35 196 73 280 34 64 128 256), losses := [] }

theorem u9998 : Upper (D 6) (R 6) [6,33,192,65,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9998
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9999 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 73 280 36 114 178 306), lower := (rows 7 35 196 73 280 36 64 128 256), losses := [] }

theorem u9999 : Upper (D 6) (R 6) [6,33,192,65,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9999
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10000 : Route 9 := (fun mask => (mask,id))

def c10000 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10000 : Upper (D 6) (R 6) [6,33,192,65,264,16] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,264,16] 13 (by decide) (choices 1) [2,4,32] r10000 c10000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1154
  · exact u1155
  · exact u1156

def b10001 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 73 304 34 92 156 284), lower := (rows 7 35 196 73 304 34 64 128 256), losses := [] }

theorem u10001 : Upper (D 6) (R 6) [6,33,192,65,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10001
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10002 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 73 304 36 90 154 282), lower := (rows 7 35 196 73 304 36 64 128 256), losses := [] }

theorem u10002 : Upper (D 6) (R 6) [6,33,192,65,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10002
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10003 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 196 73 304 40 86 150 278), lower := (rows 7 35 196 73 304 40 64 128 256), losses := [] }

theorem u10003 : Upper (D 6) (R 6) [6,33,192,65,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10003
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10004 : PairBound 9 := { available := 14, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 196 73 304 48 78 142 270), lower := (rows 7 35 196 73 304 48 64 128 256), losses := [] }

theorem u10004 : Upper (D 6) (R 6) [6,33,192,65,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10004
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10005 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 74 273 36 120 184 312), lower := (rows 7 35 196 74 273 36 64 128 256), losses := [] }

theorem u10005 : Upper (D 6) (R 6) [6,33,192,66,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10005
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10006 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 35 196 74 273 40 116 180 308), lower := (rows 7 35 196 74 273 40 64 128 256), losses := [] }

theorem u10006 : Upper (D 6) (R 6) [6,33,192,66,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10006
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10007 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 74 273 48 108 172 300), lower := (rows 7 35 196 74 273 48 64 128 256), losses := [] }

theorem u10007 : Upper (D 6) (R 6) [6,33,192,66,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10007
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10008 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 74 276 33 120 184 312), lower := (rows 7 35 196 74 276 33 64 128 256), losses := [] }

theorem u10008 : Upper (D 6) (R 6) [6,33,192,66,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10008
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10009 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 35 196 74 276 40 113 177 305), lower := (rows 7 35 196 74 276 40 64 128 256), losses := [] }

theorem u10009 : Upper (D 6) (R 6) [6,33,192,66,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10009
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10010 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 74 276 48 105 169 297), lower := (rows 7 35 196 74 276 48 64 128 256), losses := [] }

theorem u10010 : Upper (D 6) (R 6) [6,33,192,66,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10010
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10011 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 74 280 33 116 180 308), lower := (rows 7 35 196 74 280 33 64 128 256), losses := [] }

theorem u10011 : Upper (D 6) (R 6) [6,33,192,66,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10011
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10012 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 74 280 36 113 177 305), lower := (rows 7 35 196 74 280 36 64 128 256), losses := [] }

theorem u10012 : Upper (D 6) (R 6) [6,33,192,66,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10012
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10013 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 196, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 35 196 74 280 48 101 165 293), lower := (rows 7 35 196 74 280 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 15 8 24 56 66 130 258), good := (rows 453 485 196 508 316 48 64 128 256) }] }

theorem u10013 : Upper (D 6) (R 6) [6,33,192,66,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10013
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10014 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 74 304 33 92 156 284), lower := (rows 7 35 196 74 304 33 64 128 256), losses := [] }

theorem u10014 : Upper (D 6) (R 6) [6,33,192,66,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10014
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10015 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 74 304 36 89 153 281), lower := (rows 7 35 196 74 304 36 64 128 256), losses := [] }

theorem u10015 : Upper (D 6) (R 6) [6,33,192,66,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10015
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10016 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 35 196 74 304 40 85 149 277), lower := (rows 7 35 196 74 304 40 64 128 256), losses := [] }

theorem u10016 : Upper (D 6) (R 6) [6,33,192,66,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10016
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10017 : PairBound 9 := { available := 13, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 196 74 304 48 77 141 269), lower := (rows 7 35 196 74 304 48 64 128 256), losses := [] }

theorem u10017 : Upper (D 6) (R 6) [6,33,192,66,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10017
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10018 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 88 273 34 108 172 300), lower := (rows 7 35 196 88 273 34 64 128 256), losses := [] }

theorem u10018 : Upper (D 6) (R 6) [6,33,192,80,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10018
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10019 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 88 273 36 106 170 298), lower := (rows 7 35 196 88 273 36 64 128 256), losses := [] }

theorem u10019 : Upper (D 6) (R 6) [6,33,192,80,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10019
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10019
end Delivery.IrregularNine14.P06
