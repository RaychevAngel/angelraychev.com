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

def r10020 : Route 9 := (fun mask => (mask,id))

def c10020 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10020 : Upper (D 6) (R 6) [6,33,192,80,257,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,257,8] 13 (by decide) (choices 1) [2,4,32] r10020 c10020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1157
  · exact u1158
  · exact u1159

def b10021 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 88 274 33 108 172 300), lower := (rows 7 35 196 88 274 33 64 128 256), losses := [] }

theorem u10021 : Upper (D 6) (R 6) [6,33,192,80,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10021
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10022 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 88 274 36 105 169 297), lower := (rows 7 35 196 88 274 36 64 128 256), losses := [] }

theorem u10022 : Upper (D 6) (R 6) [6,33,192,80,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10022
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10023 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 196, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 88 274 40 101 165 293), lower := (rows 7 35 196 88 274 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 56 66 130 258), good := (rows 453 485 196 124 508 40 64 128 256) }] }

theorem u10023 : Upper (D 6) (R 6) [6,33,192,80,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10023
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10024 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 88 276 33 106 170 298), lower := (rows 7 35 196 88 276 33 64 128 256), losses := [] }

theorem u10024 : Upper (D 6) (R 6) [6,33,192,80,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10024
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10025 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 88 276 34 105 169 297), lower := (rows 7 35 196 88 276 34 64 128 256), losses := [] }

theorem u10025 : Upper (D 6) (R 6) [6,33,192,80,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10025
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10026 : Route 9 := (fun mask => (mask,id))

def c10026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10026 : Upper (D 6) (R 6) [6,33,192,80,260,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,260,8] 13 (by decide) (choices 1) [1,2,32] r10026 c10026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1160
  · exact u1161
  · exact u1162

def b10027 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 88 280 33 102 166 294), lower := (rows 7 35 196 88 280 33 64 128 256), losses := [] }

theorem u10027 : Upper (D 6) (R 6) [6,33,192,80,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10027
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10028 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 88 280 34 101 165 293), lower := (rows 7 35 196 88 280 34 64 128 256), losses := [] }

theorem u10028 : Upper (D 6) (R 6) [6,33,192,80,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10028
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10029 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 88 280 36 99 163 291), lower := (rows 7 35 196 88 280 36 64 128 256), losses := [] }

theorem u10029 : Upper (D 6) (R 6) [6,33,192,80,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10029
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10030 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 88 304 33 78 142 270), lower := (rows 7 35 196 88 304 33 64 128 256), losses := [] }

theorem u10030 : Upper (D 6) (R 6) [6,33,192,80,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10030
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10031 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 88 304 34 77 141 269), lower := (rows 7 35 196 88 304 34 64 128 256), losses := [] }

theorem u10031 : Upper (D 6) (R 6) [6,33,192,80,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10031
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10032 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 88 304 36 75 139 267), lower := (rows 7 35 196 88 304 36 64 128 256), losses := [] }

theorem u10032 : Upper (D 6) (R 6) [6,33,192,80,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10032
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10033 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 88 304 40 71 135 263), lower := (rows 7 35 196 88 304 40 64 128 256), losses := [] }

theorem u10033 : Upper (D 6) (R 6) [6,33,192,80,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10033
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10034 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 104 273 34 92 156 284), lower := (rows 7 35 196 104 273 34 64 128 256), losses := [] }

theorem u10034 : Upper (D 6) (R 6) [6,33,192,96,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10034
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10035 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 40, targets := 1 }], pairs := [(3,0),(3,2),(4,2)], upper := (rows 7 35 196 104 273 36 90 154 282), lower := (rows 7 35 196 104 273 36 64 128 256), losses := [] }

theorem u10035 : Upper (D 6) (R 6) [6,33,192,96,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10035
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10036 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 104 273 40 86 150 278), lower := (rows 7 35 196 104 273 40 64 128 256), losses := [] }

theorem u10036 : Upper (D 6) (R 6) [6,33,192,96,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10036
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10037 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 104 273 48 78 142 270), lower := (rows 7 35 196 104 273 48 64 128 256), losses := [] }

theorem u10037 : Upper (D 6) (R 6) [6,33,192,96,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10037
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10038 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 104 274 33 92 156 284), lower := (rows 7 35 196 104 274 33 64 128 256), losses := [] }

theorem u10038 : Upper (D 6) (R 6) [6,33,192,96,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10038
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10039 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 40, targets := 1 }], pairs := [(3,0),(3,2),(4,2)], upper := (rows 7 35 196 104 274 36 89 153 281), lower := (rows 7 35 196 104 274 36 64 128 256), losses := [] }

theorem u10039 : Upper (D 6) (R 6) [6,33,192,96,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10039
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10040 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 104 274 40 85 149 277), lower := (rows 7 35 196 104 274 40 64 128 256), losses := [] }

theorem u10040 : Upper (D 6) (R 6) [6,33,192,96,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10040
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10041 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 104 274 48 77 141 269), lower := (rows 7 35 196 104 274 48 64 128 256), losses := [] }

theorem u10041 : Upper (D 6) (R 6) [6,33,192,96,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10041
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10042 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 104 276 33 90 154 282), lower := (rows 7 35 196 104 276 33 64 128 256), losses := [] }

theorem u10042 : Upper (D 6) (R 6) [6,33,192,96,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10042
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10043 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 104 276 34 89 153 281), lower := (rows 7 35 196 104 276 34 64 128 256), losses := [] }

theorem u10043 : Upper (D 6) (R 6) [6,33,192,96,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10043
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10044 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 104 276 40 83 147 275), lower := (rows 7 35 196 104 276 40 64 128 256), losses := [] }

theorem u10044 : Upper (D 6) (R 6) [6,33,192,96,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10044
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10045 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 104 276 48 75 139 267), lower := (rows 7 35 196 104 276 48 64 128 256), losses := [] }

theorem u10045 : Upper (D 6) (R 6) [6,33,192,96,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10045
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10046 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 104 280 33 86 150 278), lower := (rows 7 35 196 104 280 33 64 128 256), losses := [] }

theorem u10046 : Upper (D 6) (R 6) [6,33,192,96,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10046
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10047 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 104 280 34 85 149 277), lower := (rows 7 35 196 104 280 34 64 128 256), losses := [] }

theorem u10047 : Upper (D 6) (R 6) [6,33,192,96,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10047
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10048 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 40, targets := 1 }], pairs := [(3,0),(3,2),(4,2)], upper := (rows 7 35 196 104 280 36 83 147 275), lower := (rows 7 35 196 104 280 36 64 128 256), losses := [] }

theorem u10048 : Upper (D 6) (R 6) [6,33,192,96,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10048
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10049 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 104 280 48 71 135 263), lower := (rows 7 35 196 104 280 48 64 128 256), losses := [] }

theorem u10049 : Upper (D 6) (R 6) [6,33,192,96,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10049
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10050 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 88, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 388 25 82 36 104 232 360), lower := (rows 7 35 388 25 82 36 64 128 256), losses := [] }

theorem u10050 : Upper (D 6) (R 6) [6,33,384,17,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10050
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10051 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 388 25 82 40 100 228 356), lower := (rows 7 35 388 25 82 40 64 128 256), losses := [] }

theorem u10051 : Upper (D 6) (R 6) [6,33,384,17,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10051
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10052 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 484, targets := 3 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 7 35 388 25 82 96 108 172 300), lower := (rows 7 35 388 25 82 96 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 112 64 128 256), good := (rows 3 35 384 59 114 96 96 128 256) }] }

theorem u10052 : Upper (D 6) (R 6) [6,33,384,17,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10052
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10053 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 25 84 34 104 232 360), lower := (rows 7 35 388 25 84 34 64 128 256), losses := [] }

theorem u10053 : Upper (D 6) (R 6) [6,33,384,17,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10053
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10054 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 388 25 84 40 98 226 354), lower := (rows 7 35 388 25 84 40 64 128 256), losses := [] }

theorem u10054 : Upper (D 6) (R 6) [6,33,384,17,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10054
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10055 : Route 9 := (fun mask => (mask,id))

def c10055 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10055 : Upper (D 6) (R 6) [6,33,384,17,68,64] 13 := by
  apply FastRouting.sound _ _ [6,33,384,17,68,64] 13 (by decide) (choices 1) [2,8,32] r10055 c10055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1163
  · exact u1164
  · exact u1165

def b10056 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 25 88 34 100 228 356), lower := (rows 7 35 388 25 88 34 64 128 256), losses := [] }

theorem u10056 : Upper (D 6) (R 6) [6,33,384,17,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10056
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10057 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 88, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 388 25 88 36 98 226 354), lower := (rows 7 35 388 25 88 36 64 128 256), losses := [] }

theorem u10057 : Upper (D 6) (R 6) [6,33,384,17,72,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10057
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10058 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 388 25 88 96 102 166 294), lower := (rows 7 35 388 25 88 96 64 128 256), losses := [] }

theorem u10058 : Upper (D 6) (R 6) [6,33,384,17,72,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10058
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10059 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 25 112 34 76 204 332), lower := (rows 7 35 388 25 112 34 64 128 256), losses := [] }

theorem u10059 : Upper (D 6) (R 6) [6,33,384,17,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10059
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10060 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 88, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 388 25 112 36 74 202 330), lower := (rows 7 35 388 25 112 36 64 128 256), losses := [] }

theorem u10060 : Upper (D 6) (R 6) [6,33,384,17,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10060
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10061 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 388 25 112 40 70 198 326), lower := (rows 7 35 388 25 112 40 64 128 256), losses := [] }

theorem u10061 : Upper (D 6) (R 6) [6,33,384,17,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10061
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10062 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 388 25 112 96 78 142 270), lower := (rows 7 35 388 25 112 96 64 128 256), losses := [] }

theorem u10062 : Upper (D 6) (R 6) [6,33,384,17,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10062
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10063 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 88, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 388 26 81 36 104 232 360), lower := (rows 7 35 388 26 81 36 64 128 256), losses := [] }

theorem u10063 : Upper (D 6) (R 6) [6,33,384,18,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10063
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10064 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 35 388 26 81 40 100 228 356), lower := (rows 7 35 388 26 81 40 64 128 256), losses := [] }

theorem u10064 : Upper (D 6) (R 6) [6,33,384,18,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10064
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10065 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 7 35 388 26 81 96 108 172 300), lower := (rows 7 35 388 26 81 96 64 128 256), losses := [] }

theorem u10065 : Upper (D 6) (R 6) [6,33,384,18,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10065
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10066 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 26 84 33 104 232 360), lower := (rows 7 35 388 26 84 33 64 128 256), losses := [] }

theorem u10066 : Upper (D 6) (R 6) [6,33,384,18,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10066
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10067 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 388 26 84 40 97 225 353), lower := (rows 7 35 388 26 84 40 64 128 256), losses := [] }

theorem u10067 : Upper (D 6) (R 6) [6,33,384,18,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10067
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10068 : Route 9 := (fun mask => (mask,id))

def c10068 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10068 : Upper (D 6) (R 6) [6,33,384,18,68,64] 13 := by
  apply FastRouting.sound _ _ [6,33,384,18,68,64] 13 (by decide) (choices 1) [1,8,32] r10068 c10068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1166
  · exact u1167
  · exact u1168

def b10069 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 26 88 33 100 228 356), lower := (rows 7 35 388 26 88 33 64 128 256), losses := [] }

theorem u10069 : Upper (D 6) (R 6) [6,33,384,18,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10069
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10070 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 88, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 388 26 88 36 97 225 353), lower := (rows 7 35 388 26 88 36 64 128 256), losses := [] }

theorem u10070 : Upper (D 6) (R 6) [6,33,384,18,72,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10070
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10071 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 388 26 88 96 101 165 293), lower := (rows 7 35 388 26 88 96 64 128 256), losses := [] }

theorem u10071 : Upper (D 6) (R 6) [6,33,384,18,72,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10071
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10072 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 26 112 33 76 204 332), lower := (rows 7 35 388 26 112 33 64 128 256), losses := [] }

theorem u10072 : Upper (D 6) (R 6) [6,33,384,18,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10072
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10073 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 88, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 388 26 112 36 73 201 329), lower := (rows 7 35 388 26 112 36 64 128 256), losses := [] }

theorem u10073 : Upper (D 6) (R 6) [6,33,384,18,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10073
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10074 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 452, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 35 388 26 112 40 69 197 325), lower := (rows 7 35 388 26 112 40 64 128 256), losses := [] }

theorem u10074 : Upper (D 6) (R 6) [6,33,384,18,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10074
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10075 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 388 26 112 96 77 141 269), lower := (rows 7 35 388 26 112 96 64 128 256), losses := [] }

theorem u10075 : Upper (D 6) (R 6) [6,33,384,18,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10075
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10076 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 28 81 34 104 232 360), lower := (rows 7 35 388 28 81 34 64 128 256), losses := [] }

theorem u10076 : Upper (D 6) (R 6) [6,33,384,20,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10076
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10077 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 388 28 81 40 98 226 354), lower := (rows 7 35 388 28 81 40 64 128 256), losses := [] }

theorem u10077 : Upper (D 6) (R 6) [6,33,384,20,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10077
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10078 : Route 9 := (fun mask => (mask,id))

def c10078 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10078 : Upper (D 6) (R 6) [6,33,384,20,65,64] 13 := by
  apply FastRouting.sound _ _ [6,33,384,20,65,64] 13 (by decide) (choices 1) [2,8,32] r10078 c10078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1169
  · exact u1170
  · exact u1171

def b10079 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 28 82 33 104 232 360), lower := (rows 7 35 388 28 82 33 64 128 256), losses := [] }

theorem u10079 : Upper (D 6) (R 6) [6,33,384,20,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10079
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10079
end Delivery.IrregularNine14.P06
