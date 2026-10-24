import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0004

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1020 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 76 392 304 48 101 165 293), lower := (rows 35 194 76 392 304 48 64 128 256), losses := [] }

theorem u1020 : Upper (D 10) (R 10) [34,192,72,384,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1020 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1021 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 37, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 100 168 273 36 344 408 280), lower := (rows 35 194 100 168 273 36 64 128 256), losses := [] }

theorem u1021 : Upper (D 10) (R 10) [34,192,96,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1021 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1022 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 100 168 273 48 332 396 268), lower := (rows 35 194 100 168 273 48 64 128 256), losses := [] }

theorem u1022 : Upper (D 10) (R 10) [34,192,96,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1022 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1023 : Route 9 := (fun mask => (mask,id))

def c1023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1023 : Upper (D 10) (R 10) [34,192,96,160,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,96,160,257,256] 13 (by decide) (choices 1) [4,8,16] r1023 c1023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u250
  · exact u251
  · exact u252

def b1024 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 33, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 100 168 276 33 344 408 280), lower := (rows 35 194 100 168 276 33 64 128 256), losses := [] }

theorem u1024 : Upper (D 10) (R 10) [34,192,96,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1024 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1025 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 41, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 100 168 276 40 337 401 273), lower := (rows 35 194 100 168 276 40 64 128 256), losses := [] }

theorem u1025 : Upper (D 10) (R 10) [34,192,96,160,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1025 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1026 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 100 168 276 48 329 393 265), lower := (rows 35 194 100 168 276 48 64 128 256), losses := [] }

theorem u1026 : Upper (D 10) (R 10) [34,192,96,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1026 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1027 : Route 9 := (fun mask => (mask,id))

def c1027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1027 : Upper (D 10) (R 10) [34,192,96,160,260,256] 13 := by
  apply FastRouting.sound _ _ [34,192,96,160,260,256] 13 (by decide) (choices 1) [1,8,16] r1027 c1027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u253
  · exact u254
  · exact u255

def b1028 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 100 265 276 40 240 176 432), lower := (rows 35 194 100 265 276 40 64 128 256), losses := [] }

theorem u1028 : Upper (D 10) (R 10) [34,192,96,257,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1028 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1029 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 100 265 276 48 232 168 424), lower := (rows 35 194 100 265 276 48 64 128 256), losses := [] }

theorem u1029 : Upper (D 10) (R 10) [34,192,96,257,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1029 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1030 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 35 194 100 265 276 160 120 184 312), lower := (rows 35 194 100 265 276 160 64 128 256), losses := [] }

theorem u1030 : Upper (D 10) (R 10) [34,192,96,257,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1030 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1031 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 100 265 304 36 216 152 408), lower := (rows 35 194 100 265 304 36 64 128 256), losses := [] }

theorem u1031 : Upper (D 10) (R 10) [34,192,96,257,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1031 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1032 : PairBound 9 := { available := 148, camps := [{ cop := 4, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 100 265 304 40 212 148 404), lower := (rows 35 194 100 265 304 40 64 128 256), losses := [] }

theorem u1032 : Upper (D 10) (R 10) [34,192,96,257,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1032 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1033 : PairBound 9 := { available := 140, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 100 265 304 48 204 140 396), lower := (rows 35 194 100 265 304 48 64 128 256), losses := [] }

theorem u1033 : Upper (D 10) (R 10) [34,192,96,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1033 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1034 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 35 194 100 265 304 160 92 156 284), lower := (rows 35 194 100 265 304 160 64 128 256), losses := [] }

theorem u1034 : Upper (D 10) (R 10) [34,192,96,257,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1034 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1035 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 100 265 400 36 120 184 312), lower := (rows 35 194 100 265 400 36 64 128 256), losses := [] }

theorem u1035 : Upper (D 10) (R 10) [34,192,96,257,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1035 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1036 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 100 265 400 40 116 180 308), lower := (rows 35 194 100 265 400 40 64 128 256), losses := [] }

theorem u1036 : Upper (D 10) (R 10) [34,192,96,257,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1036 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1037 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 100 265 400 48 108 172 300), lower := (rows 35 194 100 265 400 48 64 128 256), losses := [] }

theorem u1037 : Upper (D 10) (R 10) [34,192,96,257,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1037 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1038 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 100 268 304 33 216 152 408), lower := (rows 35 194 100 268 304 33 64 128 256), losses := [] }

theorem u1038 : Upper (D 10) (R 10) [34,192,96,260,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1038 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1039 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 195, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 100 268 304 40 209 145 401), lower := (rows 35 194 100 268 304 40 64 128 256), losses := [] }

theorem u1039 : Upper (D 10) (R 10) [34,192,96,260,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1039 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1040 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 100 268 304 48 201 137 393), lower := (rows 35 194 100 268 304 48 64 128 256), losses := [] }

theorem u1040 : Upper (D 10) (R 10) [34,192,96,260,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1040 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1041 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 35 194 100 268 304 160 89 153 281), lower := (rows 35 194 100 268 304 160 64 128 256), losses := [] }

theorem u1041 : Upper (D 10) (R 10) [34,192,96,260,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1041 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1042 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 100 268 400 33 120 184 312), lower := (rows 35 194 100 268 400 33 64 128 256), losses := [] }

theorem u1042 : Upper (D 10) (R 10) [34,192,96,260,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1042 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1043 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 100 268 400 40 113 177 305), lower := (rows 35 194 100 268 400 40 64 128 256), losses := [] }

theorem u1043 : Upper (D 10) (R 10) [34,192,96,260,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1043 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1044 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 100 268 400 48 105 169 297), lower := (rows 35 194 100 268 400 48 64 128 256), losses := [] }

theorem u1044 : Upper (D 10) (R 10) [34,192,96,260,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1044 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1045 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 100 296 400 33 92 156 284), lower := (rows 35 194 100 296 400 33 64 128 256), losses := [] }

theorem u1045 : Upper (D 10) (R 10) [34,192,96,288,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1045 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1046 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 100 296 400 36 89 153 281), lower := (rows 35 194 100 296 400 36 64 128 256), losses := [] }

theorem u1046 : Upper (D 10) (R 10) [34,192,96,288,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1046 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1047 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 100 296 400 40 85 149 277), lower := (rows 35 194 100 296 400 40 64 128 256), losses := [] }

theorem u1047 : Upper (D 10) (R 10) [34,192,96,288,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1047 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1048 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 100 296 400 48 77 141 269), lower := (rows 35 194 100 296 400 48 64 128 256), losses := [] }

theorem u1048 : Upper (D 10) (R 10) [34,192,96,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1048 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1049 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 268 104 176 33 368 432 304), lower := (rows 67 134 268 104 176 33 64 128 256), losses := [] }

theorem u1049 : Upper (D 10) (R 10) [66,132,264,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1049 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1050 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 268 104 176 48 353 417 289), lower := (rows 67 134 268 104 176 48 64 128 256), losses := [] }

theorem u1050 : Upper (D 10) (R 10) [66,132,264,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1050 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1051 : Route 9 := (fun mask => (mask,id))

def c1051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1051 : Upper (D 10) (R 10) [66,132,264,96,160,256] 13 := by
  apply FastRouting.sound _ _ [66,132,264,96,160,256] 13 (by decide) (choices 1) [1,16,32] r1051 c1051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u256
  · exact u257
  · exact u258

def b1052 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 268 104 304 33 240 176 432), lower := (rows 67 134 268 104 304 33 64 128 256), losses := [] }

theorem u1052 : Upper (D 10) (R 10) [66,132,264,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1052 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1053 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 268 104 304 48 225 161 417), lower := (rows 67 134 268 104 304 48 64 128 256), losses := [] }

theorem u1053 : Upper (D 10) (R 10) [66,132,264,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1053 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1054 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(3,8),(4,6)], upper := (rows 67 134 268 104 304 160 113 177 305), lower := (rows 67 134 268 104 304 160 64 128 256), losses := [{ target := 8, region := (rows 1 2 4 9 16 162 64 128 0), good := (rows 107 166 12 104 48 160 64 160 0) }] }

theorem u1054 : Upper (D 10) (R 10) [66,132,264,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1054 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1055 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 268 104 400 33 112 176 304), lower := (rows 67 134 268 104 400 33 64 128 256), losses := [] }

theorem u1055 : Upper (D 10) (R 10) [66,132,264,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1055 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1056 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 268 104 400 48 97 161 289), lower := (rows 67 134 268 104 400 48 64 128 256), losses := [] }

theorem u1056 : Upper (D 10) (R 10) [66,132,264,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1056 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1057 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 292 88 176 33 360 424 296), lower := (rows 67 134 292 88 176 33 64 128 256), losses := [] }

theorem u1057 : Upper (D 10) (R 10) [66,132,288,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1057 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1058 : Route 9 := (fun mask => (mask,id))

def c1058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1058 : Upper (D 10) (R 10) [66,132,288,80,160,8] 13 := by
  apply FastRouting.sound _ _ [66,132,288,80,160,8] 13 (by decide) (choices 1) [1,32,256] r1058 c1058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u259
  · exact u260
  · exact u261

def b1059 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 219, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 67 134 292 88 176 288 105 169 297), lower := (rows 67 134 292 88 176 288 64 128 256), losses := [] }

theorem u1059 : Upper (D 10) (R 10) [66,132,288,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1059 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1060 : Route 9 := (fun mask => (mask,id))

def c1060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1060 : Upper (D 10) (R 10) [66,132,288,80,384,1] 13 := by
  apply FastRouting.sound _ _ [66,132,288,80,384,1] 13 (by decide) (choices 1) [8,32] r1060 c1060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u262
  · exact u263

def b1061 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8)], upper := (rows 67 134 292 88 400 40 97 161 289), lower := (rows 67 134 292 88 400 40 64 128 256), losses := [] }

theorem u1061 : Upper (D 10) (R 10) [66,132,288,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1061 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1062 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 104 152 33 368 432 304), lower := (rows 67 134 292 104 152 33 64 128 256), losses := [] }

theorem u1062 : Upper (D 10) (R 10) [66,132,288,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1062 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1063 : Route 9 := (fun mask => (mask,id))

def c1063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1063 : Upper (D 10) (R 10) [66,132,288,96,136,16] 13 := by
  apply FastRouting.sound _ _ [66,132,288,96,136,16] 13 (by decide) (choices 1) [1,32,256] r1063 c1063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u264
  · exact u265
  · exact u266

def b1064 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 219, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 67 134 292 104 152 288 113 177 305), lower := (rows 67 134 292 104 152 288 64 128 256), losses := [] }

theorem u1064 : Upper (D 10) (R 10) [66,132,288,96,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1064 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1065 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 104 176 33 344 408 280), lower := (rows 67 134 292 104 176 33 64 128 256), losses := [] }

theorem u1065 : Upper (D 10) (R 10) [66,132,288,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1065 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1066 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 134 292 104 176 40 337 401 273), lower := (rows 67 134 292 104 176 40 64 128 256), losses := [] }

theorem u1066 : Upper (D 10) (R 10) [66,132,288,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1066 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1067 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 292 104 176 48 329 393 265), lower := (rows 67 134 292 104 176 48 64 128 256), losses := [] }

theorem u1067 : Upper (D 10) (R 10) [66,132,288,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1067 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1068 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 219, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 67 134 292 104 176 288 89 153 281), lower := (rows 67 134 292 104 176 288 64 128 256), losses := [] }

theorem u1068 : Upper (D 10) (R 10) [66,132,288,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1068 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1069 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 104 280 33 240 176 432), lower := (rows 67 134 292 104 280 33 64 128 256), losses := [] }

theorem u1069 : Upper (D 10) (R 10) [66,132,288,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1069 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1070 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8)], upper := (rows 67 134 292 104 280 48 225 161 417), lower := (rows 67 134 292 104 280 48 64 128 256), losses := [] }

theorem u1070 : Upper (D 10) (R 10) [66,132,288,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1070 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1071 : Route 9 := (fun mask => (mask,id))

def c1071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1071 : Upper (D 10) (R 10) [66,132,288,96,264,128] 13 := by
  apply FastRouting.sound _ _ [66,132,288,96,264,128] 13 (by decide) (choices 1) [1,16,32] r1071 c1071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u267
  · exact u268
  · exact u269

def b1072 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 104 400 33 120 184 312), lower := (rows 67 134 292 104 400 33 64 128 256), losses := [] }

theorem u1072 : Upper (D 10) (R 10) [66,132,288,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1072 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1073 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 134 292 104 400 40 113 177 305), lower := (rows 67 134 292 104 400 40 64 128 256), losses := [] }

theorem u1073 : Upper (D 10) (R 10) [66,132,288,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1073 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1074 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 203, targets := 256 }], pairs := [(0,8)], upper := (rows 67 134 292 104 400 48 105 169 297), lower := (rows 67 134 292 104 400 48 64 128 256), losses := [] }

theorem u1074 : Upper (D 10) (R 10) [66,132,288,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1074 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1075 : Route 9 := (fun mask => (mask,id))

def c1075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1075 : Upper (D 10) (R 10) [66,132,288,144,320,1] 13 := by
  apply FastRouting.sound _ _ [66,132,288,144,320,1] 13 (by decide) (choices 1) [8,32] r1075 c1075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u270
  · exact u271

def b1076 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8)], upper := (rows 67 134 292 152 336 40 97 161 289), lower := (rows 67 134 292 152 336 40 64 128 256), losses := [] }

theorem u1076 : Upper (D 10) (R 10) [66,132,288,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1076 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1077 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 340, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 292 168 280 33 112 240 368), lower := (rows 67 134 292 168 280 33 64 128 256), losses := [] }

theorem u1077 : Upper (D 10) (R 10) [66,132,288,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1077 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1078 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8)], upper := (rows 67 134 292 168 280 48 97 225 353), lower := (rows 67 134 292 168 280 48 64 128 256), losses := [] }

theorem u1078 : Upper (D 10) (R 10) [66,132,288,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1078 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1079 : Route 9 := (fun mask => (mask,id))

def c1079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1079 : Upper (D 10) (R 10) [66,132,288,160,264,64] 13 := by
  apply FastRouting.sound _ _ [66,132,288,160,264,64] 13 (by decide) (choices 1) [1,16,32] r1079 c1079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u272
  · exact u273
  · exact u274

#print axioms u1079
end Delivery.IrregularNine14.P10
