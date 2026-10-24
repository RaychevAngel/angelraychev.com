import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0141
import IrregularNine14P07C0142

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25020 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 194 14 88 304 33 195 131 387), lower := (rows 37 194 14 88 304 33 64 128 256), losses := [] }

theorem u25020 : Upper (D 7) (R 7) [36,192,10,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25021 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 194 14 88 304 34 193 129 385), lower := (rows 37 194 14 88 304 34 64 128 256), losses := [] }

theorem u25021 : Upper (D 7) (R 7) [36,192,10,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25022 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(1,5),(4,6)], upper := (rows 37 194 14 88 304 160 67 131 259), lower := (rows 37 194 14 88 304 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 162 64 128 256), good := (rows 37 224 45 88 304 160 64 160 256) }] }

theorem u25022 : Upper (D 7) (R 7) [36,192,10,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25023 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 2, region := 33, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 194 14 88 400 33 99 163 291), lower := (rows 37 194 14 88 400 33 64 128 256), losses := [] }

theorem u25023 : Upper (D 7) (R 7) [36,192,10,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25024 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 194 14 88 400 34 97 161 289), lower := (rows 37 194 14 88 400 34 64 128 256), losses := [] }

theorem u25024 : Upper (D 7) (R 7) [36,192,10,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25025 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 194 14 265 19 48 224 224 480), lower := (rows 37 194 14 265 19 48 64 128 256), losses := [] }

theorem u25025 : Upper (D 7) (R 7) [36,192,10,257,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25025 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25026 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 226, targets := 1 },{ cop := 4, region := 488, targets := 2 }], pairs := [(0,1),(0,7),(1,0),(3,1)], upper := (rows 37 194 14 265 19 96 240 176 432), lower := (rows 37 194 14 265 19 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 114 80 144 272), good := (rows 37 224 45 265 505 96 96 128 256) },{ target := 7, region := (rows 5 2 4 8 20 98 64 0 256), good := (rows 53 98 63 265 51 96 96 0 256) }] }

theorem u25026 : Upper (D 7) (R 7) [36,192,10,257,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25027 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 194 14 265 50 33 208 208 464), lower := (rows 37 194 14 265 50 33 64 128 256), losses := [] }

theorem u25027 : Upper (D 7) (R 7) [36,192,10,257,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25028 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 194 14 265 50 48 193 193 449), lower := (rows 37 194 14 265 50 48 64 128 256), losses := [] }

theorem u25028 : Upper (D 7) (R 7) [36,192,10,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25028 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25029 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 194 14 265 50 96 209 145 401), lower := (rows 37 194 14 265 50 96 64 128 256), losses := [] }

theorem u25029 : Upper (D 7) (R 7) [36,192,10,257,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25030 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 194 14 265 81 34 240 176 432), lower := (rows 37 194 14 265 81 34 64 128 256), losses := [] }

theorem u25030 : Upper (D 7) (R 7) [36,192,10,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25031 : Route 9 := (fun mask => (mask,id))

def c25031 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25031 : Upper (D 7) (R 7) [36,192,10,257,65,16] 13 := by
  apply FastRouting.sound _ _ [36,192,10,257,65,16] 13 (by decide) (choices 1) [2,32,128] r25031 c25031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8518
  · exact u8519
  · exact u8520

def r25032 : Route 9 := (fun mask => (mask,id))

def c25032 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25032 : Upper (D 7) (R 7) [36,192,10,257,65,128] 13 := by
  apply FastRouting.sound _ _ [36,192,10,257,65,128] 13 (by decide) (choices 1) [2,16,32] r25032 c25032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8521
  · exact u8522
  · exact u8523

def b25033 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 14 265 112 33 210 146 402), lower := (rows 37 194 14 265 112 33 64 128 256), losses := [] }

theorem u25033 : Upper (D 7) (R 7) [36,192,10,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25034 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 48, targets := 129 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 37 194 14 265 112 34 209 145 401), lower := (rows 37 194 14 265 112 34 64 128 256), losses := [] }

theorem u25034 : Upper (D 7) (R 7) [36,192,10,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25035 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 14 265 112 48 195 131 387), lower := (rows 37 194 14 265 112 48 64 128 256), losses := [] }

theorem u25035 : Upper (D 7) (R 7) [36,192,10,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25035 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25036 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 48, targets := 1 },{ cop := 1, region := 48, targets := 2 }], pairs := [(0,1),(0,6),(4,0),(4,1)], upper := (rows 37 194 14 265 112 160 83 147 275), lower := (rows 37 194 14 265 112 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 18 162 64 128 256), good := (rows 37 240 61 265 112 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 162 0 128 256), good := (rows 37 162 47 265 48 160 0 160 256) }] }

theorem u25036 : Upper (D 7) (R 7) [36,192,10,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25037 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 194 14 280 19 33 224 224 480), lower := (rows 37 194 14 280 19 33 64 128 256), losses := [] }

theorem u25037 : Upper (D 7) (R 7) [36,192,10,272,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25038 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 225, targets := 2 },{ cop := 4, region := 488, targets := 2 }], pairs := [(0,1),(2,6),(3,1),(3,6)], upper := (rows 37 194 14 280 19 96 225 161 417), lower := (rows 37 194 14 280 19 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 32 0 129 257), good := (rows 421 130 14 284 415 32 0 128 256) }] }

theorem u25038 : Upper (D 7) (R 7) [36,192,10,272,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25039 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 194 14 280 50 33 193 193 449), lower := (rows 37 194 14 280 50 33 64 128 256), losses := [] }

theorem u25039 : Upper (D 7) (R 7) [36,192,10,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25040 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 194 14 280 50 96 193 129 385), lower := (rows 37 194 14 280 50 96 64 128 256), losses := [] }

theorem u25040 : Upper (D 7) (R 7) [36,192,10,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25041 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 0, region := 194, targets := 1 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 14 280 81 33 226 162 418), lower := (rows 37 194 14 280 81 33 64 128 256), losses := [] }

theorem u25041 : Upper (D 7) (R 7) [36,192,10,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25042 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 194 14 280 81 34 225 161 417), lower := (rows 37 194 14 280 81 34 64 128 256), losses := [] }

theorem u25042 : Upper (D 7) (R 7) [36,192,10,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25043 : Route 9 := (fun mask => (mask,id))

def c25043 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25043 : Upper (D 7) (R 7) [36,192,10,272,65,128] 13 := by
  apply FastRouting.sound _ _ [36,192,10,272,65,128] 13 (by decide) (choices 1) [1,2,32] r25043 c25043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8524
  · exact u8525
  · exact u8526

def b25044 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 0, region := 194, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 14 280 112 33 195 131 387), lower := (rows 37 194 14 280 112 33 64 128 256), losses := [] }

theorem u25044 : Upper (D 7) (R 7) [36,192,10,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25045 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 48, targets := 129 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 37 194 14 280 112 34 193 129 385), lower := (rows 37 194 14 280 112 34 64 128 256), losses := [] }

theorem u25045 : Upper (D 7) (R 7) [36,192,10,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25046 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 48, targets := 1 },{ cop := 1, region := 48, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(4,0),(4,1)], upper := (rows 37 194 14 280 112 160 67 131 259), lower := (rows 37 194 14 280 112 160 64 128 256), losses := [] }

theorem u25046 : Upper (D 7) (R 7) [36,192,10,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25047 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 194 14 296 19 33 208 208 464), lower := (rows 37 194 14 296 19 33 64 128 256), losses := [] }

theorem u25047 : Upper (D 7) (R 7) [36,192,10,288,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25048 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 194 14 296 19 48 193 193 449), lower := (rows 37 194 14 296 19 48 64 128 256), losses := [] }

theorem u25048 : Upper (D 7) (R 7) [36,192,10,288,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25048 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25049 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 4, region := 488, targets := 2 }], pairs := [(0,1),(1,5),(3,1),(4,5)], upper := (rows 37 194 14 296 19 96 209 145 401), lower := (rows 37 194 14 296 19 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 114 80 144 272), good := (rows 37 224 45 296 505 96 96 128 256) }] }

theorem u25049 : Upper (D 7) (R 7) [36,192,10,288,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25050 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 14 296 81 33 210 146 402), lower := (rows 37 194 14 296 81 33 64 128 256), losses := [] }

theorem u25050 : Upper (D 7) (R 7) [36,192,10,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25051 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 194 14 296 81 34 209 145 401), lower := (rows 37 194 14 296 81 34 64 128 256), losses := [] }

theorem u25051 : Upper (D 7) (R 7) [36,192,10,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25052 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 14 296 81 48 195 131 387), lower := (rows 37 194 14 296 81 48 64 128 256), losses := [{ target := 5, region := (rows 1 51 12 8 17 0 81 145 273), good := (rows 471 194 14 270 467 466 64 128 256) }] }

theorem u25052 : Upper (D 7) (R 7) [36,192,10,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25052 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25053 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(0,1),(0,6),(1,5),(4,5)], upper := (rows 37 194 14 296 81 160 83 147 275), lower := (rows 37 194 14 296 81 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 162 64 128 256), good := (rows 37 224 45 296 81 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 162 0 128 256), good := (rows 37 162 47 296 17 160 0 160 256) }] }

theorem u25053 : Upper (D 7) (R 7) [36,192,10,288,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25054 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 194 14 328 19 33 240 176 432), lower := (rows 37 194 14 328 19 33 64 128 256), losses := [] }

theorem u25054 : Upper (D 7) (R 7) [36,192,10,320,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25055 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 194 14 328 19 48 225 161 417), lower := (rows 37 194 14 328 19 48 64 128 256), losses := [] }

theorem u25055 : Upper (D 7) (R 7) [36,192,10,320,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25055 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25056 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 488, targets := 2 }], pairs := [(0,1),(0,6),(3,1),(4,6)], upper := (rows 37 194 14 328 19 160 113 177 305), lower := (rows 37 194 14 328 19 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 178 80 144 272), good := (rows 37 224 45 328 505 160 64 160 256) }] }

theorem u25056 : Upper (D 7) (R 7) [36,192,10,320,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25057 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 194 14 328 50 33 209 145 401), lower := (rows 37 194 14 328 50 33 64 128 256), losses := [] }

theorem u25057 : Upper (D 7) (R 7) [36,192,10,320,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25058 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 14 328 50 48 193 129 385), lower := (rows 37 194 14 328 50 48 64 128 256), losses := [] }

theorem u25058 : Upper (D 7) (R 7) [36,192,10,320,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25058 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25059 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 14 328 50 160 81 145 273), lower := (rows 37 194 14 328 50 160 64 128 256), losses := [] }

theorem u25059 : Upper (D 7) (R 7) [36,192,10,320,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25060 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 194 14 328 145 33 114 178 306), lower := (rows 37 194 14 328 145 33 64 128 256), losses := [] }

theorem u25060 : Upper (D 7) (R 7) [36,192,10,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25061 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 194 14 328 145 34 113 177 305), lower := (rows 37 194 14 328 145 34 64 128 256), losses := [] }

theorem u25061 : Upper (D 7) (R 7) [36,192,10,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25062 : Route 9 := (fun mask => (mask,id))

def c25062 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25062 : Upper (D 7) (R 7) [36,192,10,320,129,16] 13 := by
  apply FastRouting.sound _ _ [36,192,10,320,129,16] 13 (by decide) (choices 1) [1,2,32] r25062 c25062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8527
  · exact u8528
  · exact u8529

def b25063 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 194 14 328 176 33 83 147 275), lower := (rows 37 194 14 328 176 33 64 128 256), losses := [] }

theorem u25063 : Upper (D 7) (R 7) [36,192,10,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25064 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 48, targets := 65 }], pairs := [(3,1),(4,0),(4,1),(4,6)], upper := (rows 37 194 14 328 176 34 81 145 273), lower := (rows 37 194 14 328 176 34 64 128 256), losses := [] }

theorem u25064 : Upper (D 7) (R 7) [36,192,10,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25065 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 14 328 176 48 67 131 259), lower := (rows 37 194 14 328 176 48 64 128 256), losses := [] }

theorem u25065 : Upper (D 7) (R 7) [36,192,10,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25065 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25066 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 28 11 81 34 480 416 416), lower := (rows 37 194 28 11 81 34 64 128 256), losses := [] }

theorem u25066 : Upper (D 7) (R 7) [36,192,24,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25067 : Route 9 := (fun mask => (mask,id))

def c25067 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u25067 : Upper (D 7) (R 7) [36,192,24,3,65,128] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3,65,128] 13 (by decide) (choices 1) [2,32,256] r25067 c25067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8530
  · exact u8531
  · exact u8532

def r25068 : Route 9 := (fun mask => (mask,id))

def c25068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25068 : Upper (D 7) (R 7) [36,192,24,3,65,256] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3,65,256] 13 (by decide) (choices 1) [2,32,128] r25068 c25068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8533
  · exact u8534
  · exact u8535

def b25069 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 28 11 112 33 450 386 386), lower := (rows 37 194 28 11 112 33 64 128 256), losses := [] }

theorem u25069 : Upper (D 7) (R 7) [36,192,24,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25070 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 28 11 112 34 449 385 385), lower := (rows 37 194 28 11 112 34 64 128 256), losses := [] }

theorem u25070 : Upper (D 7) (R 7) [36,192,24,3,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25071 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 1, region := 48, targets := 1 },{ cop := 1, region := 48, targets := 2 }], pairs := [(1,5),(3,5),(4,0),(4,1)], upper := (rows 37 194 28 11 112 160 323 387 259), lower := (rows 37 194 28 11 112 160 64 128 256), losses := [] }

theorem u25071 : Upper (D 7) (R 7) [36,192,24,3,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25072 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(0,6),(1,5),(3,5)], upper := (rows 37 194 28 11 112 288 195 131 387), lower := (rows 37 194 28 11 112 288 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 300 0 136 264), good := (rows 37 130 445 427 48 288 0 128 288) }] }

theorem u25072 : Upper (D 7) (R 7) [36,192,24,3,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25072 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25073 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 194, targets := 1 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(1,0),(2,1),(4,1)], upper := (rows 37 194 28 11 273 34 224 224 480), lower := (rows 37 194 28 11 273 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 32 97 161 289), good := (rows 501 192 28 477 465 480 64 128 256) },{ target := 6, region := (rows 5 2 4 8 16 42 0 128 256), good := (rows 37 162 61 43 273 34 0 128 256) }] }

theorem u25073 : Upper (D 7) (R 7) [36,192,24,3,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25074 : Route 9 := (fun mask => (mask,id))

def c25074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25074 : Upper (D 7) (R 7) [36,192,24,3,257,64] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3,257,64] 13 (by decide) (choices 1) [2,32,128] r25074 c25074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8536
  · exact u8537
  · exact u8538

def b25075 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 28 11 274 33 224 224 480), lower := (rows 37 194 28 11 274 33 64 128 256), losses := [] }

theorem u25075 : Upper (D 7) (R 7) [36,192,24,3,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25076 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,6),(4,6)], upper := (rows 37 194 28 11 274 96 225 161 417), lower := (rows 37 194 28 11 274 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 24 32 0 129 257), good := (rows 421 130 28 415 274 32 0 128 256) },{ target := 7, region := (rows 17 2 20 24 16 98 64 0 256), good := (rows 37 98 29 43 319 96 96 0 256) }] }

theorem u25076 : Upper (D 7) (R 7) [36,192,24,3,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25077 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 28 11 304 33 194 194 450), lower := (rows 37 194 28 11 304 33 64 128 256), losses := [] }

theorem u25077 : Upper (D 7) (R 7) [36,192,24,3,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25078 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 0, region := 464, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,1)], upper := (rows 37 194 28 11 304 34 193 193 449), lower := (rows 37 194 28 11 304 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 32 73 137 265), good := (rows 501 192 476 477 304 32 64 128 256) }] }

theorem u25078 : Upper (D 7) (R 7) [36,192,24,3,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25079 : Route 9 := (fun mask => (mask,id))

def c25079 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25079 : Upper (D 7) (R 7) [36,192,24,3,288,64] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3,288,64] 13 (by decide) (choices 1) [1,2,128] r25079 c25079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8539
  · exact u8540
  · exact u8541

#print axioms u25079
end Delivery.IrregularNine14.P07
