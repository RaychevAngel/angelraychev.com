import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0054
import IrregularNine14P08C0055

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11040 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 28 76 304 161 225 161 417), lower := (rows 67 131 28 76 304 32 64 128 256), losses := [] }

theorem u11040 : Upper (D 8) (R 8) [66,129,24,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11041 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 28 76 400 33 97 161 289), lower := (rows 67 131 28 76 400 32 64 128 256), losses := [] }

theorem u11041 : Upper (D 8) (R 8) [66,129,24,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11042 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 131 28 104 145 292 356 420 292), lower := (rows 67 131 28 104 145 32 64 128 256), losses := [] }

theorem u11042 : Upper (D 8) (R 8) [66,129,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11043 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 28 104 148 289 353 417 289), lower := (rows 67 131 28 104 148 32 64 128 256), losses := [] }

theorem u11043 : Upper (D 8) (R 8) [66,129,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11044 : Route 9 := (fun mask => (mask,id))

def c11044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11044 : Upper (D 8) (R 8) [66,129,24,96,160] 13 := by
  apply FastRouting.sound _ _ [66,129,24,96,160] 13 (by decide) (choices 1) [1,4,256] r11044 c11044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3292
  · exact u3293
  · exact u3294

def b11045 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 104 273 164 228 164 420), lower := (rows 67 131 28 104 273 32 64 128 256), losses := [] }

theorem u11045 : Upper (D 8) (R 8) [66,129,24,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11046 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 28 104 276 161 225 161 417), lower := (rows 67 131 28 104 276 32 64 128 256), losses := [] }

theorem u11046 : Upper (D 8) (R 8) [66,129,24,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11047 : Route 9 := (fun mask => (mask,id))

def c11047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11047 : Upper (D 8) (R 8) [66,129,24,96,288] 13 := by
  apply FastRouting.sound _ _ [66,129,24,96,288] 13 (by decide) (choices 1) [1,4,128] r11047 c11047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3295
  · exact u3296
  · exact u3297

def r11048 : Route 9 := (fun mask => (mask,id))

def c11048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11048 : Upper (D 8) (R 8) [66,129,24,96,384] 13 := by
  apply FastRouting.sound _ _ [66,129,24,96,384] 13 (by decide) (choices 1) [1,4] r11048 c11048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3298
  · exact u3299

def b11049 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 28 137 276 96 96 224 352), lower := (rows 67 131 28 137 276 32 64 128 256), losses := [] }

theorem u11049 : Upper (D 8) (R 8) [66,129,24,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11050 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 28 137 304 100 100 228 356), lower := (rows 67 131 28 137 304 32 64 128 256), losses := [] }

theorem u11050 : Upper (D 8) (R 8) [66,129,24,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11051 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 28 137 336 36 100 164 292), lower := (rows 67 131 28 137 336 32 64 128 256), losses := [] }

theorem u11051 : Upper (D 8) (R 8) [66,129,24,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11052 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 28 140 304 97 97 225 353), lower := (rows 67 131 28 140 304 32 64 128 256), losses := [] }

theorem u11052 : Upper (D 8) (R 8) [66,129,24,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11053 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 28 140 336 33 97 161 289), lower := (rows 67 131 28 140 336 32 64 128 256), losses := [] }

theorem u11053 : Upper (D 8) (R 8) [66,129,24,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11054 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 168 273 100 100 228 356), lower := (rows 67 131 28 168 273 32 64 128 256), losses := [] }

theorem u11054 : Upper (D 8) (R 8) [66,129,24,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11055 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 28 168 276 97 97 225 353), lower := (rows 67 131 28 168 276 32 64 128 256), losses := [] }

theorem u11055 : Upper (D 8) (R 8) [66,129,24,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11056 : Route 9 := (fun mask => (mask,id))

def c11056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11056 : Upper (D 8) (R 8) [66,129,24,160,288] 13 := by
  apply FastRouting.sound _ _ [66,129,24,160,288] 13 (by decide) (choices 1) [1,4,64] r11056 c11056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3300
  · exact u3301
  · exact u3302

def r11057 : Route 9 := (fun mask => (mask,id))

def c11057 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11057 : Upper (D 8) (R 8) [66,129,24,160,320] 13 := by
  apply FastRouting.sound _ _ [66,129,24,160,320] 13 (by decide) (choices 1) [1,4] r11057 c11057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3303
  · exact u3304

def b11058 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 131 28 200 276 33 97 161 289), lower := (rows 67 131 28 200 276 32 64 128 256), losses := [] }

theorem u11058 : Upper (D 8) (R 8) [66,129,24,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11059 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 131 28 200 304 37 101 165 293), lower := (rows 67 131 28 200 304 32 64 128 256), losses := [] }

theorem u11059 : Upper (D 8) (R 8) [66,129,24,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11060 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 44 88 432 496 432 432), lower := (rows 67 131 37 44 88 32 64 128 256), losses := [] }

theorem u11060 : Upper (D 8) (R 8) [66,129,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11061 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 44 112 440 472 408 408), lower := (rows 67 131 37 44 112 32 64 128 256), losses := [] }

theorem u11061 : Upper (D 8) (R 8) [66,129,33,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11062 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 44 152 368 368 496 368), lower := (rows 67 131 37 44 152 32 64 128 256), losses := [] }

theorem u11062 : Upper (D 8) (R 8) [66,129,33,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11063 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 44 176 376 344 472 344), lower := (rows 67 131 37 44 176 32 64 128 256), losses := [] }

theorem u11063 : Upper (D 8) (R 8) [66,129,33,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11064 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 44 280 240 240 240 496), lower := (rows 67 131 37 44 280 32 64 128 256), losses := [] }

theorem u11064 : Upper (D 8) (R 8) [66,129,33,36,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11065 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 44 304 248 216 216 472), lower := (rows 67 131 37 44 304 32 64 128 256), losses := [] }

theorem u11065 : Upper (D 8) (R 8) [66,129,33,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11066 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 44 336 184 248 184 440), lower := (rows 67 131 37 44 336 32 64 128 256), losses := [] }

theorem u11066 : Upper (D 8) (R 8) [66,129,33,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11067 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 44 400 120 120 248 376), lower := (rows 67 131 37 44 400 32 64 128 256), losses := [] }

theorem u11067 : Upper (D 8) (R 8) [66,129,33,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11068 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 56 84 424 488 424 424), lower := (rows 67 131 37 56 84 32 64 128 256), losses := [] }

theorem u11068 : Upper (D 8) (R 8) [66,129,33,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11069 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 56 148 360 360 488 360), lower := (rows 67 131 37 56 148 32 64 128 256), losses := [] }

theorem u11069 : Upper (D 8) (R 8) [66,129,33,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11070 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 56 276 232 232 232 488), lower := (rows 67 131 37 56 276 32 64 128 256), losses := [] }

theorem u11070 : Upper (D 8) (R 8) [66,129,33,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11071 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 56 280 228 228 228 484), lower := (rows 67 131 37 56 280 32 64 128 256), losses := [] }

theorem u11071 : Upper (D 8) (R 8) [66,129,33,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11072 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 56 336 172 236 172 428), lower := (rows 67 131 37 56 336 32 64 128 256), losses := [] }

theorem u11072 : Upper (D 8) (R 8) [66,129,33,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11073 : PairBound 9 := { available := 108, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 56 400 108 108 236 364), lower := (rows 67 131 37 56 400 32 64 128 256), losses := [] }

theorem u11073 : Upper (D 8) (R 8) [66,129,33,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11074 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 76 152 304 368 432 304), lower := (rows 67 131 37 76 152 32 64 128 256), losses := [] }

theorem u11074 : Upper (D 8) (R 8) [66,129,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11075 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 76 176 312 376 440 312), lower := (rows 67 131 37 76 176 32 64 128 256), losses := [] }

theorem u11075 : Upper (D 8) (R 8) [66,129,33,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11076 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 76 280 176 240 176 432), lower := (rows 67 131 37 76 280 32 64 128 256), losses := [] }

theorem u11076 : Upper (D 8) (R 8) [66,129,33,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11077 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 76 304 184 248 184 440), lower := (rows 67 131 37 76 304 32 64 128 256), losses := [] }

theorem u11077 : Upper (D 8) (R 8) [66,129,33,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11078 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 76 400 56 120 184 312), lower := (rows 67 131 37 76 400 32 64 128 256), losses := [] }

theorem u11078 : Upper (D 8) (R 8) [66,129,33,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11079 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 88 148 296 360 424 296), lower := (rows 67 131 37 88 148 32 64 128 256), losses := [] }

theorem u11079 : Upper (D 8) (R 8) [66,129,33,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11080 : PairBound 9 := { available := 300, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 88 176 300 364 428 300), lower := (rows 67 131 37 88 176 32 64 128 256), losses := [] }

theorem u11080 : Upper (D 8) (R 8) [66,129,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11081 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 88 276 168 232 168 424), lower := (rows 67 131 37 88 276 32 64 128 256), losses := [] }

theorem u11081 : Upper (D 8) (R 8) [66,129,33,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11082 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 88 304 172 236 172 428), lower := (rows 67 131 37 88 304 32 64 128 256), losses := [] }

theorem u11082 : Upper (D 8) (R 8) [66,129,33,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11083 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 88 400 44 108 172 300), lower := (rows 67 131 37 88 400 32 64 128 256), losses := [] }

theorem u11083 : Upper (D 8) (R 8) [66,129,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11084 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 104 148 312 376 440 312), lower := (rows 67 131 37 104 148 32 64 128 256), losses := [] }

theorem u11084 : Upper (D 8) (R 8) [66,129,33,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11085 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 104 152 308 372 436 308), lower := (rows 67 131 37 104 152 32 64 128 256), losses := [] }

theorem u11085 : Upper (D 8) (R 8) [66,129,33,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11086 : PairBound 9 := { available := 284, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 104 176 316 348 412 284), lower := (rows 67 131 37 104 176 32 64 128 256), losses := [] }

theorem u11086 : Upper (D 8) (R 8) [66,129,33,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11087 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 104 276 184 248 184 440), lower := (rows 67 131 37 104 276 32 64 128 256), losses := [] }

theorem u11087 : Upper (D 8) (R 8) [66,129,33,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11088 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 104 280 180 244 180 436), lower := (rows 67 131 37 104 280 32 64 128 256), losses := [] }

theorem u11088 : Upper (D 8) (R 8) [66,129,33,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11089 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 104 304 188 220 156 412), lower := (rows 67 131 37 104 304 32 64 128 256), losses := [] }

theorem u11089 : Upper (D 8) (R 8) [66,129,33,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11090 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 104 400 60 124 188 316), lower := (rows 67 131 37 104 400 32 64 128 256), losses := [] }

theorem u11090 : Upper (D 8) (R 8) [66,129,33,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11091 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 140 280 112 112 240 368), lower := (rows 67 131 37 140 280 32 64 128 256), losses := [] }

theorem u11091 : Upper (D 8) (R 8) [66,129,33,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11092 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 140 304 120 120 248 376), lower := (rows 67 131 37 140 304 32 64 128 256), losses := [] }

theorem u11092 : Upper (D 8) (R 8) [66,129,33,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11093 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 140 336 56 120 184 312), lower := (rows 67 131 37 140 336 32 64 128 256), losses := [] }

theorem u11093 : Upper (D 8) (R 8) [66,129,33,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11094 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 152 276 104 104 232 360), lower := (rows 67 131 37 152 276 32 64 128 256), losses := [] }

theorem u11094 : Upper (D 8) (R 8) [66,129,33,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11095 : PairBound 9 := { available := 108, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 152 304 108 108 236 364), lower := (rows 67 131 37 152 304 32 64 128 256), losses := [] }

theorem u11095 : Upper (D 8) (R 8) [66,129,33,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11096 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 152 336 44 108 172 300), lower := (rows 67 131 37 152 336 32 64 128 256), losses := [] }

theorem u11096 : Upper (D 8) (R 8) [66,129,33,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11097 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 168 276 120 120 248 376), lower := (rows 67 131 37 168 276 32 64 128 256), losses := [] }

theorem u11097 : Upper (D 8) (R 8) [66,129,33,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11098 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 168 280 116 116 244 372), lower := (rows 67 131 37 168 280 32 64 128 256), losses := [] }

theorem u11098 : Upper (D 8) (R 8) [66,129,33,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11098 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11099 : PairBound 9 := { available := 92, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 168 304 124 92 220 348), lower := (rows 67 131 37 168 304 32 64 128 256), losses := [] }

theorem u11099 : Upper (D 8) (R 8) [66,129,33,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u11099
end Delivery.IrregularNine14.P08
