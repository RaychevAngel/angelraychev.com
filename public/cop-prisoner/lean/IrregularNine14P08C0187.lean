import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0056

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r11220 : Route 9 := (fun mask => (mask,id))

def c11220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11220 : Upper (D 8) (R 8) [66,129,96,160,288] 13 := by
  apply FastRouting.sound _ _ [66,129,96,160,288] 13 (by decide) (choices 1) [1,4,8,16] r11220 c11220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3373
  · exact u3374
  · exact u3375
  · exact u3376

def b11221 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 134 13 56 49 480 480 480 480), lower := (rows 67 134 13 56 49 32 64 128 256), losses := [] }

theorem u11221 : Upper (D 8) (R 8) [66,132,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11222 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 13 56 81 416 480 416 416), lower := (rows 67 134 13 56 81 32 64 128 256), losses := [] }

theorem u11222 : Upper (D 8) (R 8) [66,132,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11223 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 13 56 112 417 481 417 417), lower := (rows 67 134 13 56 112 32 64 128 256), losses := [] }

theorem u11223 : Upper (D 8) (R 8) [66,132,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11224 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 13 56 145 352 352 480 352), lower := (rows 67 134 13 56 145 32 64 128 256), losses := [] }

theorem u11224 : Upper (D 8) (R 8) [66,132,9,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11225 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 13 56 176 353 353 481 353), lower := (rows 67 134 13 56 176 32 64 128 256), losses := [] }

theorem u11225 : Upper (D 8) (R 8) [66,132,9,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11226 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 13 56 208 289 353 417 289), lower := (rows 67 134 13 56 208 32 64 128 256), losses := [] }

theorem u11226 : Upper (D 8) (R 8) [66,132,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11227 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 13 56 273 224 224 224 480), lower := (rows 67 134 13 56 273 32 64 128 256), losses := [] }

theorem u11227 : Upper (D 8) (R 8) [66,132,9,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11228 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 13 56 304 225 225 225 481), lower := (rows 67 134 13 56 304 32 64 128 256), losses := [] }

theorem u11228 : Upper (D 8) (R 8) [66,132,9,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11229 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 13 56 336 161 225 161 417), lower := (rows 67 134 13 56 336 32 64 128 256), losses := [] }

theorem u11229 : Upper (D 8) (R 8) [66,132,9,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11230 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 13 56 400 97 97 225 353), lower := (rows 67 134 13 56 400 32 64 128 256), losses := [] }

theorem u11230 : Upper (D 8) (R 8) [66,132,9,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11231 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 13 280 49 224 224 224 480), lower := (rows 67 134 13 280 49 32 64 128 256), losses := [] }

theorem u11231 : Upper (D 8) (R 8) [66,132,9,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11232 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 13 280 81 160 224 160 416), lower := (rows 67 134 13 280 81 32 64 128 256), losses := [] }

theorem u11232 : Upper (D 8) (R 8) [66,132,9,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11233 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 13 280 112 161 225 161 417), lower := (rows 67 134 13 280 112 32 64 128 256), losses := [] }

theorem u11233 : Upper (D 8) (R 8) [66,132,9,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11234 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 13 280 145 96 96 224 352), lower := (rows 67 134 13 280 145 32 64 128 256), losses := [] }

theorem u11234 : Upper (D 8) (R 8) [66,132,9,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11235 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 13 280 176 97 97 225 353), lower := (rows 67 134 13 280 176 32 64 128 256), losses := [] }

theorem u11235 : Upper (D 8) (R 8) [66,132,9,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11236 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 13 280 208 33 97 161 289), lower := (rows 67 134 13 280 208 32 64 128 256), losses := [] }

theorem u11236 : Upper (D 8) (R 8) [66,132,9,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11237 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 13 296 49 240 240 240 496), lower := (rows 67 134 13 296 49 32 64 128 256), losses := [] }

theorem u11237 : Upper (D 8) (R 8) [66,132,9,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11238 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 13 296 81 176 240 176 432), lower := (rows 67 134 13 296 81 32 64 128 256), losses := [] }

theorem u11238 : Upper (D 8) (R 8) [66,132,9,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11239 : Route 9 := (fun mask => (mask,id))

def c11239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11239 : Upper (D 8) (R 8) [66,132,9,288,96] 13 := by
  apply FastRouting.sound _ _ [66,132,9,288,96] 13 (by decide) (choices 1) [1,16,128] r11239 c11239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3377
  · exact u3378
  · exact u3379

def b11240 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 13 296 145 112 112 240 368), lower := (rows 67 134 13 296 145 32 64 128 256), losses := [] }

theorem u11240 : Upper (D 8) (R 8) [66,132,9,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11241 : Route 9 := (fun mask => (mask,id))

def c11241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11241 : Upper (D 8) (R 8) [66,132,9,288,160] 13 := by
  apply FastRouting.sound _ _ [66,132,9,288,160] 13 (by decide) (choices 1) [1,16,64] r11241 c11241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3380
  · exact u3381
  · exact u3382

def r11242 : Route 9 := (fun mask => (mask,id))

def c11242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11242 : Upper (D 8) (R 8) [66,132,9,288,192] 13 := by
  apply FastRouting.sound _ _ [66,132,9,288,192] 13 (by decide) (choices 1) [1,16] r11242 c11242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3383
  · exact u3384

def b11243 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 67 134 28 41 49 480 480 480 480), lower := (rows 67 134 28 41 49 32 64 128 256), losses := [] }

theorem u11243 : Upper (D 8) (R 8) [66,132,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11244 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 28 41 81 416 480 416 416), lower := (rows 67 134 28 41 81 32 64 128 256), losses := [] }

theorem u11244 : Upper (D 8) (R 8) [66,132,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11245 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 28 41 112 417 481 417 417), lower := (rows 67 134 28 41 112 32 64 128 256), losses := [] }

theorem u11245 : Upper (D 8) (R 8) [66,132,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11246 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 41 145 352 352 480 352), lower := (rows 67 134 28 41 145 32 64 128 256), losses := [] }

theorem u11246 : Upper (D 8) (R 8) [66,132,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11247 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 41 176 353 353 481 353), lower := (rows 67 134 28 41 176 32 64 128 256), losses := [] }

theorem u11247 : Upper (D 8) (R 8) [66,132,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11248 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 41 208 289 353 417 289), lower := (rows 67 134 28 41 208 32 64 128 256), losses := [] }

theorem u11248 : Upper (D 8) (R 8) [66,132,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11249 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 28 41 273 224 224 224 480), lower := (rows 67 134 28 41 273 32 64 128 256), losses := [] }

theorem u11249 : Upper (D 8) (R 8) [66,132,24,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11250 : Route 9 := (fun mask => (mask,id))

def c11250 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11250 : Upper (D 8) (R 8) [66,132,24,33,288] 13 := by
  apply FastRouting.sound _ _ [66,132,24,33,288] 13 (by decide) (choices 1) [1,64,128] r11250 c11250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3385
  · exact u3386
  · exact u3387

def b11251 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 28 41 336 161 225 161 417), lower := (rows 67 134 28 41 336 32 64 128 256), losses := [] }

theorem u11251 : Upper (D 8) (R 8) [66,132,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11251 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11252 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 41 400 97 97 225 353), lower := (rows 67 134 28 41 400 32 64 128 256), losses := [] }

theorem u11252 : Upper (D 8) (R 8) [66,132,24,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11253 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 28 73 273 160 224 160 416), lower := (rows 67 134 28 73 273 32 64 128 256), losses := [] }

theorem u11253 : Upper (D 8) (R 8) [66,132,24,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11254 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 28 73 304 161 225 161 417), lower := (rows 67 134 28 73 304 32 64 128 256), losses := [] }

theorem u11254 : Upper (D 8) (R 8) [66,132,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11255 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 28 104 273 161 225 161 417), lower := (rows 67 134 28 104 273 32 64 128 256), losses := [] }

theorem u11255 : Upper (D 8) (R 8) [66,132,24,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11256 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 28 104 304 161 225 161 417), lower := (rows 67 134 28 104 304 32 64 128 256), losses := [] }

theorem u11256 : Upper (D 8) (R 8) [66,132,24,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11257 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 137 273 96 96 224 352), lower := (rows 67 134 28 137 273 32 64 128 256), losses := [] }

theorem u11257 : Upper (D 8) (R 8) [66,132,24,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11258 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 137 304 97 97 225 353), lower := (rows 67 134 28 137 304 32 64 128 256), losses := [] }

theorem u11258 : Upper (D 8) (R 8) [66,132,24,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11258 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11259 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 168 273 97 97 225 353), lower := (rows 67 134 28 168 273 32 64 128 256), losses := [] }

theorem u11259 : Upper (D 8) (R 8) [66,132,24,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11260 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 168 304 97 97 225 353), lower := (rows 67 134 28 168 304 32 64 128 256), losses := [] }

theorem u11260 : Upper (D 8) (R 8) [66,132,24,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11261 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 200 273 33 97 161 289), lower := (rows 67 134 28 200 273 32 64 128 256), losses := [] }

theorem u11261 : Upper (D 8) (R 8) [66,132,24,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11262 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 28 200 304 33 97 161 289), lower := (rows 67 134 28 200 304 32 64 128 256), losses := [] }

theorem u11262 : Upper (D 8) (R 8) [66,132,24,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11263 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 37 25 56 480 480 480 480), lower := (rows 67 134 37 25 56 32 64 128 256), losses := [] }

theorem u11263 : Upper (D 8) (R 8) [66,132,33,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11264 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 134 37 25 88 416 480 416 416), lower := (rows 67 134 37 25 88 32 64 128 256), losses := [] }

theorem u11264 : Upper (D 8) (R 8) [66,132,33,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11265 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 25 112 424 488 424 424), lower := (rows 67 134 37 25 112 32 64 128 256), losses := [] }

theorem u11265 : Upper (D 8) (R 8) [66,132,33,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11265 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11266 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 37 25 152 352 352 480 352), lower := (rows 67 134 37 25 152 32 64 128 256), losses := [] }

theorem u11266 : Upper (D 8) (R 8) [66,132,33,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11267 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 37 25 176 360 360 488 360), lower := (rows 67 134 37 25 176 32 64 128 256), losses := [] }

theorem u11267 : Upper (D 8) (R 8) [66,132,33,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11268 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 25 208 296 360 424 296), lower := (rows 67 134 37 25 208 32 64 128 256), losses := [] }

theorem u11268 : Upper (D 8) (R 8) [66,132,33,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11269 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 25 280 224 224 224 480), lower := (rows 67 134 37 25 280 32 64 128 256), losses := [] }

theorem u11269 : Upper (D 8) (R 8) [66,132,33,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11270 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 37 25 304 232 232 232 488), lower := (rows 67 134 37 25 304 32 64 128 256), losses := [] }

theorem u11270 : Upper (D 8) (R 8) [66,132,33,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11271 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 25 336 168 232 168 424), lower := (rows 67 134 37 25 336 32 64 128 256), losses := [] }

theorem u11271 : Upper (D 8) (R 8) [66,132,33,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11272 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 37 25 400 104 104 232 360), lower := (rows 67 134 37 25 400 32 64 128 256), losses := [] }

theorem u11272 : Upper (D 8) (R 8) [66,132,33,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11273 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 37 41 56 496 464 464 464), lower := (rows 67 134 37 41 56 32 64 128 256), losses := [] }

theorem u11273 : Upper (D 8) (R 8) [66,132,33,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11274 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 37 41 88 432 496 432 432), lower := (rows 67 134 37 41 88 32 64 128 256), losses := [] }

theorem u11274 : Upper (D 8) (R 8) [66,132,33,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11275 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 37 41 112 440 472 408 408), lower := (rows 67 134 37 41 112 32 64 128 256), losses := [] }

theorem u11275 : Upper (D 8) (R 8) [66,132,33,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11276 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 37 41 152 368 368 496 368), lower := (rows 67 134 37 41 152 32 64 128 256), losses := [] }

theorem u11276 : Upper (D 8) (R 8) [66,132,33,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11277 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 37 41 176 376 344 472 344), lower := (rows 67 134 37 41 176 32 64 128 256), losses := [] }

theorem u11277 : Upper (D 8) (R 8) [66,132,33,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11278 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 37 41 208 312 376 440 312), lower := (rows 67 134 37 41 208 32 64 128 256), losses := [] }

theorem u11278 : Upper (D 8) (R 8) [66,132,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11279 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 37 41 280 240 240 240 496), lower := (rows 67 134 37 41 280 32 64 128 256), losses := [] }

theorem u11279 : Upper (D 8) (R 8) [66,132,33,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u11279
end Delivery.IrregularNine14.P08
