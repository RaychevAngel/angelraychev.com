import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0016

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7200 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 100 73 145 416 480 416 416), lower := (rows 7 26 100 73 145 32 64 128 256), losses := [] }

theorem u7200 : Upper (D 8) (R 8) [6,24,96,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7201 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 100 73 176 417 481 417 417), lower := (rows 7 26 100 73 176 32 64 128 256), losses := [] }

theorem u7201 : Upper (D 8) (R 8) [6,24,96,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7202 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 100 73 273 160 224 160 416), lower := (rows 7 26 100 73 273 32 64 128 256), losses := [] }

theorem u7202 : Upper (D 8) (R 8) [6,24,96,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7203 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 100 73 304 161 225 161 417), lower := (rows 7 26 100 73 304 32 64 128 256), losses := [] }

theorem u7203 : Upper (D 8) (R 8) [6,24,96,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7203 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7204 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 100 73 400 161 225 161 417), lower := (rows 7 26 100 73 400 32 64 128 256), losses := [] }

theorem u7204 : Upper (D 8) (R 8) [6,24,96,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7205 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 100 104 145 417 481 417 417), lower := (rows 7 26 100 104 145 32 64 128 256), losses := [] }

theorem u7205 : Upper (D 8) (R 8) [6,24,96,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7206 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 100 104 176 417 449 385 385), lower := (rows 7 26 100 104 176 32 64 128 256), losses := [] }

theorem u7206 : Upper (D 8) (R 8) [6,24,96,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7207 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 100 104 273 161 225 161 417), lower := (rows 7 26 100 104 273 32 64 128 256), losses := [] }

theorem u7207 : Upper (D 8) (R 8) [6,24,96,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7208 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 100 104 304 161 193 129 385), lower := (rows 7 26 100 104 304 32 64 128 256), losses := [] }

theorem u7208 : Upper (D 8) (R 8) [6,24,96,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7209 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 100 104 400 161 225 161 417), lower := (rows 7 26 100 104 400 32 64 128 256), losses := [] }

theorem u7209 : Upper (D 8) (R 8) [6,24,96,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7210 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 100 137 145 352 352 480 352), lower := (rows 7 26 100 137 145 32 64 128 256), losses := [] }

theorem u7210 : Upper (D 8) (R 8) [6,24,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7211 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 137 176 353 353 481 353), lower := (rows 7 26 100 137 176 32 64 128 256), losses := [] }

theorem u7211 : Upper (D 8) (R 8) [6,24,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7211 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7212 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 137 208 289 353 417 289), lower := (rows 7 26 100 137 208 32 64 128 256), losses := [] }

theorem u7212 : Upper (D 8) (R 8) [6,24,96,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7213 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 137 273 224 224 224 480), lower := (rows 7 26 100 137 273 32 64 128 256), losses := [] }

theorem u7213 : Upper (D 8) (R 8) [6,24,96,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7214 : Route 9 := (fun mask => (mask,id))

def c7214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7214 : Upper (D 8) (R 8) [6,24,96,129,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288] 13 (by decide) (choices 1) [1,64,128] r7214 c7214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u989
  · exact u990
  · exact u991

def b7215 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 100 137 336 161 225 161 417), lower := (rows 7 26 100 137 336 32 64 128 256), losses := [] }

theorem u7215 : Upper (D 8) (R 8) [6,24,96,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7216 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 137 400 97 97 225 353), lower := (rows 7 26 100 137 400 32 64 128 256), losses := [] }

theorem u7216 : Upper (D 8) (R 8) [6,24,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7217 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 100 168 176 353 321 449 321), lower := (rows 7 26 100 168 176 32 64 128 256), losses := [] }

theorem u7217 : Upper (D 8) (R 8) [6,24,96,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7218 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 168 208 289 353 417 289), lower := (rows 7 26 100 168 208 32 64 128 256), losses := [] }

theorem u7218 : Upper (D 8) (R 8) [6,24,96,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7219 : Route 9 := (fun mask => (mask,id))

def c7219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7219 : Upper (D 8) (R 8) [6,24,96,160,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,257] 13 (by decide) (choices 1) [1,64,128] r7219 c7219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u992
  · exact u993
  · exact u994

def r7220 : Route 9 := (fun mask => (mask,id))

def c7220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7220 : Upper (D 8) (R 8) [6,24,96,160,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,288] 13 (by decide) (choices 1) [1,64,128] r7220 c7220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u995
  · exact u996
  · exact u997

def b7221 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 100 168 336 161 225 161 417), lower := (rows 7 26 100 168 336 32 64 128 256), losses := [] }

theorem u7221 : Upper (D 8) (R 8) [6,24,96,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7222 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 168 400 97 97 225 353), lower := (rows 7 26 100 168 400 32 64 128 256), losses := [] }

theorem u7222 : Upper (D 8) (R 8) [6,24,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7223 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 100 200 273 161 225 161 417), lower := (rows 7 26 100 200 273 32 64 128 256), losses := [] }

theorem u7223 : Upper (D 8) (R 8) [6,24,96,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7224 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 100 200 304 161 225 161 417), lower := (rows 7 26 100 200 304 32 64 128 256), losses := [] }

theorem u7224 : Upper (D 8) (R 8) [6,24,96,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7225 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 200 400 33 97 161 289), lower := (rows 7 26 100 200 400 32 64 128 256), losses := [] }

theorem u7225 : Upper (D 8) (R 8) [6,24,96,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7226 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 196 41 49 480 480 480 480), lower := (rows 7 26 196 41 49 32 64 128 256), losses := [] }

theorem u7226 : Upper (D 8) (R 8) [6,24,192,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7227 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 196 41 81 416 480 416 416), lower := (rows 7 26 196 41 81 32 64 128 256), losses := [] }

theorem u7227 : Upper (D 8) (R 8) [6,24,192,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7228 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 196 41 112 417 481 417 417), lower := (rows 7 26 196 41 112 32 64 128 256), losses := [] }

theorem u7228 : Upper (D 8) (R 8) [6,24,192,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7229 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 26 196 41 208 289 353 417 289), lower := (rows 7 26 196 41 208 32 64 128 256), losses := [] }

theorem u7229 : Upper (D 8) (R 8) [6,24,192,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7230 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 196 41 273 224 224 224 480), lower := (rows 7 26 196 41 273 32 64 128 256), losses := [] }

theorem u7230 : Upper (D 8) (R 8) [6,24,192,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7231 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7231 : Upper (D 8) (R 8) [6,24,192,33,288] 13 := by
  apply FastRouting.sound _ _ [6,24,192,33,288] 13 (by decide) (choices 1) [1,64] r7231 c7231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u998
  · exact u999

def b7232 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 196 41 336 161 225 161 417), lower := (rows 7 26 196 41 336 32 64 128 256), losses := [] }

theorem u7232 : Upper (D 8) (R 8) [6,24,192,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7233 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 196 73 273 160 224 160 416), lower := (rows 7 26 196 73 273 32 64 128 256), losses := [] }

theorem u7233 : Upper (D 8) (R 8) [6,24,192,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7234 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 196 73 304 161 225 161 417), lower := (rows 7 26 196 73 304 32 64 128 256), losses := [] }

theorem u7234 : Upper (D 8) (R 8) [6,24,192,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7235 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 196 104 273 161 225 161 417), lower := (rows 7 26 196 104 273 32 64 128 256), losses := [] }

theorem u7235 : Upper (D 8) (R 8) [6,24,192,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7236 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 196 104 304 161 225 161 417), lower := (rows 7 26 196 104 304 32 64 128 256), losses := [] }

theorem u7236 : Upper (D 8) (R 8) [6,24,192,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7237 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 196 200 273 33 97 161 289), lower := (rows 7 26 196 200 273 32 64 128 256), losses := [] }

theorem u7237 : Upper (D 8) (R 8) [6,24,192,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7238 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 196 200 304 33 97 161 289), lower := (rows 7 26 196 200 304 32 64 128 256), losses := [] }

theorem u7238 : Upper (D 8) (R 8) [6,24,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7239 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 261 41 112 224 224 224 480), lower := (rows 7 26 261 41 112 32 64 128 256), losses := [] }

theorem u7239 : Upper (D 8) (R 8) [6,24,257,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7240 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 261 41 208 224 224 224 480), lower := (rows 7 26 261 41 208 32 64 128 256), losses := [] }

theorem u7240 : Upper (D 8) (R 8) [6,24,257,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7241 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 261 73 112 160 224 160 416), lower := (rows 7 26 261 73 112 32 64 128 256), losses := [] }

theorem u7241 : Upper (D 8) (R 8) [6,24,257,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7242 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 261 73 176 224 224 224 480), lower := (rows 7 26 261 73 176 32 64 128 256), losses := [] }

theorem u7242 : Upper (D 8) (R 8) [6,24,257,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7243 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 261 73 208 160 224 160 416), lower := (rows 7 26 261 73 208 32 64 128 256), losses := [] }

theorem u7243 : Upper (D 8) (R 8) [6,24,257,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7244 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 261 104 112 161 225 161 417), lower := (rows 7 26 261 104 112 32 64 128 256), losses := [] }

theorem u7244 : Upper (D 8) (R 8) [6,24,257,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m7245_128 : Upper (D 8) (R 8) [6,24,257,96,160,128] 13 :=
  permutation_upper _ _ _ [6,24,257,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1001

def r7245 : Route 9 := (fun mask => (mask,id))

def c7245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7245 : Upper (D 8) (R 8) [6,24,257,96,160] 13 := by
  apply FastRouting.sound _ _ [6,24,257,96,160] 13 (by decide) (choices 1) [1,64,128] r7245 c7245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1000
  · exact u1001
  · exact m7245_128

def b7246 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 261 104 208 161 225 161 417), lower := (rows 7 26 261 104 208 32 64 128 256), losses := [] }

theorem u7246 : Upper (D 8) (R 8) [6,24,257,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7247 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 261 200 208 33 97 161 289), lower := (rows 7 26 261 200 208 32 64 128 256), losses := [] }

theorem u7247 : Upper (D 8) (R 8) [6,24,257,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7248 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 292 41 49 224 192 192 448), lower := (rows 7 26 292 41 49 32 64 128 256), losses := [] }

theorem u7248 : Upper (D 8) (R 8) [6,24,288,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7249 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 292 41 81 224 224 224 480), lower := (rows 7 26 292 41 81 32 64 128 256), losses := [] }

theorem u7249 : Upper (D 8) (R 8) [6,24,288,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7250 : Route 9 := (fun mask => (mask,id))

def c7250 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7250 : Upper (D 8) (R 8) [6,24,288,33,96] 13 := by
  apply FastRouting.sound _ _ [6,24,288,33,96] 13 (by decide) (choices 1) [1,64,128] r7250 c7250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1002
  · exact u1003
  · exact u1004

def r7251 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7251 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7251 : Upper (D 8) (R 8) [6,24,288,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,288,33,192] 13 (by decide) (choices 1) [1,64] r7251 c7251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1005
  · exact u1006

def b7252 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 292 73 81 160 224 160 416), lower := (rows 7 26 292 73 81 32 64 128 256), losses := [] }

theorem u7252 : Upper (D 8) (R 8) [6,24,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7253 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 292 73 112 161 225 161 417), lower := (rows 7 26 292 73 112 32 64 128 256), losses := [] }

theorem u7253 : Upper (D 8) (R 8) [6,24,288,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7254 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 292 73 145 224 224 224 480), lower := (rows 7 26 292 73 145 32 64 128 256), losses := [] }

theorem u7254 : Upper (D 8) (R 8) [6,24,288,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7255 : Route 9 := (fun mask => (mask,id))

def c7255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7255 : Upper (D 8) (R 8) [6,24,288,65,160] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,160] 13 (by decide) (choices 1) [1,64,128] r7255 c7255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1007
  · exact u1008
  · exact u1009

def b7256 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 292 73 208 161 225 161 417), lower := (rows 7 26 292 73 208 32 64 128 256), losses := [] }

theorem u7256 : Upper (D 8) (R 8) [6,24,288,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7257 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 292 104 112 161 193 129 385), lower := (rows 7 26 292 104 112 32 64 128 256), losses := [] }

theorem u7257 : Upper (D 8) (R 8) [6,24,288,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m7258_128 : Upper (D 8) (R 8) [6,24,288,96,160,128] 13 :=
  permutation_upper _ _ _ [6,24,288,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1011

def r7258 : Route 9 := (fun mask => (mask,id))

def c7258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7258 : Upper (D 8) (R 8) [6,24,288,96,160] 13 := by
  apply FastRouting.sound _ _ [6,24,288,96,160] 13 (by decide) (choices 1) [1,64,128] r7258 c7258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1010
  · exact u1011
  · exact m7258_128

def b7259 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 292 104 208 161 225 161 417), lower := (rows 7 26 292 104 208 32 64 128 256), losses := [] }

theorem u7259 : Upper (D 8) (R 8) [6,24,288,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u7259
end Delivery.IrregularNine14.P08
