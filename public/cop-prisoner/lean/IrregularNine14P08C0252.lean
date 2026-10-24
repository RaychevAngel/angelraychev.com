import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0088

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15120 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 22, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 28 41 50 480 480 480 480), lower := (rows 193 7 28 41 50 32 64 128 256), losses := [] }

theorem u15120 : Upper (D 8) (R 8) [192,5,24,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15121 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 296, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 28 41 82 416 480 416 416), lower := (rows 193 7 28 41 82 32 64 128 256), losses := [] }

theorem u15121 : Upper (D 8) (R 8) [192,5,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15122 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 28 41 112 418 482 418 418), lower := (rows 193 7 28 41 112 32 64 128 256), losses := [] }

theorem u15122 : Upper (D 8) (R 8) [192,5,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15123 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 28 41 274 224 224 224 480), lower := (rows 193 7 28 41 274 32 64 128 256), losses := [] }

theorem u15123 : Upper (D 8) (R 8) [192,5,24,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15124 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 28 41 304 226 226 226 482), lower := (rows 193 7 28 41 304 32 64 128 256), losses := [] }

theorem u15124 : Upper (D 8) (R 8) [192,5,24,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15125 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 28 41 336 162 226 162 418), lower := (rows 193 7 28 41 336 32 64 128 256), losses := [] }

theorem u15125 : Upper (D 8) (R 8) [192,5,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15126 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 28 42 81 416 480 416 416), lower := (rows 193 7 28 42 81 32 64 128 256), losses := [] }

theorem u15126 : Upper (D 8) (R 8) [192,5,24,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15127 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 28 42 112 417 481 417 417), lower := (rows 193 7 28 42 112 32 64 128 256), losses := [] }

theorem u15127 : Upper (D 8) (R 8) [192,5,24,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15128 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 28 42 208 289 353 417 289), lower := (rows 193 7 28 42 208 32 64 128 256), losses := [] }

theorem u15128 : Upper (D 8) (R 8) [192,5,24,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15129 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 28 42 273 224 224 224 480), lower := (rows 193 7 28 42 273 32 64 128 256), losses := [] }

theorem u15129 : Upper (D 8) (R 8) [192,5,24,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15130 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15130 : Upper (D 8) (R 8) [192,5,24,34,288] 13 := by
  apply FastRouting.sound _ _ [192,5,24,34,288] 13 (by decide) (choices 1) [1,64] r15130 c15130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5335
  · exact u5336

def b15131 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 28 42 336 161 225 161 417), lower := (rows 193 7 28 42 336 32 64 128 256), losses := [] }

theorem u15131 : Upper (D 8) (R 8) [192,5,24,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15132 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 28 73 274 160 224 160 416), lower := (rows 193 7 28 73 274 32 64 128 256), losses := [] }

theorem u15132 : Upper (D 8) (R 8) [192,5,24,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15133 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 28 73 304 162 226 162 418), lower := (rows 193 7 28 73 304 32 64 128 256), losses := [] }

theorem u15133 : Upper (D 8) (R 8) [192,5,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15134 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 28 74 176 289 353 417 289), lower := (rows 193 7 28 74 176 32 64 128 256), losses := [] }

theorem u15134 : Upper (D 8) (R 8) [192,5,24,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15135 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 28 74 273 160 224 160 416), lower := (rows 193 7 28 74 273 32 64 128 256), losses := [] }

theorem u15135 : Upper (D 8) (R 8) [192,5,24,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15136 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 28 74 304 161 225 161 417), lower := (rows 193 7 28 74 304 32 64 128 256), losses := [] }

theorem u15136 : Upper (D 8) (R 8) [192,5,24,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15137 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 28 74 400 33 97 161 289), lower := (rows 193 7 28 74 400 32 64 128 256), losses := [] }

theorem u15137 : Upper (D 8) (R 8) [192,5,24,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15138 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 28 104 176 291 355 419 291), lower := (rows 193 7 28 104 176 32 64 128 256), losses := [] }

theorem u15138 : Upper (D 8) (R 8) [192,5,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15139 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 28 104 273 162 226 162 418), lower := (rows 193 7 28 104 273 32 64 128 256), losses := [] }

theorem u15139 : Upper (D 8) (R 8) [192,5,24,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15139 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15140 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 28 104 274 161 225 161 417), lower := (rows 193 7 28 104 274 32 64 128 256), losses := [] }

theorem u15140 : Upper (D 8) (R 8) [192,5,24,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15141 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 28 104 304 163 227 163 419), lower := (rows 193 7 28 104 304 32 64 128 256), losses := [] }

theorem u15141 : Upper (D 8) (R 8) [192,5,24,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15142 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 28 104 400 35 99 163 291), lower := (rows 193 7 28 104 400 32 64 128 256), losses := [] }

theorem u15142 : Upper (D 8) (R 8) [192,5,24,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15143 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 28 200 274 33 97 161 289), lower := (rows 193 7 28 200 274 32 64 128 256), losses := [] }

theorem u15143 : Upper (D 8) (R 8) [192,5,24,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15144 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 28 200 304 35 99 163 291), lower := (rows 193 7 28 200 304 32 64 128 256), losses := [] }

theorem u15144 : Upper (D 8) (R 8) [192,5,24,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15145 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 37 26 56 480 480 480 480), lower := (rows 193 7 37 26 56 32 64 128 256), losses := [] }

theorem u15145 : Upper (D 8) (R 8) [192,5,33,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15146 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 26 112 424 488 424 424), lower := (rows 193 7 37 26 112 32 64 128 256), losses := [] }

theorem u15146 : Upper (D 8) (R 8) [192,5,33,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15147 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 26 280 224 224 224 480), lower := (rows 193 7 37 26 280 32 64 128 256), losses := [] }

theorem u15147 : Upper (D 8) (R 8) [192,5,33,18,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15148 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 26 304 232 232 232 488), lower := (rows 193 7 37 26 304 32 64 128 256), losses := [] }

theorem u15148 : Upper (D 8) (R 8) [192,5,33,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15149 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 26 336 168 232 168 424), lower := (rows 193 7 37 26 336 32 64 128 256), losses := [] }

theorem u15149 : Upper (D 8) (R 8) [192,5,33,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15150 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 37 42 88 432 496 432 432), lower := (rows 193 7 37 42 88 32 64 128 256), losses := [] }

theorem u15150 : Upper (D 8) (R 8) [192,5,33,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15151 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 37 42 112 440 472 408 408), lower := (rows 193 7 37 42 112 32 64 128 256), losses := [] }

theorem u15151 : Upper (D 8) (R 8) [192,5,33,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15152 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 37 42 280 240 240 240 496), lower := (rows 193 7 37 42 280 32 64 128 256), losses := [] }

theorem u15152 : Upper (D 8) (R 8) [192,5,33,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15153 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 37 42 304 248 216 216 472), lower := (rows 193 7 37 42 304 32 64 128 256), losses := [] }

theorem u15153 : Upper (D 8) (R 8) [192,5,33,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15154 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 37 42 336 184 248 184 440), lower := (rows 193 7 37 42 336 32 64 128 256), losses := [] }

theorem u15154 : Upper (D 8) (R 8) [192,5,33,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15155 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 56 82 424 488 424 424), lower := (rows 193 7 37 56 82 32 64 128 256), losses := [] }

theorem u15155 : Upper (D 8) (R 8) [192,5,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15156 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 56 274 232 232 232 488), lower := (rows 193 7 37 56 274 32 64 128 256), losses := [] }

theorem u15156 : Upper (D 8) (R 8) [192,5,33,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15157 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 56 280 226 226 226 482), lower := (rows 193 7 37 56 280 32 64 128 256), losses := [] }

theorem u15157 : Upper (D 8) (R 8) [192,5,33,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15158 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 56 336 170 234 170 426), lower := (rows 193 7 37 56 336 32 64 128 256), losses := [] }

theorem u15158 : Upper (D 8) (R 8) [192,5,33,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15159 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 74 152 304 368 432 304), lower := (rows 193 7 37 74 152 32 64 128 256), losses := [] }

theorem u15159 : Upper (D 8) (R 8) [192,5,33,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15160 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 74 176 312 376 440 312), lower := (rows 193 7 37 74 176 32 64 128 256), losses := [] }

theorem u15160 : Upper (D 8) (R 8) [192,5,33,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15161 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 74 280 176 240 176 432), lower := (rows 193 7 37 74 280 32 64 128 256), losses := [] }

theorem u15161 : Upper (D 8) (R 8) [192,5,33,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15162 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 74 304 184 248 184 440), lower := (rows 193 7 37 74 304 32 64 128 256), losses := [] }

theorem u15162 : Upper (D 8) (R 8) [192,5,33,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15163 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 74 400 56 120 184 312), lower := (rows 193 7 37 74 400 32 64 128 256), losses := [] }

theorem u15163 : Upper (D 8) (R 8) [192,5,33,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15164 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 88 176 298 362 426 298), lower := (rows 193 7 37 88 176 32 64 128 256), losses := [] }

theorem u15164 : Upper (D 8) (R 8) [192,5,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15165 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 88 274 168 232 168 424), lower := (rows 193 7 37 88 274 32 64 128 256), losses := [] }

theorem u15165 : Upper (D 8) (R 8) [192,5,33,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15166 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 88 304 170 234 170 426), lower := (rows 193 7 37 88 304 32 64 128 256), losses := [] }

theorem u15166 : Upper (D 8) (R 8) [192,5,33,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15167 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 88 400 42 106 170 298), lower := (rows 193 7 37 88 400 32 64 128 256), losses := [] }

theorem u15167 : Upper (D 8) (R 8) [192,5,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15168 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 104 176 314 346 410 282), lower := (rows 193 7 37 104 176 32 64 128 256), losses := [] }

theorem u15168 : Upper (D 8) (R 8) [192,5,33,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15169 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 104 274 184 248 184 440), lower := (rows 193 7 37 104 274 32 64 128 256), losses := [] }

theorem u15169 : Upper (D 8) (R 8) [192,5,33,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15170 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 104 280 178 242 178 434), lower := (rows 193 7 37 104 280 32 64 128 256), losses := [] }

theorem u15170 : Upper (D 8) (R 8) [192,5,33,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15171 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 104 304 186 218 154 410), lower := (rows 193 7 37 104 304 32 64 128 256), losses := [] }

theorem u15171 : Upper (D 8) (R 8) [192,5,33,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15172 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 104 400 58 122 186 314), lower := (rows 193 7 37 104 400 32 64 128 256), losses := [] }

theorem u15172 : Upper (D 8) (R 8) [192,5,33,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15173 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 38 25 56 480 480 480 480), lower := (rows 193 7 38 25 56 32 64 128 256), losses := [] }

theorem u15173 : Upper (D 8) (R 8) [192,5,34,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15173 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15174 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 193 7 38 25 88 416 480 416 416), lower := (rows 193 7 38 25 88 32 64 128 256), losses := [] }

theorem u15174 : Upper (D 8) (R 8) [192,5,34,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15175 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 25 112 424 488 424 424), lower := (rows 193 7 38 25 112 32 64 128 256), losses := [] }

theorem u15175 : Upper (D 8) (R 8) [192,5,34,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15176 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 38 25 280 224 224 224 480), lower := (rows 193 7 38 25 280 32 64 128 256), losses := [] }

theorem u15176 : Upper (D 8) (R 8) [192,5,34,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15177 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 38 25 304 232 232 232 488), lower := (rows 193 7 38 25 304 32 64 128 256), losses := [] }

theorem u15177 : Upper (D 8) (R 8) [192,5,34,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15178 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 25 336 168 232 168 424), lower := (rows 193 7 38 25 336 32 64 128 256), losses := [] }

theorem u15178 : Upper (D 8) (R 8) [192,5,34,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15179 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 41 56 496 464 464 464), lower := (rows 193 7 38 41 56 32 64 128 256), losses := [] }

theorem u15179 : Upper (D 8) (R 8) [192,5,34,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15179
end Delivery.IrregularNine14.P08
