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

def b15060 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 88 50 416 480 416 416), lower := (rows 193 7 13 88 50 32 64 128 256), losses := [] }

theorem u15060 : Upper (D 8) (R 8) [192,5,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15061 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 30, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 88 146 288 352 416 288), lower := (rows 193 7 13 88 146 32 64 128 256), losses := [] }

theorem u15061 : Upper (D 8) (R 8) [192,5,9,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15062 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 88 176 290 354 418 290), lower := (rows 193 7 13 88 176 32 64 128 256), losses := [] }

theorem u15062 : Upper (D 8) (R 8) [192,5,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15063 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 88 274 160 224 160 416), lower := (rows 193 7 13 88 274 32 64 128 256), losses := [] }

theorem u15063 : Upper (D 8) (R 8) [192,5,9,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15064 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 88 304 162 226 162 418), lower := (rows 193 7 13 88 304 32 64 128 256), losses := [] }

theorem u15064 : Upper (D 8) (R 8) [192,5,9,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15065 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 88 400 34 98 162 290), lower := (rows 193 7 13 88 400 32 64 128 256), losses := [] }

theorem u15065 : Upper (D 8) (R 8) [192,5,9,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15066 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 104 50 432 496 432 432), lower := (rows 193 7 13 104 50 32 64 128 256), losses := [] }

theorem u15066 : Upper (D 8) (R 8) [192,5,9,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15067 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 104 146 304 368 432 304), lower := (rows 193 7 13 104 146 32 64 128 256), losses := [] }

theorem u15067 : Upper (D 8) (R 8) [192,5,9,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15068 : PairBound 9 := { available := 306, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 104 176 306 370 434 306), lower := (rows 193 7 13 104 176 32 64 128 256), losses := [] }

theorem u15068 : Upper (D 8) (R 8) [192,5,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15069 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 104 274 176 240 176 432), lower := (rows 193 7 13 104 274 32 64 128 256), losses := [] }

theorem u15069 : Upper (D 8) (R 8) [192,5,9,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15070 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 104 304 178 242 178 434), lower := (rows 193 7 13 104 304 32 64 128 256), losses := [] }

theorem u15070 : Upper (D 8) (R 8) [192,5,9,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15071 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 104 400 50 114 178 306), lower := (rows 193 7 13 104 400 32 64 128 256), losses := [] }

theorem u15071 : Upper (D 8) (R 8) [192,5,9,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15072 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 266 112 176 240 176 432), lower := (rows 193 7 13 266 112 32 64 128 256), losses := [] }

theorem u15072 : Upper (D 8) (R 8) [192,5,9,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15073 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 280 50 224 224 224 480), lower := (rows 193 7 13 280 50 32 64 128 256), losses := [] }

theorem u15073 : Upper (D 8) (R 8) [192,5,9,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15074 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 280 82 160 224 160 416), lower := (rows 193 7 13 280 82 32 64 128 256), losses := [] }

theorem u15074 : Upper (D 8) (R 8) [192,5,9,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15075 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 280 112 162 226 162 418), lower := (rows 193 7 13 280 112 32 64 128 256), losses := [] }

theorem u15075 : Upper (D 8) (R 8) [192,5,9,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15076 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 296 50 240 240 240 496), lower := (rows 193 7 13 296 50 32 64 128 256), losses := [] }

theorem u15076 : Upper (D 8) (R 8) [192,5,9,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15077 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 296 82 176 240 176 432), lower := (rows 193 7 13 296 82 32 64 128 256), losses := [] }

theorem u15077 : Upper (D 8) (R 8) [192,5,9,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15078 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 296 112 178 242 178 434), lower := (rows 193 7 13 296 112 32 64 128 256), losses := [] }

theorem u15078 : Upper (D 8) (R 8) [192,5,9,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15079 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 328 50 176 240 176 432), lower := (rows 193 7 13 328 50 32 64 128 256), losses := [] }

theorem u15079 : Upper (D 8) (R 8) [192,5,9,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15080 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 328 146 48 112 176 304), lower := (rows 193 7 13 328 146 32 64 128 256), losses := [] }

theorem u15080 : Upper (D 8) (R 8) [192,5,9,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15081 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 328 176 50 114 178 306), lower := (rows 193 7 13 328 176 32 64 128 256), losses := [] }

theorem u15081 : Upper (D 8) (R 8) [192,5,9,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15082 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 25 112 416 480 416 416), lower := (rows 193 7 14 25 112 32 64 128 256), losses := [] }

theorem u15082 : Upper (D 8) (R 8) [192,5,10,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15083 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 25 304 224 224 224 480), lower := (rows 193 7 14 25 304 32 64 128 256), losses := [] }

theorem u15083 : Upper (D 8) (R 8) [192,5,10,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15084 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 25 336 160 224 160 416), lower := (rows 193 7 14 25 336 32 64 128 256), losses := [] }

theorem u15084 : Upper (D 8) (R 8) [192,5,10,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15085 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 41 112 432 496 432 432), lower := (rows 193 7 14 41 112 32 64 128 256), losses := [] }

theorem u15085 : Upper (D 8) (R 8) [192,5,10,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15086 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 41 304 240 240 240 496), lower := (rows 193 7 14 41 304 32 64 128 256), losses := [] }

theorem u15086 : Upper (D 8) (R 8) [192,5,10,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15087 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 41 336 176 240 176 432), lower := (rows 193 7 14 41 336 32 64 128 256), losses := [] }

theorem u15087 : Upper (D 8) (R 8) [192,5,10,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15088 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 14 56 49 480 480 480 480), lower := (rows 193 7 14 56 49 32 64 128 256), losses := [] }

theorem u15088 : Upper (D 8) (R 8) [192,5,10,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15089 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 14 56 81 416 480 416 416), lower := (rows 193 7 14 56 81 32 64 128 256), losses := [] }

theorem u15089 : Upper (D 8) (R 8) [192,5,10,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15090 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 14 56 112 417 481 417 417), lower := (rows 193 7 14 56 112 32 64 128 256), losses := [] }

theorem u15090 : Upper (D 8) (R 8) [192,5,10,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15091 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 14 56 208 289 353 417 289), lower := (rows 193 7 14 56 208 32 64 128 256), losses := [] }

theorem u15091 : Upper (D 8) (R 8) [192,5,10,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15092 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 14 56 273 224 224 224 480), lower := (rows 193 7 14 56 273 32 64 128 256), losses := [] }

theorem u15092 : Upper (D 8) (R 8) [192,5,10,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15093 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 14 56 304 225 225 225 481), lower := (rows 193 7 14 56 304 32 64 128 256), losses := [] }

theorem u15093 : Upper (D 8) (R 8) [192,5,10,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15094 : Route 9 := (fun mask => (mask,id))

def c15094 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15094 : Upper (D 8) (R 8) [192,5,10,48,320] 13 := by
  apply FastRouting.sound _ _ [192,5,10,48,320] 13 (by decide) (choices 1) [1,128] r15094 c15094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5328
  · exact u5329

def b15095 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 73 176 304 368 432 304), lower := (rows 193 7 14 73 176 32 64 128 256), losses := [] }

theorem u15095 : Upper (D 8) (R 8) [192,5,10,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15096 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 73 304 176 240 176 432), lower := (rows 193 7 14 73 304 32 64 128 256), losses := [] }

theorem u15096 : Upper (D 8) (R 8) [192,5,10,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15097 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 73 400 48 112 176 304), lower := (rows 193 7 14 73 400 32 64 128 256), losses := [] }

theorem u15097 : Upper (D 8) (R 8) [192,5,10,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15098 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 88 49 416 480 416 416), lower := (rows 193 7 14 88 49 32 64 128 256), losses := [] }

theorem u15098 : Upper (D 8) (R 8) [192,5,10,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15098 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15099 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 88 176 289 353 417 289), lower := (rows 193 7 14 88 176 32 64 128 256), losses := [] }

theorem u15099 : Upper (D 8) (R 8) [192,5,10,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15100 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 88 273 160 224 160 416), lower := (rows 193 7 14 88 273 32 64 128 256), losses := [] }

theorem u15100 : Upper (D 8) (R 8) [192,5,10,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15101 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 88 304 161 225 161 417), lower := (rows 193 7 14 88 304 32 64 128 256), losses := [] }

theorem u15101 : Upper (D 8) (R 8) [192,5,10,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15102 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 88 400 33 97 161 289), lower := (rows 193 7 14 88 400 32 64 128 256), losses := [] }

theorem u15102 : Upper (D 8) (R 8) [192,5,10,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15103 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 104 49 432 496 432 432), lower := (rows 193 7 14 104 49 32 64 128 256), losses := [] }

theorem u15103 : Upper (D 8) (R 8) [192,5,10,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15104 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 104 176 305 369 433 305), lower := (rows 193 7 14 104 176 32 64 128 256), losses := [] }

theorem u15104 : Upper (D 8) (R 8) [192,5,10,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15105 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 104 273 176 240 176 432), lower := (rows 193 7 14 104 273 32 64 128 256), losses := [] }

theorem u15105 : Upper (D 8) (R 8) [192,5,10,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15106 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 104 304 177 241 177 433), lower := (rows 193 7 14 104 304 32 64 128 256), losses := [] }

theorem u15106 : Upper (D 8) (R 8) [192,5,10,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15107 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 104 400 49 113 177 305), lower := (rows 193 7 14 104 400 32 64 128 256), losses := [] }

theorem u15107 : Upper (D 8) (R 8) [192,5,10,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15108 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 200 304 49 113 177 305), lower := (rows 193 7 14 200 304 32 64 128 256), losses := [] }

theorem u15108 : Upper (D 8) (R 8) [192,5,10,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15109 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 265 112 176 240 176 432), lower := (rows 193 7 14 265 112 32 64 128 256), losses := [] }

theorem u15109 : Upper (D 8) (R 8) [192,5,10,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15110 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 14 280 49 224 224 224 480), lower := (rows 193 7 14 280 49 32 64 128 256), losses := [] }

theorem u15110 : Upper (D 8) (R 8) [192,5,10,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15111 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 14 280 81 160 224 160 416), lower := (rows 193 7 14 280 81 32 64 128 256), losses := [] }

theorem u15111 : Upper (D 8) (R 8) [192,5,10,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15112 : Route 9 := (fun mask => (mask,id))

def c15112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15112 : Upper (D 8) (R 8) [192,5,10,272,96] 13 := by
  apply FastRouting.sound _ _ [192,5,10,272,96] 13 (by decide) (choices 1) [1,128] r15112 c15112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5330
  · exact u5331

def b15113 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 14 280 208 33 97 161 289), lower := (rows 193 7 14 280 208 32 64 128 256), losses := [] }

theorem u15113 : Upper (D 8) (R 8) [192,5,10,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15114 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 14 296 49 240 240 240 496), lower := (rows 193 7 14 296 49 32 64 128 256), losses := [] }

theorem u15114 : Upper (D 8) (R 8) [192,5,10,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15115 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 14 296 81 176 240 176 432), lower := (rows 193 7 14 296 81 32 64 128 256), losses := [] }

theorem u15115 : Upper (D 8) (R 8) [192,5,10,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15116 : Route 9 := (fun mask => (mask,id))

def c15116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15116 : Upper (D 8) (R 8) [192,5,10,288,96] 13 := by
  apply FastRouting.sound _ _ [192,5,10,288,96] 13 (by decide) (choices 1) [1,16,128] r15116 c15116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5332
  · exact u5333
  · exact u5334

def b15117 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 14 296 208 49 113 177 305), lower := (rows 193 7 14 296 208 32 64 128 256), losses := [] }

theorem u15117 : Upper (D 8) (R 8) [192,5,10,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15118 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 328 49 176 240 176 432), lower := (rows 193 7 14 328 49 32 64 128 256), losses := [] }

theorem u15118 : Upper (D 8) (R 8) [192,5,10,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15119 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 328 176 49 113 177 305), lower := (rows 193 7 14 328 176 32 64 128 256), losses := [] }

theorem u15119 : Upper (D 8) (R 8) [192,5,10,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15119
end Delivery.IrregularNine14.P08
