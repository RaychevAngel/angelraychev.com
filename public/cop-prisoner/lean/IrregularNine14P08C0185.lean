import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0055

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11100 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 168 336 60 124 188 316), lower := (rows 67 131 37 168 336 32 64 128 256), losses := [] }

theorem u11100 : Upper (D 8) (R 8) [66,129,33,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11101 : PairBound 9 := { available := 401, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 44 112 433 465 401 401), lower := (rows 67 131 44 44 112 32 64 128 256), losses := [] }

theorem u11101 : Upper (D 8) (R 8) [66,129,40,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11102 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 44 176 369 337 465 337), lower := (rows 67 131 44 44 176 32 64 128 256), losses := [] }

theorem u11102 : Upper (D 8) (R 8) [66,129,40,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11103 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 44 304 241 209 209 465), lower := (rows 67 131 44 44 304 32 64 128 256), losses := [] }

theorem u11103 : Upper (D 8) (R 8) [66,129,40,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11104 : PairBound 9 := { available := 177, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 44 336 177 241 177 433), lower := (rows 67 131 44 44 336 32 64 128 256), losses := [] }

theorem u11104 : Upper (D 8) (R 8) [66,129,40,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11105 : PairBound 9 := { available := 113, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 44 400 113 113 241 369), lower := (rows 67 131 44 44 400 32 64 128 256), losses := [] }

theorem u11105 : Upper (D 8) (R 8) [66,129,40,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11106 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 56 84 417 481 417 417), lower := (rows 67 131 44 56 84 32 64 128 256), losses := [] }

theorem u11106 : Upper (D 8) (R 8) [66,129,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11107 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 56 112 421 453 389 389), lower := (rows 67 131 44 56 112 32 64 128 256), losses := [] }

theorem u11107 : Upper (D 8) (R 8) [66,129,40,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11108 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 56 148 353 353 481 353), lower := (rows 67 131 44 56 148 32 64 128 256), losses := [] }

theorem u11108 : Upper (D 8) (R 8) [66,129,40,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11109 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 56 176 357 325 453 325), lower := (rows 67 131 44 56 176 32 64 128 256), losses := [] }

theorem u11109 : Upper (D 8) (R 8) [66,129,40,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11110 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 56 276 225 225 225 481), lower := (rows 67 131 44 56 276 32 64 128 256), losses := [] }

theorem u11110 : Upper (D 8) (R 8) [66,129,40,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11111 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 56 304 229 197 197 453), lower := (rows 67 131 44 56 304 32 64 128 256), losses := [] }

theorem u11111 : Upper (D 8) (R 8) [66,129,40,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11112 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 56 336 165 229 165 421), lower := (rows 67 131 44 56 336 32 64 128 256), losses := [] }

theorem u11112 : Upper (D 8) (R 8) [66,129,40,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11113 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 56 400 101 101 229 357), lower := (rows 67 131 44 56 400 32 64 128 256), losses := [] }

theorem u11113 : Upper (D 8) (R 8) [66,129,40,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11114 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 73 148 304 368 432 304), lower := (rows 67 131 44 73 148 32 64 128 256), losses := [] }

theorem u11114 : Upper (D 8) (R 8) [66,129,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11115 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 73 176 308 372 436 308), lower := (rows 67 131 44 73 176 32 64 128 256), losses := [] }

theorem u11115 : Upper (D 8) (R 8) [66,129,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11116 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 73 276 176 240 176 432), lower := (rows 67 131 44 73 276 32 64 128 256), losses := [] }

theorem u11116 : Upper (D 8) (R 8) [66,129,40,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11117 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 73 304 180 244 180 436), lower := (rows 67 131 44 73 304 32 64 128 256), losses := [] }

theorem u11117 : Upper (D 8) (R 8) [66,129,40,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11118 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 73 400 52 116 180 308), lower := (rows 67 131 44 73 400 32 64 128 256), losses := [] }

theorem u11118 : Upper (D 8) (R 8) [66,129,40,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11119 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 76 176 305 369 433 305), lower := (rows 67 131 44 76 176 32 64 128 256), losses := [] }

theorem u11119 : Upper (D 8) (R 8) [66,129,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11120 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 76 304 177 241 177 433), lower := (rows 67 131 44 76 304 32 64 128 256), losses := [] }

theorem u11120 : Upper (D 8) (R 8) [66,129,40,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11121 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 76 400 49 113 177 305), lower := (rows 67 131 44 76 400 32 64 128 256), losses := [] }

theorem u11121 : Upper (D 8) (R 8) [66,129,40,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11122 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 131 44 88 145 292 356 420 292), lower := (rows 67 131 44 88 145 32 64 128 256), losses := [] }

theorem u11122 : Upper (D 8) (R 8) [66,129,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11123 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 88 148 289 353 417 289), lower := (rows 67 131 44 88 148 32 64 128 256), losses := [] }

theorem u11123 : Upper (D 8) (R 8) [66,129,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11124 : Route 9 := (fun mask => (mask,id))

def c11124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11124 : Upper (D 8) (R 8) [66,129,40,80,160] 13 := by
  apply FastRouting.sound _ _ [66,129,40,80,160] 13 (by decide) (choices 1) [1,4,256] r11124 c11124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3305
  · exact u3306
  · exact u3307

def b11125 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 88 273 164 228 164 420), lower := (rows 67 131 44 88 273 32 64 128 256), losses := [] }

theorem u11125 : Upper (D 8) (R 8) [66,129,40,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11126 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 88 276 161 225 161 417), lower := (rows 67 131 44 88 276 32 64 128 256), losses := [] }

theorem u11126 : Upper (D 8) (R 8) [66,129,40,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11127 : Route 9 := (fun mask => (mask,id))

def c11127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11127 : Upper (D 8) (R 8) [66,129,40,80,288] 13 := by
  apply FastRouting.sound _ _ [66,129,40,80,288] 13 (by decide) (choices 1) [1,4,128] r11127 c11127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3308
  · exact u3309
  · exact u3310

def r11128 : Route 9 := (fun mask => (mask,id))

def c11128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11128 : Upper (D 8) (R 8) [66,129,40,80,384] 13 := by
  apply FastRouting.sound _ _ [66,129,40,80,384] 13 (by decide) (choices 1) [1,4] r11128 c11128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3311
  · exact u3312

def b11129 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 104 148 305 369 433 305), lower := (rows 67 131 44 104 148 32 64 128 256), losses := [] }

theorem u11129 : Upper (D 8) (R 8) [66,129,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11130 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 104 176 309 341 405 277), lower := (rows 67 131 44 104 176 32 64 128 256), losses := [] }

theorem u11130 : Upper (D 8) (R 8) [66,129,40,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11131 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 104 276 177 241 177 433), lower := (rows 67 131 44 104 276 32 64 128 256), losses := [] }

theorem u11131 : Upper (D 8) (R 8) [66,129,40,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11132 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 104 304 181 213 149 405), lower := (rows 67 131 44 104 304 32 64 128 256), losses := [] }

theorem u11132 : Upper (D 8) (R 8) [66,129,40,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11133 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 104 400 53 117 181 309), lower := (rows 67 131 44 104 400 32 64 128 256), losses := [] }

theorem u11133 : Upper (D 8) (R 8) [66,129,40,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11134 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 44 137 84 304 368 432 304), lower := (rows 67 131 44 137 84 32 64 128 256), losses := [] }

theorem u11134 : Upper (D 8) (R 8) [66,129,40,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11135 : PairBound 9 := { available := 308, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 44 137 112 308 372 436 308), lower := (rows 67 131 44 137 112 32 64 128 256), losses := [] }

theorem u11135 : Upper (D 8) (R 8) [66,129,40,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11136 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 44 137 276 112 112 240 368), lower := (rows 67 131 44 137 276 32 64 128 256), losses := [] }

theorem u11136 : Upper (D 8) (R 8) [66,129,40,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11137 : PairBound 9 := { available := 116, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 44 137 304 116 116 244 372), lower := (rows 67 131 44 137 304 32 64 128 256), losses := [] }

theorem u11137 : Upper (D 8) (R 8) [66,129,40,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11138 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 44 137 336 52 116 180 308), lower := (rows 67 131 44 137 336 32 64 128 256), losses := [] }

theorem u11138 : Upper (D 8) (R 8) [66,129,40,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11139 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 44 140 112 305 369 433 305), lower := (rows 67 131 44 140 112 32 64 128 256), losses := [] }

theorem u11139 : Upper (D 8) (R 8) [66,129,40,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11139 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11140 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 44 140 304 113 113 241 369), lower := (rows 67 131 44 140 304 32 64 128 256), losses := [] }

theorem u11140 : Upper (D 8) (R 8) [66,129,40,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11141 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 44 140 336 49 113 177 305), lower := (rows 67 131 44 140 336 32 64 128 256), losses := [] }

theorem u11141 : Upper (D 8) (R 8) [66,129,40,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11142 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 152 81 292 356 420 292), lower := (rows 67 131 44 152 81 32 64 128 256), losses := [] }

theorem u11142 : Upper (D 8) (R 8) [66,129,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11143 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 152 84 289 353 417 289), lower := (rows 67 131 44 152 84 32 64 128 256), losses := [] }

theorem u11143 : Upper (D 8) (R 8) [66,129,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11144 : Route 9 := (fun mask => (mask,id))

def c11144 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11144 : Upper (D 8) (R 8) [66,129,40,144,96] 13 := by
  apply FastRouting.sound _ _ [66,129,40,144,96] 13 (by decide) (choices 1) [1,4,256] r11144 c11144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3313
  · exact u3314
  · exact u3315

def b11145 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 152 273 100 100 228 356), lower := (rows 67 131 44 152 273 32 64 128 256), losses := [] }

theorem u11145 : Upper (D 8) (R 8) [66,129,40,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11146 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 44 152 276 97 97 225 353), lower := (rows 67 131 44 152 276 32 64 128 256), losses := [] }

theorem u11146 : Upper (D 8) (R 8) [66,129,40,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11147 : Route 9 := (fun mask => (mask,id))

def c11147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11147 : Upper (D 8) (R 8) [66,129,40,144,288] 13 := by
  apply FastRouting.sound _ _ [66,129,40,144,288] 13 (by decide) (choices 1) [1,4,64] r11147 c11147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3316
  · exact u3317
  · exact u3318

def r11148 : Route 9 := (fun mask => (mask,id))

def c11148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11148 : Upper (D 8) (R 8) [66,129,40,144,320] 13 := by
  apply FastRouting.sound _ _ [66,129,40,144,320] 13 (by decide) (choices 1) [1,4] r11148 c11148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3319
  · exact u3320

def b11149 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 168 84 305 369 433 305), lower := (rows 67 131 44 168 84 32 64 128 256), losses := [] }

theorem u11149 : Upper (D 8) (R 8) [66,129,40,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11150 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 168 112 309 341 405 277), lower := (rows 67 131 44 168 112 32 64 128 256), losses := [] }

theorem u11150 : Upper (D 8) (R 8) [66,129,40,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11151 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 168 276 113 113 241 369), lower := (rows 67 131 44 168 276 32 64 128 256), losses := [] }

theorem u11151 : Upper (D 8) (R 8) [66,129,40,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11152 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 168 304 117 85 213 341), lower := (rows 67 131 44 168 304 32 64 128 256), losses := [] }

theorem u11152 : Upper (D 8) (R 8) [66,129,40,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11153 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 168 336 53 117 181 309), lower := (rows 67 131 44 168 336 32 64 128 256), losses := [] }

theorem u11153 : Upper (D 8) (R 8) [66,129,40,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11154 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 131 44 200 276 49 113 177 305), lower := (rows 67 131 44 200 276 32 64 128 256), losses := [] }

theorem u11154 : Upper (D 8) (R 8) [66,129,40,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11155 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 131 44 200 304 53 117 181 309), lower := (rows 67 131 44 200 304 32 64 128 256), losses := [] }

theorem u11155 : Upper (D 8) (R 8) [66,129,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11156 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 265 84 176 240 176 432), lower := (rows 67 131 44 265 84 32 64 128 256), losses := [] }

theorem u11156 : Upper (D 8) (R 8) [66,129,40,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11157 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 265 112 180 244 180 436), lower := (rows 67 131 44 265 112 32 64 128 256), losses := [] }

theorem u11157 : Upper (D 8) (R 8) [66,129,40,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11158 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 265 148 112 112 240 368), lower := (rows 67 131 44 265 148 32 64 128 256), losses := [] }

theorem u11158 : Upper (D 8) (R 8) [66,129,40,257,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11159 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 265 176 116 116 244 372), lower := (rows 67 131 44 265 176 32 64 128 256), losses := [] }

theorem u11159 : Upper (D 8) (R 8) [66,129,40,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u11159
end Delivery.IrregularNine14.P08
