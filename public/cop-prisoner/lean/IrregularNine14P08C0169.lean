import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0046
import IrregularNine14P08C0047

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10140 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 104 145 56 120 184 312), lower := (rows 67 7 388 104 145 32 64 128 256), losses := [] }

theorem u10140 : Upper (D 8) (R 8) [66,5,384,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10141 : Route 9 := (fun mask => (mask,id))

def c10141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10141 : Upper (D 8) (R 8) [66,5,384,96,136] 13 := by
  apply FastRouting.sound _ _ [66,5,384,96,136] 13 (by decide) (choices 1) [1,16] r10141 c10141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2793
  · exact u2794

def r10142 : Route 9 := (fun mask => (mask,id))

def c10142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10142 : Upper (D 8) (R 8) [66,5,384,96,160] 13 := by
  apply FastRouting.sound _ _ [66,5,384,96,160] 13 (by decide) (choices 1) [1,8,16] r10142 c10142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2795
  · exact u2796
  · exact u2797

def b10143 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 14 21 168 49 480 480 480 480), lower := (rows 67 14 21 168 49 32 64 128 256), losses := [] }

theorem u10143 : Upper (D 8) (R 8) [66,12,17,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10144 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 67 14 21 168 81 416 480 416 416), lower := (rows 67 14 21 168 81 32 64 128 256), losses := [] }

theorem u10144 : Upper (D 8) (R 8) [66,12,17,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10145 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 21 168 112 417 481 417 417), lower := (rows 67 14 21 168 112 32 64 128 256), losses := [] }

theorem u10145 : Upper (D 8) (R 8) [66,12,17,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10146 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 490, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 21 168 145 352 352 480 352), lower := (rows 67 14 21 168 145 32 64 128 256), losses := [] }

theorem u10146 : Upper (D 8) (R 8) [66,12,17,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10147 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 21 168 176 353 353 481 353), lower := (rows 67 14 21 168 176 32 64 128 256), losses := [] }

theorem u10147 : Upper (D 8) (R 8) [66,12,17,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10148 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 21 168 208 289 353 417 289), lower := (rows 67 14 21 168 208 32 64 128 256), losses := [] }

theorem u10148 : Upper (D 8) (R 8) [66,12,17,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10149 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 14 21 168 273 224 224 224 480), lower := (rows 67 14 21 168 273 32 64 128 256), losses := [] }

theorem u10149 : Upper (D 8) (R 8) [66,12,17,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10150 : Route 9 := (fun mask => (mask,id))

def c10150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10150 : Upper (D 8) (R 8) [66,12,17,160,288] 13 := by
  apply FastRouting.sound _ _ [66,12,17,160,288] 13 (by decide) (choices 1) [1,64,128] r10150 c10150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2798
  · exact u2799
  · exact u2800

def b10151 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 21 168 336 161 225 161 417), lower := (rows 67 14 21 168 336 32 64 128 256), losses := [] }

theorem u10151 : Upper (D 8) (R 8) [66,12,17,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10152 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 21 168 400 97 97 225 353), lower := (rows 67 14 21 168 400 32 64 128 256), losses := [] }

theorem u10152 : Upper (D 8) (R 8) [66,12,17,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10153 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 14 21 296 49 224 224 224 480), lower := (rows 67 14 21 296 49 32 64 128 256), losses := [] }

theorem u10153 : Upper (D 8) (R 8) [66,12,17,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10154 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 67 14 21 296 81 160 224 160 416), lower := (rows 67 14 21 296 81 32 64 128 256), losses := [] }

theorem u10154 : Upper (D 8) (R 8) [66,12,17,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10155 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 21 296 112 161 225 161 417), lower := (rows 67 14 21 296 112 32 64 128 256), losses := [] }

theorem u10155 : Upper (D 8) (R 8) [66,12,17,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10156 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 14 21 296 145 224 224 224 480), lower := (rows 67 14 21 296 145 32 64 128 256), losses := [] }

theorem u10156 : Upper (D 8) (R 8) [66,12,17,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10157 : Route 9 := (fun mask => (mask,id))

def c10157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10157 : Upper (D 8) (R 8) [66,12,17,288,160] 13 := by
  apply FastRouting.sound _ _ [66,12,17,288,160] 13 (by decide) (choices 1) [1,64,128] r10157 c10157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2801
  · exact u2802
  · exact u2803

def b10158 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 21 296 208 161 225 161 417), lower := (rows 67 14 21 296 208 32 64 128 256), losses := [] }

theorem u10158 : Upper (D 8) (R 8) [66,12,17,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10159 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 14 21 392 49 224 224 224 480), lower := (rows 67 14 21 392 49 32 64 128 256), losses := [] }

theorem u10159 : Upper (D 8) (R 8) [66,12,17,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10160 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 67 14 21 392 81 160 224 160 416), lower := (rows 67 14 21 392 81 32 64 128 256), losses := [] }

theorem u10160 : Upper (D 8) (R 8) [66,12,17,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10161 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 21 392 112 161 225 161 417), lower := (rows 67 14 21 392 112 32 64 128 256), losses := [] }

theorem u10161 : Upper (D 8) (R 8) [66,12,17,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10162 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 490, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 21 392 145 96 96 224 352), lower := (rows 67 14 21 392 145 32 64 128 256), losses := [] }

theorem u10162 : Upper (D 8) (R 8) [66,12,17,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10163 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 21 392 176 97 97 225 353), lower := (rows 67 14 21 392 176 32 64 128 256), losses := [] }

theorem u10163 : Upper (D 8) (R 8) [66,12,17,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10164 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 21 392 208 33 97 161 289), lower := (rows 67 14 21 392 208 32 64 128 256), losses := [] }

theorem u10164 : Upper (D 8) (R 8) [66,12,17,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10165 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 26, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 56 49 480 448 448 448), lower := (rows 67 14 37 56 49 32 64 128 256), losses := [] }

theorem u10165 : Upper (D 8) (R 8) [66,12,33,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10166 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 56 81 416 480 416 416), lower := (rows 67 14 37 56 81 32 64 128 256), losses := [] }

theorem u10166 : Upper (D 8) (R 8) [66,12,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10167 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 56 112 417 449 385 385), lower := (rows 67 14 37 56 112 32 64 128 256), losses := [] }

theorem u10167 : Upper (D 8) (R 8) [66,12,33,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10168 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 37 56 145 480 480 480 480), lower := (rows 67 14 37 56 145 32 64 128 256), losses := [] }

theorem u10168 : Upper (D 8) (R 8) [66,12,33,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10169 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 37 56 176 481 449 449 449), lower := (rows 67 14 37 56 176 32 64 128 256), losses := [] }

theorem u10169 : Upper (D 8) (R 8) [66,12,33,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10170 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 37 56 208 417 481 417 417), lower := (rows 67 14 37 56 208 32 64 128 256), losses := [] }

theorem u10170 : Upper (D 8) (R 8) [66,12,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10171 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 37 56 273 224 224 224 480), lower := (rows 67 14 37 56 273 32 64 128 256), losses := [] }

theorem u10171 : Upper (D 8) (R 8) [66,12,33,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10172 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 37 56 304 225 193 193 449), lower := (rows 67 14 37 56 304 32 64 128 256), losses := [] }

theorem u10172 : Upper (D 8) (R 8) [66,12,33,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10173 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 37 56 336 161 225 161 417), lower := (rows 67 14 37 56 336 32 64 128 256), losses := [] }

theorem u10173 : Upper (D 8) (R 8) [66,12,33,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10173 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10174 : Route 9 := (fun mask => (mask,id))

def c10174 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10174 : Upper (D 8) (R 8) [66,12,33,48,384] 13 := by
  apply FastRouting.sound _ _ [66,12,33,48,384] 13 (by decide) (choices 1) [1,64,128] r10174 c10174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2804
  · exact u2805
  · exact u2806

def b10175 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 14 37 152 49 480 480 480 480), lower := (rows 67 14 37 152 49 32 64 128 256), losses := [] }

theorem u10175 : Upper (D 8) (R 8) [66,12,33,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10176 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 152 81 416 480 416 416), lower := (rows 67 14 37 152 81 32 64 128 256), losses := [] }

theorem u10176 : Upper (D 8) (R 8) [66,12,33,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10177 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 37 152 112 417 481 417 417), lower := (rows 67 14 37 152 112 32 64 128 256), losses := [] }

theorem u10177 : Upper (D 8) (R 8) [66,12,33,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10178 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 152 145 352 352 480 352), lower := (rows 67 14 37 152 145 32 64 128 256), losses := [] }

theorem u10178 : Upper (D 8) (R 8) [66,12,33,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10179 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 152 176 353 353 481 353), lower := (rows 67 14 37 152 176 32 64 128 256), losses := [] }

theorem u10179 : Upper (D 8) (R 8) [66,12,33,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10180 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 152 208 289 353 417 289), lower := (rows 67 14 37 152 208 32 64 128 256), losses := [] }

theorem u10180 : Upper (D 8) (R 8) [66,12,33,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10181 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 37 152 273 224 224 224 480), lower := (rows 67 14 37 152 273 32 64 128 256), losses := [] }

theorem u10181 : Upper (D 8) (R 8) [66,12,33,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10182 : Route 9 := (fun mask => (mask,id))

def c10182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10182 : Upper (D 8) (R 8) [66,12,33,144,288] 13 := by
  apply FastRouting.sound _ _ [66,12,33,144,288] 13 (by decide) (choices 1) [1,64,128] r10182 c10182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2807
  · exact u2808
  · exact u2809

def b10183 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 37 152 336 161 225 161 417), lower := (rows 67 14 37 152 336 32 64 128 256), losses := [] }

theorem u10183 : Upper (D 8) (R 8) [66,12,33,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10184 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 152 400 97 97 225 353), lower := (rows 67 14 37 152 400 32 64 128 256), losses := [] }

theorem u10184 : Upper (D 8) (R 8) [66,12,33,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10185 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 14 37 168 49 496 464 464 464), lower := (rows 67 14 37 168 49 32 64 128 256), losses := [] }

theorem u10185 : Upper (D 8) (R 8) [66,12,33,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10186 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 168 81 432 496 432 432), lower := (rows 67 14 37 168 81 32 64 128 256), losses := [] }

theorem u10186 : Upper (D 8) (R 8) [66,12,33,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10187 : Route 9 := (fun mask => (mask,id))

def c10187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u10187 : Upper (D 8) (R 8) [66,12,33,160,96] 13 := by
  apply FastRouting.sound _ _ [66,12,33,160,96] 13 (by decide) (choices 1) [1,16,128,256] r10187 c10187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2810
  · exact u2811
  · exact u2812
  · exact u2813

def b10188 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 37 168 145 368 368 496 368), lower := (rows 67 14 37 168 145 32 64 128 256), losses := [] }

theorem u10188 : Upper (D 8) (R 8) [66,12,33,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10189 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 37 168 176 369 337 465 337), lower := (rows 67 14 37 168 176 32 64 128 256), losses := [] }

theorem u10189 : Upper (D 8) (R 8) [66,12,33,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10190 : Route 9 := (fun mask => (mask,id))

def c10190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u10190 : Upper (D 8) (R 8) [66,12,33,160,192] 13 := by
  apply FastRouting.sound _ _ [66,12,33,160,192] 13 (by decide) (choices 1) [1,16,256] r10190 c10190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2814
  · exact u2815
  · exact u2816

def b10191 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 37 168 273 240 240 240 496), lower := (rows 67 14 37 168 273 32 64 128 256), losses := [] }

theorem u10191 : Upper (D 8) (R 8) [66,12,33,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10192 : Route 9 := (fun mask => (mask,id))

def c10192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10192 : Upper (D 8) (R 8) [66,12,33,160,288] 13 := by
  apply FastRouting.sound _ _ [66,12,33,160,288] 13 (by decide) (choices 1) [1,16,64,128] r10192 c10192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2817
  · exact u2818
  · exact u2819
  · exact u2820

def r10193 : Route 9 := (fun mask => (mask,id))

def c10193 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10193 : Upper (D 8) (R 8) [66,12,33,160,320] 13 := by
  apply FastRouting.sound _ _ [66,12,33,160,320] 13 (by decide) (choices 1) [1,16,128] r10193 c10193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2821
  · exact u2822
  · exact u2823

def r10194 : Route 9 := (fun mask => (mask,id))

def c10194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10194 : Upper (D 8) (R 8) [66,12,33,160,384] 13 := by
  apply FastRouting.sound _ _ [66,12,33,160,384] 13 (by decide) (choices 1) [1,16,64] r10194 c10194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2824
  · exact u2825
  · exact u2826

def b10195 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 14 37 280 49 224 224 224 480), lower := (rows 67 14 37 280 49 32 64 128 256), losses := [] }

theorem u10195 : Upper (D 8) (R 8) [66,12,33,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10196 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 280 81 160 224 160 416), lower := (rows 67 14 37 280 81 32 64 128 256), losses := [] }

theorem u10196 : Upper (D 8) (R 8) [66,12,33,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10197 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 37 280 112 161 225 161 417), lower := (rows 67 14 37 280 112 32 64 128 256), losses := [] }

theorem u10197 : Upper (D 8) (R 8) [66,12,33,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10198 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 37 280 145 224 224 224 480), lower := (rows 67 14 37 280 145 32 64 128 256), losses := [] }

theorem u10198 : Upper (D 8) (R 8) [66,12,33,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10199 : Route 9 := (fun mask => (mask,id))

def c10199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10199 : Upper (D 8) (R 8) [66,12,33,272,160] 13 := by
  apply FastRouting.sound _ _ [66,12,33,272,160] 13 (by decide) (choices 1) [1,64,128] r10199 c10199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2827
  · exact u2828
  · exact u2829

#print axioms u10199
end Delivery.IrregularNine14.P08
