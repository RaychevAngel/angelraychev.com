import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0014
import IrregularNine14P08C0015

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7020 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 84 168 176 353 353 481 353), lower := (rows 7 11 84 168 176 32 64 128 256), losses := [] }

theorem u7020 : Upper (D 8) (R 8) [6,9,80,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7021 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 84 168 208 289 353 417 289), lower := (rows 7 11 84 168 208 32 64 128 256), losses := [] }

theorem u7021 : Upper (D 8) (R 8) [6,9,80,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7022 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 168 273 224 224 224 480), lower := (rows 7 11 84 168 273 32 64 128 256), losses := [] }

theorem u7022 : Upper (D 8) (R 8) [6,9,80,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7023 : Route 9 := (fun mask => (mask,id))

def c7023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7023 : Upper (D 8) (R 8) [6,9,80,160,288] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,288] 13 (by decide) (choices 1) [1,64,128] r7023 c7023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u874
  · exact u875
  · exact u876

def b7024 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 84 168 336 161 225 161 417), lower := (rows 7 11 84 168 336 32 64 128 256), losses := [] }

theorem u7024 : Upper (D 8) (R 8) [6,9,80,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7025 : Route 9 := (fun mask => (mask,id))

def c7025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7025 : Upper (D 8) (R 8) [6,9,80,160,384] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,384] 13 (by decide) (choices 1) [1,64] r7025 c7025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u877
  · exact u878

def b7026 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 296 49 224 224 224 480), lower := (rows 7 11 84 296 49 32 64 128 256), losses := [] }

theorem u7026 : Upper (D 8) (R 8) [6,9,80,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7027 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 84 296 81 160 224 160 416), lower := (rows 7 11 84 296 81 32 64 128 256), losses := [] }

theorem u7027 : Upper (D 8) (R 8) [6,9,80,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7028 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 84 296 112 161 225 161 417), lower := (rows 7 11 84 296 112 32 64 128 256), losses := [] }

theorem u7028 : Upper (D 8) (R 8) [6,9,80,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7029 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 296 145 224 224 224 480), lower := (rows 7 11 84 296 145 32 64 128 256), losses := [] }

theorem u7029 : Upper (D 8) (R 8) [6,9,80,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7029 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7030 : Route 9 := (fun mask => (mask,id))

def c7030 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7030 : Upper (D 8) (R 8) [6,9,80,288,160] 13 := by
  apply FastRouting.sound _ _ [6,9,80,288,160] 13 (by decide) (choices 1) [1,64,128] r7030 c7030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u879
  · exact u880
  · exact u881

def b7031 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 84 296 208 161 225 161 417), lower := (rows 7 11 84 296 208 32 64 128 256), losses := [] }

theorem u7031 : Upper (D 8) (R 8) [6,9,80,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7032 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 392 49 224 224 224 480), lower := (rows 7 11 84 392 49 32 64 128 256), losses := [] }

theorem u7032 : Upper (D 8) (R 8) [6,9,80,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7033 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 84 392 81 160 224 160 416), lower := (rows 7 11 84 392 81 32 64 128 256), losses := [] }

theorem u7033 : Upper (D 8) (R 8) [6,9,80,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7034 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 84 392 112 161 225 161 417), lower := (rows 7 11 84 392 112 32 64 128 256), losses := [] }

theorem u7034 : Upper (D 8) (R 8) [6,9,80,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7035 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 392 145 96 96 224 352), lower := (rows 7 11 84 392 145 32 64 128 256), losses := [] }

theorem u7035 : Upper (D 8) (R 8) [6,9,80,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7036 : Route 9 := (fun mask => (mask,id))

def c7036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7036 : Upper (D 8) (R 8) [6,9,80,384,160] 13 := by
  apply FastRouting.sound _ _ [6,9,80,384,160] 13 (by decide) (choices 1) [1,64] r7036 c7036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u882
  · exact u883

def b7037 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 84 392 208 33 97 161 289), lower := (rows 7 11 84 392 208 32 64 128 256), losses := [] }

theorem u7037 : Upper (D 8) (R 8) [6,9,80,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7038 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 56 49 480 448 448 448), lower := (rows 7 11 100 56 49 32 64 128 256), losses := [] }

theorem u7038 : Upper (D 8) (R 8) [6,9,96,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7039 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 27, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 56 81 416 480 416 416), lower := (rows 7 11 100 56 81 32 64 128 256), losses := [] }

theorem u7039 : Upper (D 8) (R 8) [6,9,96,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7040 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 27, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 56 112 417 449 385 385), lower := (rows 7 11 100 56 112 32 64 128 256), losses := [] }

theorem u7040 : Upper (D 8) (R 8) [6,9,96,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7041 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 56 145 480 480 480 480), lower := (rows 7 11 100 56 145 32 64 128 256), losses := [] }

theorem u7041 : Upper (D 8) (R 8) [6,9,96,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7042 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 100 56 176 481 449 449 449), lower := (rows 7 11 100 56 176 32 64 128 256), losses := [] }

theorem u7042 : Upper (D 8) (R 8) [6,9,96,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7043 : Route 9 := (fun mask => (mask,id))

def c7043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7043 : Upper (D 8) (R 8) [6,9,96,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,192] 13 (by decide) (choices 1) [1,128,256] r7043 c7043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u884
  · exact u885
  · exact u886

def b7044 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 56 273 224 224 224 480), lower := (rows 7 11 100 56 273 32 64 128 256), losses := [] }

theorem u7044 : Upper (D 8) (R 8) [6,9,96,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7045 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 100 56 304 225 193 193 449), lower := (rows 7 11 100 56 304 32 64 128 256), losses := [] }

theorem u7045 : Upper (D 8) (R 8) [6,9,96,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7046 : Route 9 := (fun mask => (mask,id))

def c7046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7046 : Upper (D 8) (R 8) [6,9,96,48,320] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,320] 13 (by decide) (choices 1) [1,128] r7046 c7046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u887
  · exact u888

def r7047 : Route 9 := (fun mask => (mask,id))

def c7047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7047 : Upper (D 8) (R 8) [6,9,96,48,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,384] 13 (by decide) (choices 1) [1,64,128] r7047 c7047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u889
  · exact u890
  · exact u891

def b7048 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 152 49 480 480 480 480), lower := (rows 7 11 100 152 49 32 64 128 256), losses := [] }

theorem u7048 : Upper (D 8) (R 8) [6,9,96,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7049 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 152 81 416 480 416 416), lower := (rows 7 11 100 152 81 32 64 128 256), losses := [] }

theorem u7049 : Upper (D 8) (R 8) [6,9,96,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7050 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 100 152 112 417 481 417 417), lower := (rows 7 11 100 152 112 32 64 128 256), losses := [] }

theorem u7050 : Upper (D 8) (R 8) [6,9,96,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7051 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 100 152 145 352 352 480 352), lower := (rows 7 11 100 152 145 32 64 128 256), losses := [] }

theorem u7051 : Upper (D 8) (R 8) [6,9,96,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7052 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 152 176 353 353 481 353), lower := (rows 7 11 100 152 176 32 64 128 256), losses := [] }

theorem u7052 : Upper (D 8) (R 8) [6,9,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7053 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 152 208 289 353 417 289), lower := (rows 7 11 100 152 208 32 64 128 256), losses := [] }

theorem u7053 : Upper (D 8) (R 8) [6,9,96,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7054 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 152 273 224 224 224 480), lower := (rows 7 11 100 152 273 32 64 128 256), losses := [] }

theorem u7054 : Upper (D 8) (R 8) [6,9,96,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7055 : Route 9 := (fun mask => (mask,id))

def c7055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7055 : Upper (D 8) (R 8) [6,9,96,144,288] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,288] 13 (by decide) (choices 1) [1,64,128] r7055 c7055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u892
  · exact u893
  · exact u894

def r7056 : Route 9 := (fun mask => (mask,id))

def c7056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7056 : Upper (D 8) (R 8) [6,9,96,144,320] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,320] 13 (by decide) (choices 1) [1,128] r7056 c7056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u895
  · exact u896

def b7057 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 152 400 97 97 225 353), lower := (rows 7 11 100 152 400 32 64 128 256), losses := [] }

theorem u7057 : Upper (D 8) (R 8) [6,9,96,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7058 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 168 49 496 464 464 464), lower := (rows 7 11 100 168 49 32 64 128 256), losses := [] }

theorem u7058 : Upper (D 8) (R 8) [6,9,96,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7059 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 168 81 432 496 432 432), lower := (rows 7 11 100 168 81 32 64 128 256), losses := [] }

theorem u7059 : Upper (D 8) (R 8) [6,9,96,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7060 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 100 168 112 433 465 401 401), lower := (rows 7 11 100 168 112 32 64 128 256), losses := [] }

theorem u7060 : Upper (D 8) (R 8) [6,9,96,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7061 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 168 145 368 368 496 368), lower := (rows 7 11 100 168 145 32 64 128 256), losses := [] }

theorem u7061 : Upper (D 8) (R 8) [6,9,96,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7062 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 100 168 176 369 337 465 337), lower := (rows 7 11 100 168 176 32 64 128 256), losses := [] }

theorem u7062 : Upper (D 8) (R 8) [6,9,96,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7063 : Route 9 := (fun mask => (mask,id))

def c7063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7063 : Upper (D 8) (R 8) [6,9,96,160,192] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,192] 13 (by decide) (choices 1) [1,16,256] r7063 c7063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u897
  · exact u898
  · exact u899

def b7064 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 168 273 240 240 240 496), lower := (rows 7 11 100 168 273 32 64 128 256), losses := [] }

theorem u7064 : Upper (D 8) (R 8) [6,9,96,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7065 : Route 9 := (fun mask => (mask,id))

def c7065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7065 : Upper (D 8) (R 8) [6,9,96,160,288] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,288] 13 (by decide) (choices 1) [1,16,64,128] r7065 c7065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u900
  · exact u901
  · exact u902
  · exact u903

def r7066 : Route 9 := (fun mask => (mask,id))

def c7066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7066 : Upper (D 8) (R 8) [6,9,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,320] 13 (by decide) (choices 1) [1,16,128] r7066 c7066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u904
  · exact u905
  · exact u906

def r7067 : Route 9 := (fun mask => (mask,id))

def c7067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7067 : Upper (D 8) (R 8) [6,9,96,160,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,384] 13 (by decide) (choices 1) [1,16,64] r7067 c7067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u907
  · exact u908
  · exact u909

def b7068 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 280 49 224 224 224 480), lower := (rows 7 11 100 280 49 32 64 128 256), losses := [] }

theorem u7068 : Upper (D 8) (R 8) [6,9,96,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7069 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 280 81 160 224 160 416), lower := (rows 7 11 100 280 81 32 64 128 256), losses := [] }

theorem u7069 : Upper (D 8) (R 8) [6,9,96,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7070 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 100 280 112 161 225 161 417), lower := (rows 7 11 100 280 112 32 64 128 256), losses := [] }

theorem u7070 : Upper (D 8) (R 8) [6,9,96,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7071 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 280 145 224 224 224 480), lower := (rows 7 11 100 280 145 32 64 128 256), losses := [] }

theorem u7071 : Upper (D 8) (R 8) [6,9,96,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7072 : Route 9 := (fun mask => (mask,id))

def c7072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7072 : Upper (D 8) (R 8) [6,9,96,272,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,160] 13 (by decide) (choices 1) [1,64,128] r7072 c7072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u910
  · exact u911
  · exact u912

def r7073 : Route 9 := (fun mask => (mask,id))

def c7073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7073 : Upper (D 8) (R 8) [6,9,96,272,192] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,192] 13 (by decide) (choices 1) [1,128] r7073 c7073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u913
  · exact u914

def b7074 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 296 49 240 208 208 464), lower := (rows 7 11 100 296 49 32 64 128 256), losses := [] }

theorem u7074 : Upper (D 8) (R 8) [6,9,96,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7075 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 296 81 176 240 176 432), lower := (rows 7 11 100 296 81 32 64 128 256), losses := [] }

theorem u7075 : Upper (D 8) (R 8) [6,9,96,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7076 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 100 296 112 177 209 145 401), lower := (rows 7 11 100 296 112 32 64 128 256), losses := [] }

theorem u7076 : Upper (D 8) (R 8) [6,9,96,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7077 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 296 145 240 240 240 496), lower := (rows 7 11 100 296 145 32 64 128 256), losses := [] }

theorem u7077 : Upper (D 8) (R 8) [6,9,96,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7078 : Route 9 := (fun mask => (mask,id))

def c7078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7078 : Upper (D 8) (R 8) [6,9,96,288,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288,160] 13 (by decide) (choices 1) [1,16,64,128] r7078 c7078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u915
  · exact u916
  · exact u917
  · exact u918

def r7079 : Route 9 := (fun mask => (mask,id))

def c7079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7079 : Upper (D 8) (R 8) [6,9,96,288,192] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288,192] 13 (by decide) (choices 1) [1,16,128] r7079 c7079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u919
  · exact u920
  · exact u921

#print axioms u7079
end Delivery.IrregularNine14.P08
