import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0015

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7080 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 392 49 240 240 240 496), lower := (rows 7 11 100 392 49 32 64 128 256), losses := [] }

theorem u7080 : Upper (D 8) (R 8) [6,9,96,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7081 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 392 81 176 240 176 432), lower := (rows 7 11 100 392 81 32 64 128 256), losses := [] }

theorem u7081 : Upper (D 8) (R 8) [6,9,96,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7082 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 100 392 112 177 241 177 433), lower := (rows 7 11 100 392 112 32 64 128 256), losses := [] }

theorem u7082 : Upper (D 8) (R 8) [6,9,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7083 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 392 145 112 112 240 368), lower := (rows 7 11 100 392 145 32 64 128 256), losses := [] }

theorem u7083 : Upper (D 8) (R 8) [6,9,96,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7084 : Route 9 := (fun mask => (mask,id))

def c7084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7084 : Upper (D 8) (R 8) [6,9,96,384,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,160] 13 (by decide) (choices 1) [1,16,64] r7084 c7084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u922
  · exact u923
  · exact u924

def r7085 : Route 9 := (fun mask => (mask,id))

def c7085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7085 : Upper (D 8) (R 8) [6,9,96,384,192] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,192] 13 (by decide) (choices 1) [1,16] r7085 c7085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u925
  · exact u926

def b7086 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 7 11 196 56 49 480 480 480 480), lower := (rows 7 11 196 56 49 32 64 128 256), losses := [] }

theorem u7086 : Upper (D 8) (R 8) [6,9,192,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7087 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 196 56 81 416 480 416 416), lower := (rows 7 11 196 56 81 32 64 128 256), losses := [] }

theorem u7087 : Upper (D 8) (R 8) [6,9,192,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7088 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 196 56 112 417 481 417 417), lower := (rows 7 11 196 56 112 32 64 128 256), losses := [] }

theorem u7088 : Upper (D 8) (R 8) [6,9,192,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7089 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 196 56 208 289 353 417 289), lower := (rows 7 11 196 56 208 32 64 128 256), losses := [] }

theorem u7089 : Upper (D 8) (R 8) [6,9,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7090 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 196 56 273 224 224 224 480), lower := (rows 7 11 196 56 273 32 64 128 256), losses := [] }

theorem u7090 : Upper (D 8) (R 8) [6,9,192,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7091 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 196 56 304 225 225 225 481), lower := (rows 7 11 196 56 304 32 64 128 256), losses := [] }

theorem u7091 : Upper (D 8) (R 8) [6,9,192,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7092 : Route 9 := (fun mask => (mask,id))

def c7092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7092 : Upper (D 8) (R 8) [6,9,192,48,320] 13 := by
  apply FastRouting.sound _ _ [6,9,192,48,320] 13 (by decide) (choices 1) [1,128] r7092 c7092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u927
  · exact u928

def b7093 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 196 280 49 224 224 224 480), lower := (rows 7 11 196 280 49 32 64 128 256), losses := [] }

theorem u7093 : Upper (D 8) (R 8) [6,9,192,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7094 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 196 280 81 160 224 160 416), lower := (rows 7 11 196 280 81 32 64 128 256), losses := [] }

theorem u7094 : Upper (D 8) (R 8) [6,9,192,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7095 : Route 9 := (fun mask => (mask,id))

def c7095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7095 : Upper (D 8) (R 8) [6,9,192,272,96] 13 := by
  apply FastRouting.sound _ _ [6,9,192,272,96] 13 (by decide) (choices 1) [1,128] r7095 c7095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u929
  · exact u930

def b7096 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 196 280 208 33 97 161 289), lower := (rows 7 11 196 280 208 32 64 128 256), losses := [] }

theorem u7096 : Upper (D 8) (R 8) [6,9,192,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7097 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 196 296 49 240 240 240 496), lower := (rows 7 11 196 296 49 32 64 128 256), losses := [] }

theorem u7097 : Upper (D 8) (R 8) [6,9,192,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7098 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 196 296 81 176 240 176 432), lower := (rows 7 11 196 296 81 32 64 128 256), losses := [] }

theorem u7098 : Upper (D 8) (R 8) [6,9,192,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7098 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7099 : Route 9 := (fun mask => (mask,id))

def c7099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7099 : Upper (D 8) (R 8) [6,9,192,288,96] 13 := by
  apply FastRouting.sound _ _ [6,9,192,288,96] 13 (by decide) (choices 1) [1,16,128] r7099 c7099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u931
  · exact u932
  · exact u933

def b7100 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 196 296 208 49 113 177 305), lower := (rows 7 11 196 296 208 32 64 128 256), losses := [] }

theorem u7100 : Upper (D 8) (R 8) [6,9,192,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7101 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 276 104 49 224 224 224 480), lower := (rows 7 11 276 104 49 32 64 128 256), losses := [] }

theorem u7101 : Upper (D 8) (R 8) [6,9,272,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7102 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 276 104 81 160 224 160 416), lower := (rows 7 11 276 104 81 32 64 128 256), losses := [] }

theorem u7102 : Upper (D 8) (R 8) [6,9,272,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7103 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 276 104 112 161 225 161 417), lower := (rows 7 11 276 104 112 32 64 128 256), losses := [] }

theorem u7103 : Upper (D 8) (R 8) [6,9,272,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7104 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 276 104 145 224 224 224 480), lower := (rows 7 11 276 104 145 32 64 128 256), losses := [] }

theorem u7104 : Upper (D 8) (R 8) [6,9,272,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7105 : Route 9 := (fun mask => (mask,id))

def c7105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7105 : Upper (D 8) (R 8) [6,9,272,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,272,96,160] 13 (by decide) (choices 1) [1,64,128] r7105 c7105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u934
  · exact u935
  · exact u936

def r7106 : Route 9 := (fun mask => (mask,id))

def c7106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7106 : Upper (D 8) (R 8) [6,9,272,96,192] 13 := by
  apply FastRouting.sound _ _ [6,9,272,96,192] 13 (by decide) (choices 1) [1,128] r7106 c7106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u937
  · exact u938

def b7107 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 276 200 49 224 224 224 480), lower := (rows 7 11 276 200 49 32 64 128 256), losses := [] }

theorem u7107 : Upper (D 8) (R 8) [6,9,272,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7108 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 276 200 81 160 224 160 416), lower := (rows 7 11 276 200 81 32 64 128 256), losses := [] }

theorem u7108 : Upper (D 8) (R 8) [6,9,272,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7109 : Route 9 := (fun mask => (mask,id))

def c7109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7109 : Upper (D 8) (R 8) [6,9,272,192,96] 13 := by
  apply FastRouting.sound _ _ [6,9,272,192,96] 13 (by decide) (choices 1) [1,128] r7109 c7109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u939
  · exact u940

def b7110 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 276 200 208 33 97 161 289), lower := (rows 7 11 276 200 208 32 64 128 256), losses := [] }

theorem u7110 : Upper (D 8) (R 8) [6,9,272,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7111 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 292 56 49 224 192 192 448), lower := (rows 7 11 292 56 49 32 64 128 256), losses := [] }

theorem u7111 : Upper (D 8) (R 8) [6,9,288,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7112 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 56 81 224 224 224 480), lower := (rows 7 11 292 56 81 32 64 128 256), losses := [] }

theorem u7112 : Upper (D 8) (R 8) [6,9,288,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7113 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 292 56 112 225 193 193 449), lower := (rows 7 11 292 56 112 32 64 128 256), losses := [] }

theorem u7113 : Upper (D 8) (R 8) [6,9,288,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7114 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7114 : Upper (D 8) (R 8) [6,9,288,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,288,48,192] 13 (by decide) (choices 1) [1,64] r7114 c7114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u941
  · exact u942

def b7115 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 88 49 224 224 224 480), lower := (rows 7 11 292 88 49 32 64 128 256), losses := [] }

theorem u7115 : Upper (D 8) (R 8) [6,9,288,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7116 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 292 88 81 160 224 160 416), lower := (rows 7 11 292 88 81 32 64 128 256), losses := [] }

theorem u7116 : Upper (D 8) (R 8) [6,9,288,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7117 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 292 88 112 161 225 161 417), lower := (rows 7 11 292 88 112 32 64 128 256), losses := [] }

theorem u7117 : Upper (D 8) (R 8) [6,9,288,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7118 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 88 145 224 224 224 480), lower := (rows 7 11 292 88 145 32 64 128 256), losses := [] }

theorem u7118 : Upper (D 8) (R 8) [6,9,288,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7119 : Route 9 := (fun mask => (mask,id))

def c7119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7119 : Upper (D 8) (R 8) [6,9,288,80,160] 13 := by
  apply FastRouting.sound _ _ [6,9,288,80,160] 13 (by decide) (choices 1) [1,64,128] r7119 c7119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u943
  · exact u944
  · exact u945

def b7120 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 292 88 208 161 225 161 417), lower := (rows 7 11 292 88 208 32 64 128 256), losses := [] }

theorem u7120 : Upper (D 8) (R 8) [6,9,288,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7121 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 104 49 240 208 208 464), lower := (rows 7 11 292 104 49 32 64 128 256), losses := [] }

theorem u7121 : Upper (D 8) (R 8) [6,9,288,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7122 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 104 81 176 240 176 432), lower := (rows 7 11 292 104 81 32 64 128 256), losses := [] }

theorem u7122 : Upper (D 8) (R 8) [6,9,288,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7123 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 292 104 112 177 209 145 401), lower := (rows 7 11 292 104 112 32 64 128 256), losses := [] }

theorem u7123 : Upper (D 8) (R 8) [6,9,288,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7124 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 104 145 240 240 240 496), lower := (rows 7 11 292 104 145 32 64 128 256), losses := [] }

theorem u7124 : Upper (D 8) (R 8) [6,9,288,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7125 : Route 9 := (fun mask => (mask,id))

def c7125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7125 : Upper (D 8) (R 8) [6,9,288,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,288,96,160] 13 (by decide) (choices 1) [1,16,64,128] r7125 c7125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u946
  · exact u947
  · exact u948
  · exact u949

def r7126 : Route 9 := (fun mask => (mask,id))

def c7126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7126 : Upper (D 8) (R 8) [6,9,288,96,192] 13 := by
  apply FastRouting.sound _ _ [6,9,288,96,192] 13 (by decide) (choices 1) [1,16,128] r7126 c7126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u950
  · exact u951
  · exact u952

def b7127 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 200 49 240 240 240 496), lower := (rows 7 11 292 200 49 32 64 128 256), losses := [] }

theorem u7127 : Upper (D 8) (R 8) [6,9,288,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7128 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 200 81 176 240 176 432), lower := (rows 7 11 292 200 81 32 64 128 256), losses := [] }

theorem u7128 : Upper (D 8) (R 8) [6,9,288,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7129 : Route 9 := (fun mask => (mask,id))

def c7129 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7129 : Upper (D 8) (R 8) [6,9,288,192,96] 13 := by
  apply FastRouting.sound _ _ [6,9,288,192,96] 13 (by decide) (choices 1) [1,16,128] r7129 c7129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u953
  · exact u954
  · exact u955

def b7130 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 292 200 208 49 113 177 305), lower := (rows 7 11 292 200 208 32 64 128 256), losses := [] }

theorem u7130 : Upper (D 8) (R 8) [6,9,288,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7131 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 7 11 324 56 49 224 224 224 480), lower := (rows 7 11 324 56 49 32 64 128 256), losses := [] }

theorem u7131 : Upper (D 8) (R 8) [6,9,320,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7132 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 324 56 81 160 224 160 416), lower := (rows 7 11 324 56 81 32 64 128 256), losses := [] }

theorem u7132 : Upper (D 8) (R 8) [6,9,320,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7133 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 324 56 112 161 225 161 417), lower := (rows 7 11 324 56 112 32 64 128 256), losses := [] }

theorem u7133 : Upper (D 8) (R 8) [6,9,320,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7134 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 324 56 145 224 224 224 480), lower := (rows 7 11 324 56 145 32 64 128 256), losses := [] }

theorem u7134 : Upper (D 8) (R 8) [6,9,320,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7135 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 324 56 176 225 225 225 481), lower := (rows 7 11 324 56 176 32 64 128 256), losses := [] }

theorem u7135 : Upper (D 8) (R 8) [6,9,320,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7136 : Route 9 := (fun mask => (mask,id))

def c7136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7136 : Upper (D 8) (R 8) [6,9,320,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,320,48,192] 13 (by decide) (choices 1) [1,128] r7136 c7136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u956
  · exact u957

def b7137 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 324 152 49 224 224 224 480), lower := (rows 7 11 324 152 49 32 64 128 256), losses := [] }

theorem u7137 : Upper (D 8) (R 8) [6,9,320,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7138 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 324 152 81 160 224 160 416), lower := (rows 7 11 324 152 81 32 64 128 256), losses := [] }

theorem u7138 : Upper (D 8) (R 8) [6,9,320,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7139 : Route 9 := (fun mask => (mask,id))

def c7139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7139 : Upper (D 8) (R 8) [6,9,320,144,96] 13 := by
  apply FastRouting.sound _ _ [6,9,320,144,96] 13 (by decide) (choices 1) [1,128] r7139 c7139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u958
  · exact u959

#print axioms u7139
end Delivery.IrregularNine14.P08
