import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0058

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15180 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 388 25 52 96 71 135 263), lower := (rows 11 98 388 25 52 96 64 128 256), losses := [] }

theorem u15180 : Upper (D 6) (R 6) [10,96,384,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15181 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 98 388 28 49 33 70 198 326), lower := (rows 11 98 388 28 49 33 64 128 256), losses := [] }

theorem u15181 : Upper (D 6) (R 6) [10,96,384,20,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15182 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 98 388 28 49 34 69 197 325), lower := (rows 11 98 388 28 49 34 64 128 256), losses := [] }

theorem u15182 : Upper (D 6) (R 6) [10,96,384,20,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15183 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 452, targets := 32 },{ cop := 4, region := 66, targets := 4 }], pairs := [(1,2),(2,5),(4,1)], upper := (rows 11 98 388 28 49 36 67 195 323), lower := (rows 11 98 388 28 49 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 64 128 256), good := (rows 57 96 420 60 49 36 64 128 256) }] }

theorem u15183 : Upper (D 6) (R 6) [10,96,384,20,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15184 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 388 28 49 96 71 135 263), lower := (rows 11 98 388 28 49 96 64 128 256), losses := [] }

theorem u15184 : Upper (D 6) (R 6) [10,96,384,20,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15185 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 98 388 44 22 33 81 209 337), lower := (rows 11 98 388 44 22 33 64 128 256), losses := [] }

theorem u15185 : Upper (D 6) (R 6) [10,96,384,36,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15186 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 388 44 22 48 65 193 321), lower := (rows 11 98 388 44 22 48 64 128 256), losses := [] }

theorem u15186 : Upper (D 6) (R 6) [10,96,384,36,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15186 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15187 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 388 44 22 96 81 145 273), lower := (rows 11 98 388 44 22 96 64 128 256), losses := [] }

theorem u15187 : Upper (D 6) (R 6) [10,96,384,36,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15188 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 98 388 44 81 33 86 150 278), lower := (rows 11 98 388 44 81 33 64 128 256), losses := [] }

theorem u15188 : Upper (D 6) (R 6) [10,96,384,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15189 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 388 44 81 34 85 149 277), lower := (rows 11 98 388 44 81 34 64 128 256), losses := [] }

theorem u15189 : Upper (D 6) (R 6) [10,96,384,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15190 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 98 388 44 81 36 83 147 275), lower := (rows 11 98 388 44 81 36 64 128 256), losses := [] }

theorem u15190 : Upper (D 6) (R 6) [10,96,384,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15191 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 388 44 81 48 71 135 263), lower := (rows 11 98 388 44 81 48 64 128 256), losses := [] }

theorem u15191 : Upper (D 6) (R 6) [10,96,384,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15191 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15192 : Route 9 := (fun mask => (mask,id))

def c15192 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15192 : Upper (D 6) (R 6) [10,96,384,36,68,1] 13 := by
  apply FastRouting.sound _ _ [10,96,384,36,68,1] 13 (by decide) (choices 1) [1,2,16] r15192 c15192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3488
  · exact u3489
  · exact u3490

def b15193 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 388 44 84 34 81 145 273), lower := (rows 11 98 388 44 84 34 64 128 256), losses := [] }

theorem u15193 : Upper (D 6) (R 6) [10,96,384,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15194 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 388 44 84 48 67 131 259), lower := (rows 11 98 388 44 84 48 64 128 256), losses := [] }

theorem u15194 : Upper (D 6) (R 6) [10,96,384,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15194 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15195 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 98 388 56 21 33 70 198 326), lower := (rows 11 98 388 56 21 33 64 128 256), losses := [] }

theorem u15195 : Upper (D 6) (R 6) [10,96,384,48,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15196 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 388 56 21 34 69 197 325), lower := (rows 11 98 388 56 21 34 64 128 256), losses := [] }

theorem u15196 : Upper (D 6) (R 6) [10,96,384,48,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15197 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 98 388 56 21 36 67 195 323), lower := (rows 11 98 388 56 21 36 64 128 256), losses := [] }

theorem u15197 : Upper (D 6) (R 6) [10,96,384,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15198 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 388 56 21 96 71 135 263), lower := (rows 11 98 388 56 21 96 64 128 256), losses := [] }

theorem u15198 : Upper (D 6) (R 6) [10,96,384,48,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15199 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 336, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 11 131 22 44 112 33 324 452 324), lower := (rows 11 131 22 44 112 33 64 128 256), losses := [] }

theorem u15199 : Upper (D 6) (R 6) [10,129,18,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15200 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 22 44 112 36 321 449 321), lower := (rows 11 131 22 44 112 36 64 128 256), losses := [] }

theorem u15200 : Upper (D 6) (R 6) [10,129,18,36,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15201 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 22 44 112 96 325 389 261), lower := (rows 11 131 22 44 112 96 64 128 256), losses := [] }

theorem u15201 : Upper (D 6) (R 6) [10,129,18,36,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15202 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 22 44 112 288 69 197 325), lower := (rows 11 131 22 44 112 288 64 128 256), losses := [] }

theorem u15202 : Upper (D 6) (R 6) [10,129,18,36,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15202 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15203 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 336, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 11 131 22 44 304 33 68 196 324), lower := (rows 11 131 22 44 304 33 64 128 256), losses := [] }

theorem u15203 : Upper (D 6) (R 6) [10,129,18,36,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15204 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 22 44 304 36 65 193 321), lower := (rows 11 131 22 44 304 36 64 128 256), losses := [] }

theorem u15204 : Upper (D 6) (R 6) [10,129,18,36,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15205 : Route 9 := (fun mask => (mask,id))

def c15205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15205 : Upper (D 6) (R 6) [10,129,18,36,288,64] 13 := by
  apply FastRouting.sound _ _ [10,129,18,36,288,64] 13 (by decide) (choices 1) [1,4] r15205 c15205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3491
  · exact u3492

def b15206 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 336, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 11 131 22 44 336 33 100 228 356), lower := (rows 11 131 22 44 336 33 64 128 256), losses := [] }

theorem u15206 : Upper (D 6) (R 6) [10,129,18,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15207 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 22 44 336 36 97 225 353), lower := (rows 11 131 22 44 336 36 64 128 256), losses := [] }

theorem u15207 : Upper (D 6) (R 6) [10,129,18,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15208 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(3,0)], upper := (rows 11 131 22 44 336 96 101 165 293), lower := (rows 11 131 22 44 336 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 112 64 128 256), good := (rows 10 130 62 44 368 96 96 128 256) }] }

theorem u15208 : Upper (D 6) (R 6) [10,129,18,36,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15209 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 131 22 104 52 33 324 452 324), lower := (rows 11 131 22 104 52 33 64 128 256), losses := [] }

theorem u15209 : Upper (D 6) (R 6) [10,129,18,96,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15210 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 131 22 104 52 36 321 449 321), lower := (rows 11 131 22 104 52 36 64 128 256), losses := [] }

theorem u15210 : Upper (D 6) (R 6) [10,129,18,96,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15211 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 22 104 52 96 325 389 261), lower := (rows 11 131 22 104 52 96 64 128 256), losses := [] }

theorem u15211 : Upper (D 6) (R 6) [10,129,18,96,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15212 : Route 9 := (fun mask => (mask,id))

def c15212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15212 : Upper (D 6) (R 6) [10,129,18,96,36,256] 13 := by
  apply FastRouting.sound _ _ [10,129,18,96,36,256] 13 (by decide) (choices 1) [1,4] r15212 c15212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3493
  · exact u3494

def r15213 : Route 9 := (fun mask => (mask,id))

def c15213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15213 : Upper (D 6) (R 6) [10,129,18,96,257,4] 13 := by
  apply FastRouting.sound _ _ [10,129,18,96,257,4] 13 (by decide) (choices 1) [4,32] r15213 c15213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3495
  · exact u3496

def b15214 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 22 104 273 96 100 164 292), lower := (rows 11 131 22 104 273 96 64 128 256), losses := [] }

theorem u15214 : Upper (D 6) (R 6) [10,129,18,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15215 : Route 9 := (fun mask => (mask,id))

def c15215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15215 : Upper (D 6) (R 6) [10,129,18,96,260,1] 13 := by
  apply FastRouting.sound _ _ [10,129,18,96,260,1] 13 (by decide) (choices 1) [4,32] r15215 c15215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3497
  · exact u3498

def b15216 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 22 104 276 36 97 225 353), lower := (rows 11 131 22 104 276 36 64 128 256), losses := [] }

theorem u15216 : Upper (D 6) (R 6) [10,129,18,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15217 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 22 104 276 96 101 165 293), lower := (rows 11 131 22 104 276 96 64 128 256), losses := [] }

theorem u15217 : Upper (D 6) (R 6) [10,129,18,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15218 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 22 104 304 33 68 196 324), lower := (rows 11 131 22 104 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 56 56 32 103 167 295), good := (rows 478 454 478 504 504 508 64 128 256) }] }

theorem u15218 : Upper (D 6) (R 6) [10,129,18,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15219 : Route 9 := (fun mask => (mask,id))

def c15219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15219 : Upper (D 6) (R 6) [10,129,18,96,288,4] 13 := by
  apply FastRouting.sound _ _ [10,129,18,96,288,4] 13 (by decide) (choices 1) [1,4] r15219 c15219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3499
  · exact u3500

def b15220 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 22 104 304 96 69 133 261), lower := (rows 11 131 22 104 304 96 64 128 256), losses := [] }

theorem u15220 : Upper (D 6) (R 6) [10,129,18,96,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15221 : Route 9 := (fun mask => (mask,id))

def c15221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15221 : Upper (D 6) (R 6) [10,129,18,260,96,1] 13 := by
  apply FastRouting.sound _ _ [10,129,18,260,96,1] 13 (by decide) (choices 1) [4,32] r15221 c15221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3501
  · exact u3502

theorem m15222_1 : Upper (D 6) (R 6) [10,129,18,260,96,4,1] 13 :=
  permutation_upper _ _ _ [10,129,18,260,96,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3501

def r15222 : Route 9 := (fun mask => (mask,id))

def c15222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15222 : Upper (D 6) (R 6) [10,129,18,260,96,4] 13 := by
  apply FastRouting.sound _ _ [10,129,18,260,96,4] 13 (by decide) (choices 1) [1,32] r15222 c15222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m15222_1
  · exact u3503

def b15223 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 22 268 112 96 101 165 293), lower := (rows 11 131 22 268 112 96 64 128 256), losses := [] }

theorem u15223 : Upper (D 6) (R 6) [10,129,18,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15224 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 131 22 296 52 33 68 196 324), lower := (rows 11 131 22 296 52 33 64 128 256), losses := [] }

theorem u15224 : Upper (D 6) (R 6) [10,129,18,288,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15225 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 131 22 296 52 36 65 193 321), lower := (rows 11 131 22 296 52 36 64 128 256), losses := [] }

theorem u15225 : Upper (D 6) (R 6) [10,129,18,288,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15226 : Route 9 := (fun mask => (mask,id))

def c15226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15226 : Upper (D 6) (R 6) [10,129,18,288,36,64] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288,36,64] 13 (by decide) (choices 1) [1,4] r15226 c15226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3504
  · exact u3505

def r15227 : Route 9 := (fun mask => (mask,id))

def c15227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15227 : Upper (D 6) (R 6) [10,129,18,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288,65,4] 13 (by decide) (choices 1) [4,32] r15227 c15227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3506
  · exact u3507

def r15228 : Route 9 := (fun mask => (mask,id))

def c15228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15228 : Upper (D 6) (R 6) [10,129,18,288,65,64] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288,65,64] 13 (by decide) (choices 1) [4,32] r15228 c15228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3508
  · exact u3509

def r15229 : Route 9 := (fun mask => (mask,id))

def c15229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15229 : Upper (D 6) (R 6) [10,129,18,288,68,1] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288,68,1] 13 (by decide) (choices 1) [4,32] r15229 c15229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3510
  · exact u3511

def b15230 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 22 296 84 36 97 225 353), lower := (rows 11 131 22 296 84 36 64 128 256), losses := [] }

theorem u15230 : Upper (D 6) (R 6) [10,129,18,288,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15231 : Route 9 := (fun mask => (mask,id))

def c15231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15231 : Upper (D 6) (R 6) [10,129,18,288,68,64] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288,68,64] 13 (by decide) (choices 1) [1,4,32] r15231 c15231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3512
  · exact u3513
  · exact u3514

def b15232 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 22 296 112 33 68 196 324), lower := (rows 11 131 22 296 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 56 56 32 103 167 295), good := (rows 478 454 478 504 504 508 64 128 256) }] }

theorem u15232 : Upper (D 6) (R 6) [10,129,18,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15233 : Route 9 := (fun mask => (mask,id))

def c15233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15233 : Upper (D 6) (R 6) [10,129,18,288,96,4] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288,96,4] 13 (by decide) (choices 1) [1,4] r15233 c15233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3515
  · exact u3516

def b15234 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 22 296 112 96 69 133 261), lower := (rows 11 131 22 296 112 96 64 128 256), losses := [] }

theorem u15234 : Upper (D 6) (R 6) [10,129,18,288,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15235 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 28 112 34 324 452 324), lower := (rows 11 131 37 28 112 34 64 128 256), losses := [] }

theorem u15235 : Upper (D 6) (R 6) [10,129,33,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15236 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 451, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 37 28 112 36 322 450 322), lower := (rows 11 131 37 28 112 36 64 128 256), losses := [] }

theorem u15236 : Upper (D 6) (R 6) [10,129,33,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15237 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 37 28 112 96 326 390 262), lower := (rows 11 131 37 28 112 96 64 128 256), losses := [] }

theorem u15237 : Upper (D 6) (R 6) [10,129,33,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15238 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 37 28 112 288 70 198 326), lower := (rows 11 131 37 28 112 288 64 128 256), losses := [] }

theorem u15238 : Upper (D 6) (R 6) [10,129,33,20,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15238 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15239 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 28 304 34 68 196 324), lower := (rows 11 131 37 28 304 34 64 128 256), losses := [] }

theorem u15239 : Upper (D 6) (R 6) [10,129,33,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15239
end Delivery.IrregularNine14.P06
