import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0041
import IrregularNine14P09C0042

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6060 : Route 9 := (fun mask => (mask,id))

def c6060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6060 : Upper (D 9) (R 9) [96,12,48,129,192,256] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,192,256] 13 (by decide) (choices 1) [1,2,256] r6060 c6060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2492
  · exact u2493
  · exact u2494

def r6061 : Route 9 := (fun mask => (mask,id))

def c6061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u6061 : Upper (D 9) (R 9) [96,12,48,129,257,2] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,257,2] 13 (by decide) (choices 1) [128,256] r6061 c6061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2495
  · exact u2496

def b6062 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 52 137 273 96 450 386 386), lower := (rows 97 14 52 137 273 96 64 128 256), losses := [] }

theorem u6062 : Upper (D 9) (R 9) [96,12,48,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6062 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6063 : Route 9 := (fun mask => (mask,id))

def c6063 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6063 : Upper (D 9) (R 9) [96,12,48,129,257,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,257,128] 13 (by decide) (choices 1) [2,256] r6063 c6063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2497
  · exact u2498

def b6064 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,8)], upper := (rows 97 14 52 137 273 288 194 194 450), lower := (rows 97 14 52 137 273 288 64 128 256), losses := [] }

theorem u6064 : Upper (D 9) (R 9) [96,12,48,129,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6064 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6065 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 392, targets := 32 }], pairs := [(0,7),(0,8),(3,5),(4,0),(4,5)], upper := (rows 97 14 52 137 274 33 448 448 448), lower := (rows 97 14 52 137 274 33 64 128 256), losses := [] }

theorem u6065 : Upper (D 9) (R 9) [96,12,48,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6065 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6066 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 52 137 274 96 449 385 385), lower := (rows 97 14 52 137 274 96 64 128 256), losses := [] }

theorem u6066 : Upper (D 9) (R 9) [96,12,48,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6066 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6067 : Route 9 := (fun mask => (mask,id))

def c6067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6067 : Upper (D 9) (R 9) [96,12,48,129,258,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,258,128] 13 (by decide) (choices 1) [1,256] r6067 c6067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2499
  · exact u2500

def b6068 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,8)], upper := (rows 97 14 52 137 274 288 193 193 449), lower := (rows 97 14 52 137 274 288 64 128 256), losses := [] }

theorem u6068 : Upper (D 9) (R 9) [96,12,48,129,258,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6068 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6069 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 37, targets := 384 },{ cop := 1, region := 464, targets := 1 }], pairs := [(0,7),(0,8),(2,7),(2,8),(4,0)], upper := (rows 97 14 52 137 336 33 450 386 386), lower := (rows 97 14 52 137 336 33 64 128 256), losses := [] }

theorem u6069 : Upper (D 9) (R 9) [96,12,48,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6069 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6070 : Route 9 := (fun mask => (mask,id))

def c6070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u6070 : Upper (D 9) (R 9) [96,12,48,129,320,2] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,320,2] 13 (by decide) (choices 1) [1,128,256] r6070 c6070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2501
  · exact u2502
  · exact u2503

def r6071 : Route 9 := (fun mask => (mask,id))

def c6071 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6071 : Upper (D 9) (R 9) [96,12,48,129,320,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,320,128] 13 (by decide) (choices 1) [1,2,256] r6071 c6071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2504
  · exact u2505
  · exact u2506

def b6072 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,8)], upper := (rows 97 14 52 137 336 288 195 131 387), lower := (rows 97 14 52 137 336 288 64 128 256), losses := [] }

theorem u6072 : Upper (D 9) (R 9) [96,12,48,129,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6072 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6073 : Route 9 := (fun mask => (mask,id))

def c6073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6073 : Upper (D 9) (R 9) [96,12,48,129,384,1] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,384,1] 13 (by decide) (choices 1) [2,256] r6073 c6073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2507
  · exact u2508

def r6074 : Route 9 := (fun mask => (mask,id))

def c6074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6074 : Upper (D 9) (R 9) [96,12,48,129,384,2] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,384,2] 13 (by decide) (choices 1) [1,256] r6074 c6074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2509
  · exact u2510

def b6075 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 52 137 400 96 323 387 259), lower := (rows 97 14 52 137 400 96 64 128 256), losses := [] }

theorem u6075 : Upper (D 9) (R 9) [96,12,48,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6075 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6076 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,8)], upper := (rows 97 14 52 137 400 288 67 195 323), lower := (rows 97 14 52 137 400 288 64 128 256), losses := [] }

theorem u6076 : Upper (D 9) (R 9) [96,12,48,129,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6076 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6077 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 14 52 138 208 33 321 385 257), lower := (rows 97 14 52 138 208 33 64 128 256), losses := [] }

theorem u6077 : Upper (D 9) (R 9) [96,12,48,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6077 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6078 : Route 9 := (fun mask => (mask,id))

def c6078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6078 : Upper (D 9) (R 9) [96,12,48,130,192,256] 13 := by
  apply FastRouting.sound _ _ [96,12,48,130,192,256] 13 (by decide) (choices 1) [1,256] r6078 c6078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2511
  · exact u2512

def b6079 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 458, targets := 33 },{ cop := 4, region := 36, targets := 64 }], pairs := [(1,0),(1,5),(2,6),(3,0),(3,5)], upper := (rows 97 14 52 138 273 33 448 448 448), lower := (rows 97 14 52 138 273 33 64 128 256), losses := [] }

theorem u6079 : Upper (D 9) (R 9) [96,12,48,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6079 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6080 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 52 138 273 96 449 385 385), lower := (rows 97 14 52 138 273 96 64 128 256), losses := [] }

theorem u6080 : Upper (D 9) (R 9) [96,12,48,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6080 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6081 : PairBound 9 := { available := 321, camps := [{ cop := 5, region := 341, targets := 128 },{ cop := 0, region := 272, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,5),(4,7)], upper := (rows 97 14 52 138 273 160 321 449 321), lower := (rows 97 14 52 138 273 160 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 12 17 0 81 145 273), good := (rows 465 14 478 138 465 128 64 128 256) }] }

theorem u6081 : Upper (D 9) (R 9) [96,12,48,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6081 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6082 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,8)], upper := (rows 97 14 52 138 273 288 193 193 449), lower := (rows 97 14 52 138 273 288 64 128 256), losses := [] }

theorem u6082 : Upper (D 9) (R 9) [96,12,48,130,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6082 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6083 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 37, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(2,7),(2,8),(4,5)], upper := (rows 97 14 52 138 336 33 449 385 385), lower := (rows 97 14 52 138 336 33 64 128 256), losses := [] }

theorem u6083 : Upper (D 9) (R 9) [96,12,48,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6083 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6084 : Route 9 := (fun mask => (mask,id))

def c6084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6084 : Upper (D 9) (R 9) [96,12,48,130,320,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,130,320,128] 13 (by decide) (choices 1) [1,256] r6084 c6084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2513
  · exact u2514

def b6085 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,8)], upper := (rows 97 14 52 138 336 288 193 129 385), lower := (rows 97 14 52 138 336 288 64 128 256), losses := [] }

theorem u6085 : Upper (D 9) (R 9) [96,12,48,130,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6085 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6086 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 0, region := 400, targets := 32 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(2,7),(4,5)], upper := (rows 97 14 52 138 400 33 321 449 321), lower := (rows 97 14 52 138 400 33 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 12 53 0 97 161 289), good := (rows 465 30 478 138 400 465 64 128 256) }] }

theorem u6086 : Upper (D 9) (R 9) [96,12,48,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6086 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6087 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 52 138 400 96 321 385 257), lower := (rows 97 14 52 138 400 96 64 128 256), losses := [] }

theorem u6087 : Upper (D 9) (R 9) [96,12,48,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6087 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6088 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 46, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6),(3,0)], upper := (rows 97 14 52 138 400 288 65 193 321), lower := (rows 97 14 52 138 400 288 64 128 256), losses := [] }

theorem u6088 : Upper (D 9) (R 9) [96,12,48,130,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6088 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6089 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 458, targets := 33 },{ cop := 3, region := 33, targets := 256 }], pairs := [(0,8),(1,0),(1,5),(3,0),(3,5)], upper := (rows 97 14 52 200 145 33 322 386 258), lower := (rows 97 14 52 200 145 33 64 128 256), losses := [] }

theorem u6089 : Upper (D 9) (R 9) [96,12,48,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6089 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6090 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 14 52 200 145 34 321 385 257), lower := (rows 97 14 52 200 145 34 64 128 256), losses := [] }

theorem u6090 : Upper (D 9) (R 9) [96,12,48,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6090 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6091 : Route 9 := (fun mask => (mask,id))

def c6091 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6091 : Upper (D 9) (R 9) [96,12,48,192,129,256] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,129,256] 13 (by decide) (choices 1) [1,2,256] r6091 c6091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2515
  · exact u2516
  · exact u2517

def b6092 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 14 52 200 146 33 321 385 257), lower := (rows 97 14 52 200 146 33 64 128 256), losses := [] }

theorem u6092 : Upper (D 9) (R 9) [96,12,48,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6092 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6093 : Route 9 := (fun mask => (mask,id))

def c6093 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6093 : Upper (D 9) (R 9) [96,12,48,192,130,256] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,130,256] 13 (by decide) (choices 1) [1,256] r6093 c6093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2518
  · exact u2519

def b6094 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 458, targets := 33 },{ cop := 4, region := 36, targets := 64 }], pairs := [(1,0),(1,5),(2,6),(3,0),(3,5)], upper := (rows 97 14 52 200 273 33 450 386 386), lower := (rows 97 14 52 200 273 33 64 128 256), losses := [] }

theorem u6094 : Upper (D 9) (R 9) [96,12,48,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6094 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6095 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 97 14 52 200 273 34 449 385 385), lower := (rows 97 14 52 200 273 34 64 128 256), losses := [] }

theorem u6095 : Upper (D 9) (R 9) [96,12,48,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6095 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6096 : Route 9 := (fun mask => (mask,id))

def c6096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6096 : Upper (D 9) (R 9) [96,12,48,192,257,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,257,128] 13 (by decide) (choices 1) [1,2,256] r6096 c6096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2520
  · exact u2521
  · exact u2522

def b6097 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,8)], upper := (rows 97 14 52 200 273 288 195 131 387), lower := (rows 97 14 52 200 273 288 64 128 256), losses := [] }

theorem u6097 : Upper (D 9) (R 9) [96,12,48,192,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6097 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6098 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 33, targets := 384 },{ cop := 0, region := 392, targets := 32 }], pairs := [(0,7),(0,8),(1,5),(3,5),(4,5)], upper := (rows 97 14 52 200 274 33 449 385 385), lower := (rows 97 14 52 200 274 33 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 45 20 0 97 161 289), good := (rows 457 30 478 200 274 457 64 128 256) }] }

theorem u6098 : Upper (D 9) (R 9) [96,12,48,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6098 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6099 : Route 9 := (fun mask => (mask,id))

def c6099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6099 : Upper (D 9) (R 9) [96,12,48,192,258,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,258,128] 13 (by decide) (choices 1) [1,256] r6099 c6099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2523
  · exact u2524

def b6100 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,8)], upper := (rows 97 14 52 200 274 288 193 129 385), lower := (rows 97 14 52 200 274 288 64 128 256), losses := [] }

theorem u6100 : Upper (D 9) (R 9) [96,12,48,192,258,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6100 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6101 : Route 9 := (fun mask => (mask,id))

def c6101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6101 : Upper (D 9) (R 9) [96,12,48,192,384,1] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,384,1] 13 (by decide) (choices 1) [1,2,256] r6101 c6101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2525
  · exact u2526
  · exact u2527

def b6102 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 97 14 52 200 400 34 321 385 257), lower := (rows 97 14 52 200 400 34 64 128 256), losses := [] }

theorem u6102 : Upper (D 9) (R 9) [96,12,48,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6102 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6103 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,8)], upper := (rows 97 14 52 200 400 288 67 131 259), lower := (rows 97 14 52 200 400 288 64 128 256), losses := [] }

theorem u6103 : Upper (D 9) (R 9) [96,12,48,192,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6103 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6104 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 37, targets := 384 },{ cop := 0, region := 392, targets := 32 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,5)], upper := (rows 97 14 52 392 82 33 449 385 385), lower := (rows 97 14 52 392 82 33 64 128 256), losses := [] }

theorem u6104 : Upper (D 9) (R 9) [96,12,48,384,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6104 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6105 : Route 9 := (fun mask => (mask,id))

def c6105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6105 : Upper (D 9) (R 9) [96,12,48,384,66,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,384,66,128] 13 (by decide) (choices 1) [1,256] r6105 c6105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2528
  · exact u2529

def b6106 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 458, targets := 33 },{ cop := 4, region := 36, targets := 64 }], pairs := [(1,0),(1,5),(2,6),(3,0),(3,5)], upper := (rows 97 14 52 392 145 33 322 450 322), lower := (rows 97 14 52 392 145 33 64 128 256), losses := [] }

theorem u6106 : Upper (D 9) (R 9) [96,12,48,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6106 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6107 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,5),(3,5),(4,5)], upper := (rows 97 14 52 392 145 34 321 449 321), lower := (rows 97 14 52 392 145 34 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 29 17 0 81 145 273), good := (rows 473 14 478 392 473 2 64 128 256) }] }

theorem u6107 : Upper (D 9) (R 9) [96,12,48,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6107 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6108 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 52 392 145 96 323 387 259), lower := (rows 97 14 52 392 145 96 64 128 256), losses := [] }

theorem u6108 : Upper (D 9) (R 9) [96,12,48,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6108 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6109 : Route 9 := (fun mask => (mask,id))

def c6109 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6109 : Upper (D 9) (R 9) [96,12,48,384,129,256] 13 := by
  apply FastRouting.sound _ _ [96,12,48,384,129,256] 13 (by decide) (choices 1) [1,2] r6109 c6109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2530
  · exact u2531

def b6110 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 357, targets := 128 },{ cop := 0, region := 392, targets := 32 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(2,7),(3,5)], upper := (rows 97 14 52 392 146 33 321 449 321), lower := (rows 97 14 52 392 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 45 20 0 97 161 289), good := (rows 457 30 478 392 146 457 64 128 256) }] }

theorem u6110 : Upper (D 9) (R 9) [96,12,48,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6110 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6111 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 52 392 146 96 321 385 257), lower := (rows 97 14 52 392 146 96 64 128 256), losses := [] }

theorem u6111 : Upper (D 9) (R 9) [96,12,48,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6111 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6112 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 54, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6),(4,0)], upper := (rows 97 14 52 392 146 288 65 193 321), lower := (rows 97 14 52 392 146 288 64 128 256), losses := [] }

theorem u6112 : Upper (D 9) (R 9) [96,12,48,384,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6112 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6113 : Route 9 := (fun mask => (mask,id))

def c6113 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6113 : Upper (D 9) (R 9) [96,12,48,384,192,1] 13 := by
  apply FastRouting.sound _ _ [96,12,48,384,192,1] 13 (by decide) (choices 1) [1,2,256] r6113 c6113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2532
  · exact u2533
  · exact u2534

def b6114 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 392, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(3,5),(3,6),(4,5)], upper := (rows 97 14 52 392 208 34 321 385 257), lower := (rows 97 14 52 392 208 34 64 128 256), losses := [] }

theorem u6114 : Upper (D 9) (R 9) [96,12,48,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6114 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6115 : Route 9 := (fun mask => (mask,id))

def c6115 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6115 : Upper (D 9) (R 9) [96,12,48,384,192,256] 13 := by
  apply FastRouting.sound _ _ [96,12,48,384,192,256] 13 (by decide) (choices 1) [1,2] r6115 c6115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2535
  · exact u2536

def b6116 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 58, targets := 320 }], pairs := [(1,6),(1,8),(3,6),(3,8),(4,6)], upper := (rows 97 14 133 152 50 33 320 448 320), lower := (rows 97 14 133 152 50 33 64 128 256), losses := [] }

theorem u6116 : Upper (D 9) (R 9) [96,12,129,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6116 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6117 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 133 152 50 96 321 385 257), lower := (rows 97 14 133 152 50 96 64 128 256), losses := [] }

theorem u6117 : Upper (D 9) (R 9) [96,12,129,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6117 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6118 : Route 9 := (fun mask => (mask,id))

def c6118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6118 : Upper (D 9) (R 9) [96,12,129,144,34,256] 13 := by
  apply FastRouting.sound _ _ [96,12,129,144,34,256] 13 (by decide) (choices 1) [1,256] r6118 c6118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2537
  · exact u2538

def r6119 : Route 9 := (fun mask => (mask,id))

def c6119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u6119 : Upper (D 9) (R 9) [96,12,129,144,257,2] 13 := by
  apply FastRouting.sound _ _ [96,12,129,144,257,2] 13 (by decide) (choices 1) [32,256] r6119 c6119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2539
  · exact u2540

#print axioms u6119
end Delivery.IrregularNine14.P09
