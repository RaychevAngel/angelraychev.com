import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0142

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25080 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 28 11 336 33 226 162 418), lower := (rows 37 194 28 11 336 33 64 128 256), losses := [] }

theorem u25080 : Upper (D 7) (R 7) [36,192,24,3,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25081 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(0,7),(2,1),(4,1)], upper := (rows 37 194 28 11 336 34 225 161 417), lower := (rows 37 194 28 11 336 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 32 65 129 257), good := (rows 501 192 28 477 336 32 64 128 256) },{ target := 6, region := (rows 5 2 4 8 16 42 0 141 269), good := (rows 421 162 445 427 272 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 42 64 0 256), good := (rows 37 98 61 43 336 34 64 0 256) }] }

theorem u25081 : Upper (D 7) (R 7) [36,192,24,3,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25082 : Route 9 := (fun mask => (mask,id))

def c25082 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25082 : Upper (D 7) (R 7) [36,192,24,3,320,128] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3,320,128] 13 (by decide) (choices 1) [1,2,32] r25082 c25082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8542
  · exact u8543
  · exact u8544

def b25083 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 28 42 81 33 450 386 386), lower := (rows 37 194 28 42 81 33 64 128 256), losses := [] }

theorem u25083 : Upper (D 7) (R 7) [36,192,24,34,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25084 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 28 42 81 34 449 385 385), lower := (rows 37 194 28 42 81 34 64 128 256), losses := [] }

theorem u25084 : Upper (D 7) (R 7) [36,192,24,34,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25085 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 37 194 28 42 81 160 323 387 259), lower := (rows 37 194 28 42 81 160 64 128 256), losses := [] }

theorem u25085 : Upper (D 7) (R 7) [36,192,24,34,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25086 : Route 9 := (fun mask => (mask,id))

def c25086 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25086 : Upper (D 7) (R 7) [36,192,24,34,65,256] 13 := by
  apply FastRouting.sound _ _ [36,192,24,34,65,256] 13 (by decide) (choices 1) [1,2,128] r25086 c25086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8545
  · exact u8546
  · exact u8547

def b25087 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 28 42 273 33 194 194 450), lower := (rows 37 194 28 42 273 33 64 128 256), losses := [] }

theorem u25087 : Upper (D 7) (R 7) [36,192,24,34,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25088 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 469, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 194 28 42 273 34 193 193 449), lower := (rows 37 194 28 42 273 34 64 128 256), losses := [] }

theorem u25088 : Upper (D 7) (R 7) [36,192,24,34,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25089 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 405, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,6)], upper := (rows 37 194 28 42 273 96 195 131 387), lower := (rows 37 194 28 42 273 96 64 128 256), losses := [] }

theorem u25089 : Upper (D 7) (R 7) [36,192,24,34,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25090 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 28 42 274 33 193 193 449), lower := (rows 37 194 28 42 274 33 64 128 256), losses := [] }

theorem u25090 : Upper (D 7) (R 7) [36,192,24,34,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25091 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 405, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,6)], upper := (rows 37 194 28 42 274 96 193 129 385), lower := (rows 37 194 28 42 274 96 64 128 256), losses := [] }

theorem u25091 : Upper (D 7) (R 7) [36,192,24,34,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25092 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 28 42 336 33 195 131 387), lower := (rows 37 194 28 42 336 33 64 128 256), losses := [] }

theorem u25092 : Upper (D 7) (R 7) [36,192,24,34,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25093 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 469, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 194 28 42 336 34 193 129 385), lower := (rows 37 194 28 42 336 34 64 128 256), losses := [] }

theorem u25093 : Upper (D 7) (R 7) [36,192,24,34,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25094 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 37 194 28 42 336 160 67 131 259), lower := (rows 37 194 28 42 336 160 64 128 256), losses := [] }

theorem u25094 : Upper (D 7) (R 7) [36,192,24,34,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25095 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 450, targets := 1 }], pairs := [(1,0),(2,6),(2,7),(4,6)], upper := (rows 37 194 28 73 145 34 354 418 290), lower := (rows 37 194 28 73 145 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 17 34 0 162 290), good := (rows 437 418 28 29 145 418 0 128 256) },{ target := 7, region := (rows 1 2 20 9 16 34 98 0 290), good := (rows 365 354 28 73 29 354 64 0 256) }] }

theorem u25095 : Upper (D 7) (R 7) [36,192,24,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25096 : Route 9 := (fun mask => (mask,id))

def c25096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25096 : Upper (D 7) (R 7) [36,192,24,65,129,256] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,129,256] 13 (by decide) (choices 1) [2,32] r25096 c25096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8548
  · exact u8549

def b25097 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 61, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 194 28 73 176 33 322 386 258), lower := (rows 37 194 28 73 176 33 64 128 256), losses := [] }

theorem u25097 : Upper (D 7) (R 7) [36,192,24,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25098 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 1, region := 48, targets := 65 }], pairs := [(1,5),(3,5),(4,0),(4,6)], upper := (rows 37 194 28 73 176 34 323 387 259), lower := (rows 37 194 28 73 176 34 64 128 256), losses := [] }

theorem u25098 : Upper (D 7) (R 7) [36,192,24,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25099 : Route 9 := (fun mask => (mask,id))

def c25099 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25099 : Upper (D 7) (R 7) [36,192,24,65,160,256] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,160,256] 13 (by decide) (choices 1) [1,2] r25099 c25099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8550
  · exact u8551

def r25100 : Route 9 := (fun mask => (mask,id))

def c25100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25100 : Upper (D 7) (R 7) [36,192,24,65,257,2] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,257,2] 13 (by decide) (choices 1) [2,32,128] r25100 c25100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8552
  · exact u8553
  · exact u8554

def r25101 : Route 9 := (fun mask => (mask,id))

def c25101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25101 : Upper (D 7) (R 7) [36,192,24,65,257,128] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,257,128] 13 (by decide) (choices 1) [2,32] r25101 c25101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8555
  · exact u8556

def b25102 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 28 73 274 33 226 162 418), lower := (rows 37 194 28 73 274 33 64 128 256), losses := [] }

theorem u25102 : Upper (D 7) (R 7) [36,192,24,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25103 : Route 9 := (fun mask => (mask,id))

def c25103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25103 : Upper (D 7) (R 7) [36,192,24,65,258,2] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,258,2] 13 (by decide) (choices 1) [1,32,128] r25103 c25103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8557
  · exact u8558
  · exact u8559

def r25104 : Route 9 := (fun mask => (mask,id))

def c25104 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25104 : Upper (D 7) (R 7) [36,192,24,65,258,128] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,258,128] 13 (by decide) (choices 1) [1,2,32] r25104 c25104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8560
  · exact u8561
  · exact u8562

def b25105 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 28 73 304 33 194 130 386), lower := (rows 37 194 28 73 304 33 64 128 256), losses := [] }

theorem u25105 : Upper (D 7) (R 7) [36,192,24,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25106 : Route 9 := (fun mask => (mask,id))

def c25106 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25106 : Upper (D 7) (R 7) [36,192,24,65,288,2] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,288,2] 13 (by decide) (choices 1) [1,2,128] r25106 c25106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8563
  · exact u8564
  · exact u8565

def r25107 : Route 9 := (fun mask => (mask,id))

def c25107 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25107 : Upper (D 7) (R 7) [36,192,24,65,288,128] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,288,128] 13 (by decide) (choices 1) [1,2] r25107 c25107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8566
  · exact u8567

def b25108 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 28 73 400 33 98 162 290), lower := (rows 37 194 28 73 400 33 64 128 256), losses := [] }

theorem u25108 : Upper (D 7) (R 7) [36,192,24,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25109 : Route 9 := (fun mask => (mask,id))

def c25109 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25109 : Upper (D 7) (R 7) [36,192,24,65,384,2] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,384,2] 13 (by decide) (choices 1) [1,2,32] r25109 c25109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8568
  · exact u8569
  · exact u8570

def b25110 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 28 104 273 33 194 130 386), lower := (rows 37 194 28 104 273 33 64 128 256), losses := [] }

theorem u25110 : Upper (D 7) (R 7) [36,192,24,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25111 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 40, targets := 129 }], pairs := [(1,5),(3,0),(3,7),(4,5)], upper := (rows 37 194 28 104 273 34 195 131 387), lower := (rows 37 194 28 104 273 34 64 128 256), losses := [] }

theorem u25111 : Upper (D 7) (R 7) [36,192,24,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25112 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 40, targets := 1 },{ cop := 1, region := 40, targets := 2 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 37 194 28 104 273 160 67 131 259), lower := (rows 37 194 28 104 273 160 64 128 256), losses := [] }

theorem u25112 : Upper (D 7) (R 7) [36,192,24,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25113 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 28 104 274 33 195 131 387), lower := (rows 37 194 28 104 274 33 64 128 256), losses := [] }

theorem u25113 : Upper (D 7) (R 7) [36,192,24,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25114 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 40, targets := 129 }], pairs := [(1,5),(3,0),(3,7),(4,5)], upper := (rows 37 194 28 104 274 34 193 129 385), lower := (rows 37 194 28 104 274 34 64 128 256), losses := [] }

theorem u25114 : Upper (D 7) (R 7) [36,192,24,96,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25115 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 40, targets := 1 },{ cop := 1, region := 40, targets := 2 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 37 194 28 104 274 160 67 131 259), lower := (rows 37 194 28 104 274 160 64 128 256), losses := [] }

theorem u25115 : Upper (D 7) (R 7) [36,192,24,96,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25116 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 28 104 400 33 67 131 259), lower := (rows 37 194 28 104 400 33 64 128 256), losses := [] }

theorem u25116 : Upper (D 7) (R 7) [36,192,24,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25117 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 40, targets := 129 }], pairs := [(1,5),(3,0),(3,7),(4,5)], upper := (rows 37 194 28 104 400 34 67 131 259), lower := (rows 37 194 28 104 400 34 64 128 256), losses := [] }

theorem u25117 : Upper (D 7) (R 7) [36,192,24,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25118 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 11 50 40 464 400 400), lower := (rows 37 194 69 11 50 40 64 128 256), losses := [] }

theorem u25118 : Upper (D 7) (R 7) [36,192,65,3,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25118 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25119 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 11 50 48 456 392 392), lower := (rows 37 194 69 11 50 48 64 128 256), losses := [] }

theorem u25119 : Upper (D 7) (R 7) [36,192,65,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25119 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25120 : PairBound 9 := { available := 280, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 69 11 50 160 344 408 280), lower := (rows 37 194 69 11 50 160 64 128 256), losses := [] }

theorem u25120 : Upper (D 7) (R 7) [36,192,65,3,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25121 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 194 69 11 50 288 216 152 408), lower := (rows 37 194 69 11 50 288 64 128 256), losses := [] }

theorem u25121 : Upper (D 7) (R 7) [36,192,65,3,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25121 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25122 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 69 11 152 34 368 432 304), lower := (rows 37 194 69 11 152 34 64 128 256), losses := [] }

theorem u25122 : Upper (D 7) (R 7) [36,192,65,3,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25123 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 194 69 11 152 48 354 418 290), lower := (rows 37 194 69 11 152 48 64 128 256), losses := [] }

theorem u25123 : Upper (D 7) (R 7) [36,192,65,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25123 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25124 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 194 69 11 152 288 114 178 306), lower := (rows 37 194 69 11 152 288 64 128 256), losses := [] }

theorem u25124 : Upper (D 7) (R 7) [36,192,65,3,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25124 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25125 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 69 11 176 34 344 408 280), lower := (rows 37 194 69 11 176 34 64 128 256), losses := [] }

theorem u25125 : Upper (D 7) (R 7) [36,192,65,3,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25126 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 11 176 40 338 402 274), lower := (rows 37 194 69 11 176 40 64 128 256), losses := [] }

theorem u25126 : Upper (D 7) (R 7) [36,192,65,3,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25126 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25127 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 69 11 176 48 330 394 266), lower := (rows 37 194 69 11 176 48 64 128 256), losses := [] }

theorem u25127 : Upper (D 7) (R 7) [36,192,65,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25127 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25128 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 194 69 11 176 288 90 154 282), lower := (rows 37 194 69 11 176 288 64 128 256), losses := [] }

theorem u25128 : Upper (D 7) (R 7) [36,192,65,3,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25128 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25129 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 11 274 40 240 176 432), lower := (rows 37 194 69 11 274 40 64 128 256), losses := [] }

theorem u25129 : Upper (D 7) (R 7) [36,192,65,3,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25129 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25130 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 194 69 11 274 48 232 168 424), lower := (rows 37 194 69 11 274 48 64 128 256), losses := [] }

theorem u25130 : Upper (D 7) (R 7) [36,192,65,3,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25130 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25131 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 37, targets := 2 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 194 69 11 274 160 120 184 312), lower := (rows 37 194 69 11 274 160 64 128 256), losses := [] }

theorem u25131 : Upper (D 7) (R 7) [36,192,65,3,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25132 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 69 11 280 34 240 176 432), lower := (rows 37 194 69 11 280 34 64 128 256), losses := [] }

theorem u25132 : Upper (D 7) (R 7) [36,192,65,3,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25133 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 194 69 11 280 48 226 162 418), lower := (rows 37 194 69 11 280 48 64 128 256), losses := [] }

theorem u25133 : Upper (D 7) (R 7) [36,192,65,3,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25133 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25134 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 37, targets := 2 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 194 69 11 280 160 114 178 306), lower := (rows 37 194 69 11 280 160 64 128 256), losses := [] }

theorem u25134 : Upper (D 7) (R 7) [36,192,65,3,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25135 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 69 11 304 34 216 152 408), lower := (rows 37 194 69 11 304 34 64 128 256), losses := [] }

theorem u25135 : Upper (D 7) (R 7) [36,192,65,3,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25136 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 11 304 40 210 146 402), lower := (rows 37 194 69 11 304 40 64 128 256), losses := [] }

theorem u25136 : Upper (D 7) (R 7) [36,192,65,3,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25136 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25137 : PairBound 9 := { available := 138, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 194 69 11 304 48 202 138 394), lower := (rows 37 194 69 11 304 48 64 128 256), losses := [] }

theorem u25137 : Upper (D 7) (R 7) [36,192,65,3,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25137 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25138 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 37, targets := 2 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 194 69 11 304 160 90 154 282), lower := (rows 37 194 69 11 304 160 64 128 256), losses := [] }

theorem u25138 : Upper (D 7) (R 7) [36,192,65,3,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25139 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 69 11 400 34 120 184 312), lower := (rows 37 194 69 11 400 34 64 128 256), losses := [] }

theorem u25139 : Upper (D 7) (R 7) [36,192,65,3,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u25139
end Delivery.IrregularNine14.P07
