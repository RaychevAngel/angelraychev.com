import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0148
import IrregularNine14P07C0149

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25560 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 56, targets := 1 },{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 48, targets := 64 }], pairs := [(1,5),(3,0),(4,0),(4,6)], upper := (rows 37 194 268 88 176 34 67 131 259), lower := (rows 37 194 268 88 176 34 64 128 256), losses := [] }

theorem u25560 : Upper (D 7) (R 7) [36,192,264,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25561 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 268 104 19 33 210 146 402), lower := (rows 37 194 268 104 19 33 64 128 256), losses := [] }

theorem u25561 : Upper (D 7) (R 7) [36,192,264,96,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25562 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 1, region := 40, targets := 129 }], pairs := [(1,5),(3,0),(3,7),(4,5)], upper := (rows 37 194 268 104 19 34 209 145 401), lower := (rows 37 194 268 104 19 34 64 128 256), losses := [] }

theorem u25562 : Upper (D 7) (R 7) [36,192,264,96,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25563 : Route 9 := (fun mask => (mask,id))

def c25563 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25563 : Upper (D 7) (R 7) [36,192,264,96,3,16] 13 := by
  apply FastRouting.sound _ _ [36,192,264,96,3,16] 13 (by decide) (choices 1) [1,2,128] r25563 c25563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8917
  · exact u8918
  · exact u8919

def b25564 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 1, region := 40, targets := 1 },{ cop := 1, region := 40, targets := 2 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 37 194 268 104 19 160 83 147 275), lower := (rows 37 194 268 104 19 160 64 128 256), losses := [] }

theorem u25564 : Upper (D 7) (R 7) [36,192,264,96,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25565 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 268 104 145 33 82 146 274), lower := (rows 37 194 268 104 145 33 64 128 256), losses := [] }

theorem u25565 : Upper (D 7) (R 7) [36,192,264,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25566 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 1, region := 40, targets := 129 }], pairs := [(1,5),(3,0),(3,7),(4,5)], upper := (rows 37 194 268 104 145 34 83 147 275), lower := (rows 37 194 268 104 145 34 64 128 256), losses := [] }

theorem u25566 : Upper (D 7) (R 7) [36,192,264,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25567 : Route 9 := (fun mask => (mask,id))

def c25567 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25567 : Upper (D 7) (R 7) [36,192,264,96,129,16] 13 := by
  apply FastRouting.sound _ _ [36,192,264,96,129,16] 13 (by decide) (choices 1) [1,2] r25567 c25567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8920
  · exact u8921

def b25568 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 48, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 194 324 11 50 33 216 152 408), lower := (rows 37 194 324 11 50 33 64 128 256), losses := [] }

theorem u25568 : Upper (D 7) (R 7) [36,192,320,3,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25569 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 48, targets := 129 },{ cop := 4, region := 453, targets := 2 }], pairs := [(0,1),(4,0),(4,7)], upper := (rows 37 194 324 11 50 40 209 145 401), lower := (rows 37 194 324 11 50 40 64 128 256), losses := [] }

theorem u25569 : Upper (D 7) (R 7) [36,192,320,3,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25569 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25570 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 324 11 50 48 201 137 393), lower := (rows 37 194 324 11 50 48 64 128 256), losses := [] }

theorem u25570 : Upper (D 7) (R 7) [36,192,320,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25570 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25571 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 324 11 50 160 89 153 281), lower := (rows 37 194 324 11 50 160 64 128 256), losses := [] }

theorem u25571 : Upper (D 7) (R 7) [36,192,320,3,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25572 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 324 11 56 33 210 146 402), lower := (rows 37 194 324 11 56 33 64 128 256), losses := [] }

theorem u25572 : Upper (D 7) (R 7) [36,192,320,3,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25573 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 48, targets := 129 },{ cop := 4, region := 453, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,7)], upper := (rows 37 194 324 11 56 34 209 145 401), lower := (rows 37 194 324 11 56 34 64 128 256), losses := [] }

theorem u25573 : Upper (D 7) (R 7) [36,192,320,3,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25574 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 324 11 56 48 195 131 387), lower := (rows 37 194 324 11 56 48 64 128 256), losses := [] }

theorem u25574 : Upper (D 7) (R 7) [36,192,320,3,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25574 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25575 : Route 9 := (fun mask => (mask,id))

def c25575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25575 : Upper (D 7) (R 7) [36,192,320,3,40,128] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,40,128] 13 (by decide) (choices 1) [1,2,16] r25575 c25575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8922
  · exact u8923
  · exact u8924

def r25576 : Route 9 := (fun mask => (mask,id))

def c25576 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25576 : Upper (D 7) (R 7) [36,192,320,3,129,2] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,129,2] 13 (by decide) (choices 1) [8,16,32] r25576 c25576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8925
  · exact u8926
  · exact u8927

def r25577 : Route 9 := (fun mask => (mask,id))

def c25577 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25577 : Upper (D 7) (R 7) [36,192,320,3,129,8] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,129,8] 13 (by decide) (choices 1) [2,16,32] r25577 c25577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8928
  · exact u8929
  · exact u8930

def r25578 : Route 9 := (fun mask => (mask,id))

def c25578 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25578 : Upper (D 7) (R 7) [36,192,320,3,129,16] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,129,16] 13 (by decide) (choices 1) [2,8,32] r25578 c25578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8931
  · exact u8932
  · exact u8933

def b25579 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 176, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 194 324 11 152 33 114 178 306), lower := (rows 37 194 324 11 152 33 64 128 256), losses := [] }

theorem u25579 : Upper (D 7) (R 7) [36,192,320,3,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25580 : Route 9 := (fun mask => (mask,id))

def c25580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25580 : Upper (D 7) (R 7) [36,192,320,3,136,2] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,136,2] 13 (by decide) (choices 1) [1,16,32] r25580 c25580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8934
  · exact u8935
  · exact u8936

def r25581 : Route 9 := (fun mask => (mask,id))

def c25581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25581 : Upper (D 7) (R 7) [36,192,320,3,136,16] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,136,16] 13 (by decide) (choices 1) [1,2,32] r25581 c25581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8937
  · exact u8938
  · exact u8939

def b25582 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 176, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 194 324 11 176 33 90 154 282), lower := (rows 37 194 324 11 176 33 64 128 256), losses := [] }

theorem u25582 : Upper (D 7) (R 7) [36,192,320,3,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25583 : Route 9 := (fun mask => (mask,id))

def c25583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25583 : Upper (D 7) (R 7) [36,192,320,3,160,2] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,160,2] 13 (by decide) (choices 1) [1,8,16] r25583 c25583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8940
  · exact u8941
  · exact u8942

def r25584 : Route 9 := (fun mask => (mask,id))

def c25584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25584 : Upper (D 7) (R 7) [36,192,320,3,160,8] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,160,8] 13 (by decide) (choices 1) [1,2,16] r25584 c25584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8943
  · exact u8944
  · exact u8945

def b25585 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 324 11 176 48 75 139 267), lower := (rows 37 194 324 11 176 48 64 128 256), losses := [] }

theorem u25585 : Upper (D 7) (R 7) [36,192,320,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25585 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25586 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 324 25 26 33 226 162 418), lower := (rows 37 194 324 25 26 33 64 128 256), losses := [] }

theorem u25586 : Upper (D 7) (R 7) [36,192,320,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25587 : Route 9 := (fun mask => (mask,id))

def c25587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25587 : Upper (D 7) (R 7) [36,192,320,17,10,2] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,10,2] 13 (by decide) (choices 1) [1,32,128] r25587 c25587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8946
  · exact u8947
  · exact u8948

def r25588 : Route 9 := (fun mask => (mask,id))

def c25588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25588 : Upper (D 7) (R 7) [36,192,320,17,10,128] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,10,128] 13 (by decide) (choices 1) [1,2,32] r25588 c25588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8949
  · exact u8950
  · exact u8951

def b25589 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 324 25 50 33 202 138 394), lower := (rows 37 194 324 25 50 33 64 128 256), losses := [] }

theorem u25589 : Upper (D 7) (R 7) [36,192,320,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25590 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 461, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 194 324 25 50 34 201 137 393), lower := (rows 37 194 324 25 50 34 64 128 256), losses := [] }

theorem u25590 : Upper (D 7) (R 7) [36,192,320,17,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25591 : Route 9 := (fun mask => (mask,id))

def c25591 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25591 : Upper (D 7) (R 7) [36,192,320,17,34,8] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,34,8] 13 (by decide) (choices 1) [1,2,128] r25591 c25591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8952
  · exact u8953
  · exact u8954

def b25592 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 324 25 50 160 75 139 267), lower := (rows 37 194 324 25 50 160 64 128 256), losses := [] }

theorem u25592 : Upper (D 7) (R 7) [36,192,320,17,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25593 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 324 25 152 33 98 162 290), lower := (rows 37 194 324 25 152 33 64 128 256), losses := [] }

theorem u25593 : Upper (D 7) (R 7) [36,192,320,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25594 : Route 9 := (fun mask => (mask,id))

def c25594 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25594 : Upper (D 7) (R 7) [36,192,320,17,136,2] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,136,2] 13 (by decide) (choices 1) [1,2,32] r25594 c25594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8955
  · exact u8956
  · exact u8957

def b25595 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 324 25 176 33 74 138 266), lower := (rows 37 194 324 25 176 33 64 128 256), losses := [] }

theorem u25595 : Upper (D 7) (R 7) [36,192,320,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25596 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(4,0),(4,6)], upper := (rows 37 194 324 25 176 34 75 139 267), lower := (rows 37 194 324 25 176 34 64 128 256), losses := [] }

theorem u25596 : Upper (D 7) (R 7) [36,192,320,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25597 : Route 9 := (fun mask => (mask,id))

def c25597 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25597 : Upper (D 7) (R 7) [36,192,320,17,160,8] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,160,8] 13 (by decide) (choices 1) [1,2] r25597 c25597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8958
  · exact u8959

def b25598 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 324 26 56 33 195 131 387), lower := (rows 37 194 324 26 56 33 64 128 256), losses := [] }

theorem u25598 : Upper (D 7) (R 7) [36,192,320,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25599 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 56, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 37 194 324 26 56 34 193 129 385), lower := (rows 37 194 324 26 56 34 64 128 256), losses := [] }

theorem u25599 : Upper (D 7) (R 7) [36,192,320,18,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25600 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 324 26 56 160 67 131 259), lower := (rows 37 194 324 26 56 160 64 128 256), losses := [] }

theorem u25600 : Upper (D 7) (R 7) [36,192,320,18,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25601 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 357, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,7)], upper := (rows 37 194 324 26 145 33 106 170 298), lower := (rows 37 194 324 26 145 33 64 128 256), losses := [] }

theorem u25601 : Upper (D 7) (R 7) [36,192,320,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25602 : Route 9 := (fun mask => (mask,id))

def c25602 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25602 : Upper (D 7) (R 7) [36,192,320,18,129,2] 13 := by
  apply FastRouting.sound _ _ [36,192,320,18,129,2] 13 (by decide) (choices 1) [1,8,32] r25602 c25602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8960
  · exact u8961
  · exact u8962

def r25603 : Route 9 := (fun mask => (mask,id))

def c25603 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25603 : Upper (D 7) (R 7) [36,192,320,18,129,8] 13 := by
  apply FastRouting.sound _ _ [36,192,320,18,129,8] 13 (by decide) (choices 1) [1,2,32] r25603 c25603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8963
  · exact u8964
  · exact u8965

def b25604 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 357, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,7)], upper := (rows 37 194 324 26 176 33 75 139 267), lower := (rows 37 194 324 26 176 33 64 128 256), losses := [] }

theorem u25604 : Upper (D 7) (R 7) [36,192,320,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25605 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 324 26 176 34 73 137 265), lower := (rows 37 194 324 26 176 34 64 128 256), losses := [] }

theorem u25605 : Upper (D 7) (R 7) [36,192,320,18,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25606 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 324 26 176 40 67 131 259), lower := (rows 37 194 324 26 176 40 64 128 256), losses := [] }

theorem u25606 : Upper (D 7) (R 7) [36,192,320,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25606 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25607 : Route 9 := (fun mask => (mask,id))

def c25607 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25607 : Upper (D 7) (R 7) [36,192,320,34,129,1] 13 := by
  apply FastRouting.sound _ _ [36,192,320,34,129,1] 13 (by decide) (choices 1) [2,8,16] r25607 c25607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8966
  · exact u8967
  · exact u8968

def b25608 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 469, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 194 324 42 145 34 89 153 281), lower := (rows 37 194 324 42 145 34 64 128 256), losses := [] }

theorem u25608 : Upper (D 7) (R 7) [36,192,320,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25609 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 324 42 145 40 83 147 275), lower := (rows 37 194 324 42 145 40 64 128 256), losses := [] }

theorem u25609 : Upper (D 7) (R 7) [36,192,320,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25609 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25610 : Route 9 := (fun mask => (mask,id))

def c25610 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25610 : Upper (D 7) (R 7) [36,192,320,34,129,16] 13 := by
  apply FastRouting.sound _ _ [36,192,320,34,129,16] 13 (by decide) (choices 1) [1,2,8] r25610 c25610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8969
  · exact u8970
  · exact u8971

def r25611 : Route 9 := (fun mask => (mask,id))

def c25611 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25611 : Upper (D 7) (R 7) [36,192,320,34,136,1] 13 := by
  apply FastRouting.sound _ _ [36,192,320,34,136,1] 13 (by decide) (choices 1) [1,2,16] r25611 c25611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8972
  · exact u8973
  · exact u8974

def b25612 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 324 42 152 34 81 145 273), lower := (rows 37 194 324 42 152 34 64 128 256), losses := [] }

theorem u25612 : Upper (D 7) (R 7) [36,192,320,34,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25613 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 324 42 152 48 67 131 259), lower := (rows 37 194 324 42 152 48 64 128 256), losses := [] }

theorem u25613 : Upper (D 7) (R 7) [36,192,320,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25613 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25614 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 324 56 145 33 74 138 266), lower := (rows 37 194 324 56 145 33 64 128 256), losses := [] }

theorem u25614 : Upper (D 7) (R 7) [36,192,320,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25615 : Route 9 := (fun mask => (mask,id))

def c25615 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25615 : Upper (D 7) (R 7) [36,192,320,48,129,2] 13 := by
  apply FastRouting.sound _ _ [36,192,320,48,129,2] 13 (by decide) (choices 1) [1,2,8] r25615 c25615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8975
  · exact u8976
  · exact u8977

def b25616 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 194 324 56 145 40 67 131 259), lower := (rows 37 194 324 56 145 40 64 128 256), losses := [] }

theorem u25616 : Upper (D 7) (R 7) [36,192,320,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25616 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25617 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 259 13 26 112 34 192 192 448), lower := (rows 37 259 13 26 112 34 64 128 256), losses := [] }

theorem u25617 : Upper (D 7) (R 7) [36,257,9,18,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25618 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 37 259 13 26 112 96 194 130 386), lower := (rows 37 259 13 26 112 96 64 128 256), losses := [] }

theorem u25618 : Upper (D 7) (R 7) [36,257,9,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25619 : Route 9 := (fun mask => (mask,id))

def c25619 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25619 : Upper (D 7) (R 7) [36,257,9,18,96,128] 13 := by
  apply FastRouting.sound _ _ [36,257,9,18,96,128] 13 (by decide) (choices 1) [2,128] r25619 c25619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8978
  · exact u8979

#print axioms u25619
end Delivery.IrregularNine14.P07
