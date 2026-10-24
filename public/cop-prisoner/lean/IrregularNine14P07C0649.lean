import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0442
import IrregularNine14P07C0443
import IrregularNine14P07C0444

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38940 : Route 9 := (fun mask => (mask,id))

def c38940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38940 : Upper (D 7) (R 7) [36,264,66,192,129] 13 := by
  apply FastRouting.sound _ _ [36,264,66,192,129] 13 (by decide) (choices 1) [1,2,16] r38940 c38940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26568
  · exact u26569
  · exact u26570

def b38941 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 37 266 70 200 146 49 113 177 305), lower := (rows 37 266 70 200 146 32 64 128 256), losses := [] }

theorem u38941 : Upper (D 7) (R 7) [36,264,66,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38942 : Route 9 := (fun mask => (mask,id))

def c38942 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38942 : Upper (D 7) (R 7) [36,264,66,192,160] 13 := by
  apply FastRouting.sound _ _ [36,264,66,192,160] 13 (by decide) (choices 1) [1,2,16] r38942 c38942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26571
  · exact u26572
  · exact u26573

def b38943 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 37 266 84 11 19 224 224 224 480), lower := (rows 37 266 84 11 19 32 64 128 256), losses := [] }

theorem u38943 : Upper (D 7) (R 7) [36,264,80,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38944 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 84 11 49 226 194 194 450), lower := (rows 37 266 84 11 49 32 64 128 256), losses := [] }

theorem u38944 : Upper (D 7) (R 7) [36,264,80,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38945 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(3,5)], upper := (rows 37 266 84 11 50 225 193 193 449), lower := (rows 37 266 84 11 50 32 64 128 256), losses := [] }

theorem u38945 : Upper (D 7) (R 7) [36,264,80,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38946 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 11 81 162 226 162 418), lower := (rows 37 266 84 11 81 32 64 128 256), losses := [] }

theorem u38946 : Upper (D 7) (R 7) [36,264,80,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38947 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 4, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 37 266 84 11 82 161 225 161 417), lower := (rows 37 266 84 11 82 32 64 128 256), losses := [] }

theorem u38947 : Upper (D 7) (R 7) [36,264,80,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38948 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 84 11 112 163 195 131 387), lower := (rows 37 266 84 11 112 32 64 128 256), losses := [] }

theorem u38948 : Upper (D 7) (R 7) [36,264,80,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38949 : Route 9 := (fun mask => (mask,id))

def c38949 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38949 : Upper (D 7) (R 7) [36,264,80,3,129] 13 := by
  apply FastRouting.sound _ _ [36,264,80,3,129] 13 (by decide) (choices 1) [2,64,128] r38949 c38949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26574
  · exact u26575
  · exact u26576

def r38950 : Route 9 := (fun mask => (mask,id))

def c38950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38950 : Upper (D 7) (R 7) [36,264,80,3,130] 13 := by
  apply FastRouting.sound _ _ [36,264,80,3,130] 13 (by decide) (choices 1) [1,64,128] r38950 c38950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26577
  · exact u26578
  · exact u26579

def r38951 : Route 9 := (fun mask => (mask,id))

def c38951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38951 : Upper (D 7) (R 7) [36,264,80,3,160] 13 := by
  apply FastRouting.sound _ _ [36,264,80,3,160] 13 (by decide) (choices 1) [1,2,64,128] r38951 c38951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26580
  · exact u26581
  · exact u26582
  · exact u26583

def b38952 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 11 208 163 227 163 419), lower := (rows 37 266 84 11 208 32 64 128 256), losses := [] }

theorem u38952 : Upper (D 7) (R 7) [36,264,80,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38953 : Route 9 := (fun mask => (mask,id))

def c38953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38953 : Upper (D 7) (R 7) [36,264,80,34,3] 13 := by
  apply FastRouting.sound _ _ [36,264,80,34,3] 13 (by decide) (choices 1) [1,64,128] r38953 c38953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26584
  · exact u26585
  · exact u26586

def b38954 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 42 81 163 195 131 387), lower := (rows 37 266 84 42 81 32 64 128 256), losses := [] }

theorem u38954 : Upper (D 7) (R 7) [36,264,80,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38955 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 4, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 37 266 84 42 82 161 193 129 385), lower := (rows 37 266 84 42 82 32 64 128 256), losses := [] }

theorem u38955 : Upper (D 7) (R 7) [36,264,80,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38956 : Route 9 := (fun mask => (mask,id))

def c38956 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38956 : Upper (D 7) (R 7) [36,264,80,34,129] 13 := by
  apply FastRouting.sound _ _ [36,264,80,34,129] 13 (by decide) (choices 1) [1,2,64,128] r38956 c38956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26587
  · exact u26588
  · exact u26589
  · exact u26590

def r38957 : Route 9 := (fun mask => (mask,id))

def c38957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38957 : Upper (D 7) (R 7) [36,264,80,34,130] 13 := by
  apply FastRouting.sound _ _ [36,264,80,34,130] 13 (by decide) (choices 1) [1,64,128] r38957 c38957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26591
  · exact u26592
  · exact u26593

def b38958 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 42 208 163 195 131 387), lower := (rows 37 266 84 42 208 32 64 128 256), losses := [] }

theorem u38958 : Upper (D 7) (R 7) [36,264,80,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38959 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 3, region := 418, targets := 1 },{ cop := 4, region := 228, targets := 1 }], pairs := [(1,0),(1,6),(2,0),(4,6)], upper := (rows 37 266 84 73 19 162 226 162 418), lower := (rows 37 266 84 73 19 32 64 128 256), losses := [] }

theorem u38959 : Upper (D 7) (R 7) [36,264,80,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38960 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 84 73 49 162 194 130 386), lower := (rows 37 266 84 73 49 32 64 128 256), losses := [] }

theorem u38960 : Upper (D 7) (R 7) [36,264,80,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38961 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,5),(1,6),(3,5),(4,6)], upper := (rows 37 266 84 73 50 163 195 131 387), lower := (rows 37 266 84 73 50 32 64 128 256), losses := [] }

theorem u38961 : Upper (D 7) (R 7) [36,264,80,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38962 : Route 9 := (fun mask => (mask,id))

def c38962 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38962 : Upper (D 7) (R 7) [36,264,80,65,129] 13 := by
  apply FastRouting.sound _ _ [36,264,80,65,129] 13 (by decide) (choices 1) [2,128] r38962 c38962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26594
  · exact u26595

def r38963 : Route 9 := (fun mask => (mask,id))

def c38963 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38963 : Upper (D 7) (R 7) [36,264,80,65,130] 13 := by
  apply FastRouting.sound _ _ [36,264,80,65,130] 13 (by decide) (choices 1) [1,2,128] r38963 c38963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26596
  · exact u26597
  · exact u26598

def b38964 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,5),(1,6),(3,5),(4,6)], upper := (rows 37 266 84 73 176 163 195 131 387), lower := (rows 37 266 84 73 176 32 64 128 256), losses := [] }

theorem u38964 : Upper (D 7) (R 7) [36,264,80,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38965 : Route 9 := (fun mask => (mask,id))

def c38965 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38965 : Upper (D 7) (R 7) [36,264,80,66,3] 13 := by
  apply FastRouting.sound _ _ [36,264,80,66,3] 13 (by decide) (choices 1) [1,128] r38965 c38965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26599
  · exact u26600

def b38966 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 84 74 49 163 195 131 387), lower := (rows 37 266 84 74 49 32 64 128 256), losses := [] }

theorem u38966 : Upper (D 7) (R 7) [36,264,80,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38967 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(3,5)], upper := (rows 37 266 84 74 50 161 193 129 385), lower := (rows 37 266 84 74 50 32 64 128 256), losses := [] }

theorem u38967 : Upper (D 7) (R 7) [36,264,80,66,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38968 : Route 9 := (fun mask => (mask,id))

def c38968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38968 : Upper (D 7) (R 7) [36,264,80,66,129] 13 := by
  apply FastRouting.sound _ _ [36,264,80,66,129] 13 (by decide) (choices 1) [1,2,128] r38968 c38968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26601
  · exact u26602
  · exact u26603

def r38969 : Route 9 := (fun mask => (mask,id))

def c38969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38969 : Upper (D 7) (R 7) [36,264,80,66,130] 13 := by
  apply FastRouting.sound _ _ [36,264,80,66,130] 13 (by decide) (choices 1) [1,128] r38969 c38969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26604
  · exact u26605

def r38970 : Route 9 := (fun mask => (mask,id))

def c38970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38970 : Upper (D 7) (R 7) [36,264,80,66,160] 13 := by
  apply FastRouting.sound _ _ [36,264,80,66,160] 13 (by decide) (choices 1) [1,2,128] r38970 c38970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26606
  · exact u26607
  · exact u26608

def r38971 : Route 9 := (fun mask => (mask,id))

def c38971 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38971 : Upper (D 7) (R 7) [36,264,80,96,3] 13 := by
  apply FastRouting.sound _ _ [36,264,80,96,3] 13 (by decide) (choices 1) [1,2,128] r38971 c38971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26609
  · exact u26610
  · exact u26611

def r38972 : Route 9 := (fun mask => (mask,id))

def c38972 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38972 : Upper (D 7) (R 7) [36,264,80,96,129] 13 := by
  apply FastRouting.sound _ _ [36,264,80,96,129] 13 (by decide) (choices 1) [1,2,128] r38972 c38972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26612
  · exact u26613
  · exact u26614

def r38973 : Route 9 := (fun mask => (mask,id))

def c38973 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38973 : Upper (D 7) (R 7) [36,264,80,96,130] 13 := by
  apply FastRouting.sound _ _ [36,264,80,96,130] 13 (by decide) (choices 1) [1,2,128] r38973 c38973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26615
  · exact u26616
  · exact u26617

def r38974 : Route 9 := (fun mask => (mask,id))

def c38974 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38974 : Upper (D 7) (R 7) [36,264,80,129,3] 13 := by
  apply FastRouting.sound _ _ [36,264,80,129,3] 13 (by decide) (choices 1) [2,64,128] r38974 c38974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26618
  · exact u26619
  · exact u26620

def b38975 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 84 137 49 226 194 194 450), lower := (rows 37 266 84 137 49 32 64 128 256), losses := [] }

theorem u38975 : Upper (D 7) (R 7) [36,264,80,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38976 : Route 9 := (fun mask => (mask,id))

def c38976 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38976 : Upper (D 7) (R 7) [36,264,80,129,34] 13 := by
  apply FastRouting.sound _ _ [36,264,80,129,34] 13 (by decide) (choices 1) [1,2,64,128] r38976 c38976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26621
  · exact u26622
  · exact u26623
  · exact u26624

def b38977 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 137 81 162 226 162 418), lower := (rows 37 266 84 137 81 32 64 128 256), losses := [] }

theorem u38977 : Upper (D 7) (R 7) [36,264,80,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38978 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 137 82 163 227 163 419), lower := (rows 37 266 84 137 82 32 64 128 256), losses := [] }

theorem u38978 : Upper (D 7) (R 7) [36,264,80,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38979 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 84 137 112 163 195 131 387), lower := (rows 37 266 84 137 112 32 64 128 256), losses := [] }

theorem u38979 : Upper (D 7) (R 7) [36,264,80,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38980 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 266 84 137 145 98 98 226 354), lower := (rows 37 266 84 137 145 32 64 128 256), losses := [] }

theorem u38980 : Upper (D 7) (R 7) [36,264,80,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38981 : Route 9 := (fun mask => (mask,id))

def c38981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38981 : Upper (D 7) (R 7) [36,264,80,129,130] 13 := by
  apply FastRouting.sound _ _ [36,264,80,129,130] 13 (by decide) (choices 1) [1,2,64] r38981 c38981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26625
  · exact u26626
  · exact u26627

def r38982 : Route 9 := (fun mask => (mask,id))

def c38982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38982 : Upper (D 7) (R 7) [36,264,80,129,160] 13 := by
  apply FastRouting.sound _ _ [36,264,80,129,160] 13 (by decide) (choices 1) [1,2,64] r38982 c38982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26628
  · exact u26629
  · exact u26630

def b38983 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 137 208 35 99 163 291), lower := (rows 37 266 84 137 208 32 64 128 256), losses := [] }

theorem u38983 : Upper (D 7) (R 7) [36,264,80,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38984 : Route 9 := (fun mask => (mask,id))

def c38984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38984 : Upper (D 7) (R 7) [36,264,80,130,3] 13 := by
  apply FastRouting.sound _ _ [36,264,80,130,3] 13 (by decide) (choices 1) [1,64,128] r38984 c38984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26631
  · exact u26632
  · exact u26633

def b38985 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 84 138 49 227 195 195 451), lower := (rows 37 266 84 138 49 32 64 128 256), losses := [] }

theorem u38985 : Upper (D 7) (R 7) [36,264,80,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38986 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(3,5)], upper := (rows 37 266 84 138 50 225 193 193 449), lower := (rows 37 266 84 138 50 32 64 128 256), losses := [] }

theorem u38986 : Upper (D 7) (R 7) [36,264,80,130,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38987 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 138 81 163 227 163 419), lower := (rows 37 266 84 138 81 32 64 128 256), losses := [] }

theorem u38987 : Upper (D 7) (R 7) [36,264,80,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38988 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 4, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 37 266 84 138 82 161 225 161 417), lower := (rows 37 266 84 138 82 32 64 128 256), losses := [] }

theorem u38988 : Upper (D 7) (R 7) [36,264,80,130,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38989 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 84 138 112 163 195 131 387), lower := (rows 37 266 84 138 112 32 64 128 256), losses := [] }

theorem u38989 : Upper (D 7) (R 7) [36,264,80,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38990 : Route 9 := (fun mask => (mask,id))

def c38990 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38990 : Upper (D 7) (R 7) [36,264,80,130,129] 13 := by
  apply FastRouting.sound _ _ [36,264,80,130,129] 13 (by decide) (choices 1) [1,2,64] r38990 c38990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26634
  · exact u26635
  · exact u26636

def b38991 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 266 84 138 146 97 97 225 353), lower := (rows 37 266 84 138 146 32 64 128 256), losses := [] }

theorem u38991 : Upper (D 7) (R 7) [36,264,80,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38992 : Route 9 := (fun mask => (mask,id))

def c38992 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38992 : Upper (D 7) (R 7) [36,264,80,130,160] 13 := by
  apply FastRouting.sound _ _ [36,264,80,130,160] 13 (by decide) (choices 1) [1,2,64] r38992 c38992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26637
  · exact u26638
  · exact u26639

def b38993 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 138 208 35 99 163 291), lower := (rows 37 266 84 138 208 32 64 128 256), losses := [] }

theorem u38993 : Upper (D 7) (R 7) [36,264,80,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38994 : Route 9 := (fun mask => (mask,id))

def c38994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38994 : Upper (D 7) (R 7) [36,264,80,160,3] 13 := by
  apply FastRouting.sound _ _ [36,264,80,160,3] 13 (by decide) (choices 1) [1,2,64,128] r38994 c38994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26640
  · exact u26641
  · exact u26642
  · exact u26643

def b38995 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 168 81 163 195 131 387), lower := (rows 37 266 84 168 81 32 64 128 256), losses := [] }

theorem u38995 : Upper (D 7) (R 7) [36,264,80,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38996 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 168 82 163 195 131 387), lower := (rows 37 266 84 168 82 32 64 128 256), losses := [] }

theorem u38996 : Upper (D 7) (R 7) [36,264,80,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38997 : Route 9 := (fun mask => (mask,id))

def c38997 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38997 : Upper (D 7) (R 7) [36,264,80,160,129] 13 := by
  apply FastRouting.sound _ _ [36,264,80,160,129] 13 (by decide) (choices 1) [1,2,64] r38997 c38997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26644
  · exact u26645
  · exact u26646

def r38998 : Route 9 := (fun mask => (mask,id))

def c38998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38998 : Upper (D 7) (R 7) [36,264,80,160,130] 13 := by
  apply FastRouting.sound _ _ [36,264,80,160,130] 13 (by decide) (choices 1) [1,2,64] r38998 c38998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26647
  · exact u26648
  · exact u26649

def b38999 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 168 208 35 67 131 259), lower := (rows 37 266 84 168 208 32 64 128 256), losses := [] }

theorem u38999 : Upper (D 7) (R 7) [36,264,80,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u38999
end Delivery.IrregularNine14.P07
