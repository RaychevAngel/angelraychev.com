import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0164

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27000 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 76 11 82 33 208 144 400), lower := (rows 37 290 76 11 82 33 64 128 256), losses := [] }

theorem u27000 : Upper (D 7) (R 7) [36,288,72,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27001 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 76 11 82 48 193 129 385), lower := (rows 37 290 76 11 82 48 64 128 256), losses := [] }

theorem u27001 : Upper (D 7) (R 7) [36,288,72,3,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27001 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27002 : Route 9 := (fun mask => (mask,id))

def c27002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27002 : Upper (D 7) (R 7) [36,288,72,3,66,128] 13 := by
  apply FastRouting.sound _ _ [36,288,72,3,66,128] 13 (by decide) (choices 1) [1,16,128] r27002 c27002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9862
  · exact u9863
  · exact u9864

def b27003 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 290 76 11 145 34 208 208 464), lower := (rows 37 290 76 11 145 34 64 128 256), losses := [] }

theorem u27003 : Upper (D 7) (R 7) [36,288,72,3,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27004 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 0, region := 450, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 37 290 76 11 145 48 194 194 450), lower := (rows 37 290 76 11 145 48 64 128 256), losses := [] }

theorem u27004 : Upper (D 7) (R 7) [36,288,72,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27004 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27005 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 76 11 145 96 210 146 402), lower := (rows 37 290 76 11 145 96 64 128 256), losses := [] }

theorem u27005 : Upper (D 7) (R 7) [36,288,72,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27006 : Route 9 := (fun mask => (mask,id))

def c27006 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27006 : Upper (D 7) (R 7) [36,288,72,3,129,128] 13 := by
  apply FastRouting.sound _ _ [36,288,72,3,129,128] 13 (by decide) (choices 1) [2,16] r27006 c27006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9865
  · exact u9866

def b27007 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 76 11 146 33 208 208 464), lower := (rows 37 290 76 11 146 33 64 128 256), losses := [] }

theorem u27007 : Upper (D 7) (R 7) [36,288,72,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27008 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 196, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 37 290 76 11 146 48 193 193 449), lower := (rows 37 290 76 11 146 48 64 128 256), losses := [] }

theorem u27008 : Upper (D 7) (R 7) [36,288,72,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27008 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27009 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 76 11 146 96 209 145 401), lower := (rows 37 290 76 11 146 96 64 128 256), losses := [] }

theorem u27009 : Upper (D 7) (R 7) [36,288,72,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27010 : Route 9 := (fun mask => (mask,id))

def c27010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27010 : Upper (D 7) (R 7) [36,288,72,3,130,128] 13 := by
  apply FastRouting.sound _ _ [36,288,72,3,130,128] 13 (by decide) (choices 1) [1,16] r27010 c27010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9867
  · exact u9868

def b27011 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 76 11 208 33 210 146 402), lower := (rows 37 290 76 11 208 33 64 128 256), losses := [] }

theorem u27011 : Upper (D 7) (R 7) [36,288,72,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27012 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 290 76 11 208 34 209 145 401), lower := (rows 37 290 76 11 208 34 64 128 256), losses := [] }

theorem u27012 : Upper (D 7) (R 7) [36,288,72,3,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27013 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 3, region := 196, targets := 32 }], pairs := [(1,6),(2,5),(3,6)], upper := (rows 37 290 76 11 208 48 195 131 387), lower := (rows 37 290 76 11 208 48 64 128 256), losses := [] }

theorem u27013 : Upper (D 7) (R 7) [36,288,72,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27013 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27014 : Route 9 := (fun mask => (mask,id))

def c27014 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27014 : Upper (D 7) (R 7) [36,288,72,3,192,128] 13 := by
  apply FastRouting.sound _ _ [36,288,72,3,192,128] 13 (by decide) (choices 1) [1,2,16] r27014 c27014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9869
  · exact u9870
  · exact u9871

def b27015 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 76 25 82 33 194 130 386), lower := (rows 37 290 76 25 82 33 64 128 256), losses := [] }

theorem u27015 : Upper (D 7) (R 7) [36,288,72,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27016 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 8, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 290 76 25 82 34 193 129 385), lower := (rows 37 290 76 25 82 34 64 128 256), losses := [] }

theorem u27016 : Upper (D 7) (R 7) [36,288,72,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27017 : Route 9 := (fun mask => (mask,id))

def c27017 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27017 : Upper (D 7) (R 7) [36,288,72,17,66,128] 13 := by
  apply FastRouting.sound _ _ [36,288,72,17,66,128] 13 (by decide) (choices 1) [1,2,128] r27017 c27017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9872
  · exact u9873
  · exact u9874

def b27018 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 290 76 25 146 33 194 194 450), lower := (rows 37 290 76 25 146 33 64 128 256), losses := [] }

theorem u27018 : Upper (D 7) (R 7) [36,288,72,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27019 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 290 76 25 146 34 193 193 449), lower := (rows 37 290 76 25 146 34 64 128 256), losses := [] }

theorem u27019 : Upper (D 7) (R 7) [36,288,72,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27020 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 76 25 146 96 195 131 387), lower := (rows 37 290 76 25 146 96 64 128 256), losses := [] }

theorem u27020 : Upper (D 7) (R 7) [36,288,72,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27021 : Route 9 := (fun mask => (mask,id))

def c27021 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27021 : Upper (D 7) (R 7) [36,288,72,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,288,72,17,130,128] 13 (by decide) (choices 1) [1,2] r27021 c27021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9875
  · exact u9876

def b27022 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 76 25 208 33 194 130 386), lower := (rows 37 290 76 25 208 33 64 128 256), losses := [] }

theorem u27022 : Upper (D 7) (R 7) [36,288,72,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27023 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 37 290 76 25 208 34 195 131 387), lower := (rows 37 290 76 25 208 34 64 128 256), losses := [] }

theorem u27023 : Upper (D 7) (R 7) [36,288,72,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27024 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,1),(0,6),(2,1),(3,1)], upper := (rows 37 290 76 25 208 160 67 131 259), lower := (rows 37 290 76 25 208 160 64 128 256), losses := [] }

theorem u27024 : Upper (D 7) (R 7) [36,288,72,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27025 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 290 76 26 81 33 194 130 386), lower := (rows 37 290 76 26 81 33 64 128 256), losses := [] }

theorem u27025 : Upper (D 7) (R 7) [36,288,72,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27026 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 37 290 76 26 81 34 193 129 385), lower := (rows 37 290 76 26 81 34 64 128 256), losses := [] }

theorem u27026 : Upper (D 7) (R 7) [36,288,72,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27027 : Route 9 := (fun mask => (mask,id))

def c27027 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27027 : Upper (D 7) (R 7) [36,288,72,18,65,128] 13 := by
  apply FastRouting.sound _ _ [36,288,72,18,65,128] 13 (by decide) (choices 1) [1,2,128] r27027 c27027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9877
  · exact u9878
  · exact u9879

def b27028 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 196, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 290 76 26 145 33 194 194 450), lower := (rows 37 290 76 26 145 33 64 128 256), losses := [] }

theorem u27028 : Upper (D 7) (R 7) [36,288,72,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27029 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 37 290 76 26 145 34 193 193 449), lower := (rows 37 290 76 26 145 34 64 128 256), losses := [] }

theorem u27029 : Upper (D 7) (R 7) [36,288,72,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27030 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 76 26 145 96 195 131 387), lower := (rows 37 290 76 26 145 96 64 128 256), losses := [] }

theorem u27030 : Upper (D 7) (R 7) [36,288,72,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27031 : Route 9 := (fun mask => (mask,id))

def c27031 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27031 : Upper (D 7) (R 7) [36,288,72,18,129,128] 13 := by
  apply FastRouting.sound _ _ [36,288,72,18,129,128] 13 (by decide) (choices 1) [1,2] r27031 c27031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9880
  · exact u9881

def b27032 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 290 76 26 208 33 195 131 387), lower := (rows 37 290 76 26 208 33 64 128 256), losses := [] }

theorem u27032 : Upper (D 7) (R 7) [36,288,72,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27033 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 37 290 76 26 208 34 193 129 385), lower := (rows 37 290 76 26 208 34 64 128 256), losses := [] }

theorem u27033 : Upper (D 7) (R 7) [36,288,72,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27034 : Route 9 := (fun mask => (mask,id))

def c27034 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27034 : Upper (D 7) (R 7) [36,288,72,18,192,128] 13 := by
  apply FastRouting.sound _ _ [36,288,72,18,192,128] 13 (by decide) (choices 1) [1,2] r27034 c27034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9882
  · exact u9883

def b27035 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 204, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 290 76 137 19 34 208 208 464), lower := (rows 37 290 76 137 19 34 64 128 256), losses := [] }

theorem u27035 : Upper (D 7) (R 7) [36,288,72,129,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27036 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 204, targets := 32 },{ cop := 0, region := 450, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 37 290 76 137 19 48 194 194 450), lower := (rows 37 290 76 137 19 48 64 128 256), losses := [] }

theorem u27036 : Upper (D 7) (R 7) [36,288,72,129,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27036 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27037 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 76 137 19 96 210 146 402), lower := (rows 37 290 76 137 19 96 64 128 256), losses := [] }

theorem u27037 : Upper (D 7) (R 7) [36,288,72,129,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27038 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 204, targets := 32 }], pairs := [(1,7),(2,5),(3,5),(4,7)], upper := (rows 37 290 76 137 19 160 82 210 338), lower := (rows 37 290 76 137 19 160 64 128 256), losses := [] }

theorem u27038 : Upper (D 7) (R 7) [36,288,72,129,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27039 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 37 290 76 137 81 34 210 146 402), lower := (rows 37 290 76 137 81 34 64 128 256), losses := [] }

theorem u27039 : Upper (D 7) (R 7) [36,288,72,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27040 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 290 76 137 81 48 194 130 386), lower := (rows 37 290 76 137 81 48 64 128 256), losses := [] }

theorem u27040 : Upper (D 7) (R 7) [36,288,72,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27040 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27041 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(1,7),(3,6),(4,7)], upper := (rows 37 290 76 137 81 160 82 146 274), lower := (rows 37 290 76 137 81 160 64 128 256), losses := [] }

theorem u27041 : Upper (D 7) (R 7) [36,288,72,129,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27042 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 290 76 137 82 33 210 146 402), lower := (rows 37 290 76 137 82 33 64 128 256), losses := [] }

theorem u27042 : Upper (D 7) (R 7) [36,288,72,129,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27043 : Route 9 := (fun mask => (mask,id))

def c27043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27043 : Upper (D 7) (R 7) [36,288,72,129,66,2] 13 := by
  apply FastRouting.sound _ _ [36,288,72,129,66,2] 13 (by decide) (choices 1) [1,16,128] r27043 c27043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9884
  · exact u9885
  · exact u9886

def r27044 : Route 9 := (fun mask => (mask,id))

def c27044 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27044 : Upper (D 7) (R 7) [36,288,72,129,66,16] 13 := by
  apply FastRouting.sound _ _ [36,288,72,129,66,16] 13 (by decide) (choices 1) [1,2,128] r27044 c27044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9887
  · exact u9888
  · exact u9889

def b27045 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 290 76 137 82 160 83 147 275), lower := (rows 37 290 76 137 82 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 288 109 169 80 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 290 45 169 18 160 0 160 256) }] }

theorem u27045 : Upper (D 7) (R 7) [36,288,72,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27046 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 290 76 137 146 33 82 210 338), lower := (rows 37 290 76 137 146 33 64 128 256), losses := [] }

theorem u27046 : Upper (D 7) (R 7) [36,288,72,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27047 : Route 9 := (fun mask => (mask,id))

def c27047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27047 : Upper (D 7) (R 7) [36,288,72,129,130,2] 13 := by
  apply FastRouting.sound _ _ [36,288,72,129,130,2] 13 (by decide) (choices 1) [1,16] r27047 c27047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9890
  · exact u9891

def r27048 : Route 9 := (fun mask => (mask,id))

def c27048 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27048 : Upper (D 7) (R 7) [36,288,72,129,130,16] 13 := by
  apply FastRouting.sound _ _ [36,288,72,129,130,16] 13 (by decide) (choices 1) [1,2] r27048 c27048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9892
  · exact u9893

def b27049 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 76 137 146 96 83 147 275), lower := (rows 37 290 76 137 146 96 64 128 256), losses := [] }

theorem u27049 : Upper (D 7) (R 7) [36,288,72,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27050 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 290 76 137 208 33 82 146 274), lower := (rows 37 290 76 137 208 33 64 128 256), losses := [] }

theorem u27050 : Upper (D 7) (R 7) [36,288,72,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27051 : Route 9 := (fun mask => (mask,id))

def c27051 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27051 : Upper (D 7) (R 7) [36,288,72,129,192,2] 13 := by
  apply FastRouting.sound _ _ [36,288,72,129,192,2] 13 (by decide) (choices 1) [1,2,16] r27051 c27051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9894
  · exact u9895
  · exact u9896

def b27052 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 290 76 137 208 48 67 131 259), lower := (rows 37 290 76 137 208 48 64 128 256), losses := [] }

theorem u27052 : Upper (D 7) (R 7) [36,288,72,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27052 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27053 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 204, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 290 76 138 19 33 208 208 464), lower := (rows 37 290 76 138 19 33 64 128 256), losses := [] }

theorem u27053 : Upper (D 7) (R 7) [36,288,72,130,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27054 : Route 9 := (fun mask => (mask,id))

def c27054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27054 : Upper (D 7) (R 7) [36,288,72,130,3,16] 13 := by
  apply FastRouting.sound _ _ [36,288,72,130,3,16] 13 (by decide) (choices 1) [1,128] r27054 c27054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9897
  · exact u9898

def b27055 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 76 138 19 96 209 145 401), lower := (rows 37 290 76 138 19 96 64 128 256), losses := [] }

theorem u27055 : Upper (D 7) (R 7) [36,288,72,130,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27056 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 204, targets := 32 }], pairs := [(1,7),(2,5),(3,5),(4,7)], upper := (rows 37 290 76 138 19 160 81 209 337), lower := (rows 37 290 76 138 19 160 64 128 256), losses := [] }

theorem u27056 : Upper (D 7) (R 7) [36,288,72,130,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27057 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 290 76 138 81 33 210 146 402), lower := (rows 37 290 76 138 81 33 64 128 256), losses := [] }

theorem u27057 : Upper (D 7) (R 7) [36,288,72,130,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27058 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 37 290 76 138 81 34 209 145 401), lower := (rows 37 290 76 138 81 34 64 128 256), losses := [] }

theorem u27058 : Upper (D 7) (R 7) [36,288,72,130,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27059 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 290 76 138 81 48 195 131 387), lower := (rows 37 290 76 138 81 48 64 128 256), losses := [] }

theorem u27059 : Upper (D 7) (R 7) [36,288,72,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27059 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27059
end Delivery.IrregularNine14.P07
