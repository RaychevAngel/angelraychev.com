import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0163
import IrregularNine14P07C0164

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26940 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 70 25 88 34 193 129 385), lower := (rows 37 290 70 25 88 34 64 128 256), losses := [] }

theorem u26940 : Upper (D 7) (R 7) [36,288,66,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26941 : Route 9 := (fun mask => (mask,id))

def c26941 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26941 : Upper (D 7) (R 7) [36,288,66,17,72,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,72,128] 13 (by decide) (choices 1) [1,2,128] r26941 c26941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9787
  · exact u9788
  · exact u9789

def r26942 : Route 9 := (fun mask => (mask,id))

def c26942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26942 : Upper (D 7) (R 7) [36,288,66,17,130,1] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,130,1] 13 (by decide) (choices 1) [8,128] r26942 c26942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9790
  · exact u9791

def r26943 : Route 9 := (fun mask => (mask,id))

def c26943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26943 : Upper (D 7) (R 7) [36,288,66,17,130,8] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,130,8] 13 (by decide) (choices 1) [1,128] r26943 c26943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9792
  · exact u9793

def b26944 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 70 25 146 96 201 137 393), lower := (rows 37 290 70 25 146 96 64 128 256), losses := [] }

theorem u26944 : Upper (D 7) (R 7) [36,288,66,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26945 : Route 9 := (fun mask => (mask,id))

def c26945 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26945 : Upper (D 7) (R 7) [36,288,66,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,130,128] 13 (by decide) (choices 1) [1,8] r26945 c26945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9794
  · exact u9795

def b26946 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 290 70 25 152 33 194 194 450), lower := (rows 37 290 70 25 152 33 64 128 256), losses := [] }

theorem u26946 : Upper (D 7) (R 7) [36,288,66,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26947 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 70 25 152 34 193 193 449), lower := (rows 37 290 70 25 152 34 64 128 256), losses := [] }

theorem u26947 : Upper (D 7) (R 7) [36,288,66,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26948 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 70 25 152 96 195 131 387), lower := (rows 37 290 70 25 152 96 64 128 256), losses := [] }

theorem u26948 : Upper (D 7) (R 7) [36,288,66,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26949 : Route 9 := (fun mask => (mask,id))

def c26949 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26949 : Upper (D 7) (R 7) [36,288,66,17,136,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,136,128] 13 (by decide) (choices 1) [1,2] r26949 c26949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9796
  · exact u9797

def b26950 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 290 70 25 208 33 202 138 394), lower := (rows 37 290 70 25 208 33 64 128 256), losses := [] }

theorem u26950 : Upper (D 7) (R 7) [36,288,66,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26951 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 70 25 208 34 201 137 393), lower := (rows 37 290 70 25 208 34 64 128 256), losses := [] }

theorem u26951 : Upper (D 7) (R 7) [36,288,66,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26952 : Route 9 := (fun mask => (mask,id))

def c26952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26952 : Upper (D 7) (R 7) [36,288,66,17,192,8] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,192,8] 13 (by decide) (choices 1) [1,2,128] r26952 c26952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9798
  · exact u9799
  · exact u9800

def r26953 : Route 9 := (fun mask => (mask,id))

def c26953 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26953 : Upper (D 7) (R 7) [36,288,66,17,192,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,192,128] 13 (by decide) (choices 1) [1,2,8] r26953 c26953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9801
  · exact u9802
  · exact u9803

def b26954 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 57, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,7)], upper := (rows 37 290 70 26 81 33 200 136 392), lower := (rows 37 290 70 26 81 33 64 128 256), losses := [] }

theorem u26954 : Upper (D 7) (R 7) [36,288,66,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26955 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 37 290 70 26 81 40 193 129 385), lower := (rows 37 290 70 26 81 40 64 128 256), losses := [] }

theorem u26955 : Upper (D 7) (R 7) [36,288,66,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26955 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26956 : Route 9 := (fun mask => (mask,id))

def c26956 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26956 : Upper (D 7) (R 7) [36,288,66,18,65,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,18,65,128] 13 (by decide) (choices 1) [1,8,128] r26956 c26956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9804
  · exact u9805
  · exact u9806

def b26957 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 196, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 290 70 26 145 33 200 200 456), lower := (rows 37 290 70 26 145 33 64 128 256), losses := [] }

theorem u26957 : Upper (D 7) (R 7) [36,288,66,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26958 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 37 290 70 26 145 40 193 193 449), lower := (rows 37 290 70 26 145 40 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 17 0 81 145 273), good := (rows 469 258 70 478 465 12 64 128 256) }] }

theorem u26958 : Upper (D 7) (R 7) [36,288,66,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26958 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26959 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 70 26 145 96 201 137 393), lower := (rows 37 290 70 26 145 96 64 128 256), losses := [] }

theorem u26959 : Upper (D 7) (R 7) [36,288,66,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26960 : Route 9 := (fun mask => (mask,id))

def c26960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26960 : Upper (D 7) (R 7) [36,288,66,18,129,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,18,129,128] 13 (by decide) (choices 1) [1,8] r26960 c26960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9807
  · exact u9808

def b26961 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 290 70 26 152 33 193 193 449), lower := (rows 37 290 70 26 152 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 14 19 0 97 161 289), good := (rows 477 478 94 30 152 465 64 128 256) }] }

theorem u26961 : Upper (D 7) (R 7) [36,288,66,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26962 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 70 26 152 96 193 129 385), lower := (rows 37 290 70 26 152 96 64 128 256), losses := [] }

theorem u26962 : Upper (D 7) (R 7) [36,288,66,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26963 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 290 70 26 152 160 65 193 321), lower := (rows 37 290 70 26 152 160 64 128 256), losses := [] }

theorem u26963 : Upper (D 7) (R 7) [36,288,66,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26964 : Route 9 := (fun mask => (mask,id))

def c26964 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26964 : Upper (D 7) (R 7) [36,288,66,18,192,1] 13 := by
  apply FastRouting.sound _ _ [36,288,66,18,192,1] 13 (by decide) (choices 1) [1,8,128] r26964 c26964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9809
  · exact u9810
  · exact u9811

def b26965 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6),(4,1),(4,5)], upper := (rows 37 290 70 26 208 40 193 129 385), lower := (rows 37 290 70 26 208 40 64 128 256), losses := [] }

theorem u26965 : Upper (D 7) (R 7) [36,288,66,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26965 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26966 : Route 9 := (fun mask => (mask,id))

def c26966 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26966 : Upper (D 7) (R 7) [36,288,66,18,192,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,18,192,128] 13 (by decide) (choices 1) [1,8] r26966 c26966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9812
  · exact u9813

def b26967 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 70 73 145 34 216 152 408), lower := (rows 37 290 70 73 145 34 64 128 256), losses := [] }

theorem u26967 : Upper (D 7) (R 7) [36,288,66,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26968 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 290 70 73 145 40 210 146 402), lower := (rows 37 290 70 73 145 40 64 128 256), losses := [] }

theorem u26968 : Upper (D 7) (R 7) [36,288,66,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26968 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26969 : Route 9 := (fun mask => (mask,id))

def c26969 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26969 : Upper (D 7) (R 7) [36,288,66,65,129,16] 13 := by
  apply FastRouting.sound _ _ [36,288,66,65,129,16] 13 (by decide) (choices 1) [2,8,128] r26969 c26969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9814
  · exact u9815
  · exact u9816

def r26970 : Route 9 := (fun mask => (mask,id))

def c26970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26970 : Upper (D 7) (R 7) [36,288,66,65,129,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,65,129,128] 13 (by decide) (choices 1) [2,8,16] r26970 c26970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9817
  · exact u9818
  · exact u9819

def b26971 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 290 70 73 146 33 216 152 408), lower := (rows 37 290 70 73 146 33 64 128 256), losses := [] }

theorem u26971 : Upper (D 7) (R 7) [36,288,66,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26972 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 290 70 73 146 40 209 145 401), lower := (rows 37 290 70 73 146 40 64 128 256), losses := [] }

theorem u26972 : Upper (D 7) (R 7) [36,288,66,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26972 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26973 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(3,1),(3,5)], upper := (rows 37 290 70 73 146 48 201 137 393), lower := (rows 37 290 70 73 146 48 64 128 256), losses := [] }

theorem u26973 : Upper (D 7) (R 7) [36,288,66,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26973 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26974 : Route 9 := (fun mask => (mask,id))

def c26974 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26974 : Upper (D 7) (R 7) [36,288,66,65,130,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,65,130,128] 13 (by decide) (choices 1) [1,8,16] r26974 c26974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9820
  · exact u9821
  · exact u9822

def b26975 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 290 70 73 152 33 210 146 402), lower := (rows 37 290 70 73 152 33 64 128 256), losses := [] }

theorem u26975 : Upper (D 7) (R 7) [36,288,66,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26976 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 70 73 152 34 209 145 401), lower := (rows 37 290 70 73 152 34 64 128 256), losses := [] }

theorem u26976 : Upper (D 7) (R 7) [36,288,66,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26977 : Route 9 := (fun mask => (mask,id))

def c26977 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26977 : Upper (D 7) (R 7) [36,288,66,65,136,16] 13 := by
  apply FastRouting.sound _ _ [36,288,66,65,136,16] 13 (by decide) (choices 1) [1,2,128] r26977 c26977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9823
  · exact u9824
  · exact u9825

def r26978 : Route 9 := (fun mask => (mask,id))

def c26978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26978 : Upper (D 7) (R 7) [36,288,66,65,136,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,65,136,128] 13 (by decide) (choices 1) [1,2,16] r26978 c26978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9826
  · exact u9827
  · exact u9828

def b26979 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 290 70 88 145 33 202 138 394), lower := (rows 37 290 70 88 145 33 64 128 256), losses := [{ target := 6, region := (rows 5 10 4 8 16 53 0 136 264), good := (rows 37 290 39 442 177 33 0 128 256) }] }

theorem u26979 : Upper (D 7) (R 7) [36,288,66,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26980 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 70 88 145 34 201 137 393), lower := (rows 37 290 70 88 145 34 64 128 256), losses := [] }

theorem u26980 : Upper (D 7) (R 7) [36,288,66,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26981 : Route 9 := (fun mask => (mask,id))

def c26981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26981 : Upper (D 7) (R 7) [36,288,66,80,129,8] 13 := by
  apply FastRouting.sound _ _ [36,288,66,80,129,8] 13 (by decide) (choices 1) [1,2,128] r26981 c26981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9829
  · exact u9830
  · exact u9831

def r26982 : Route 9 := (fun mask => (mask,id))

def c26982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26982 : Upper (D 7) (R 7) [36,288,66,80,129,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,80,129,128] 13 (by decide) (choices 1) [1,2,8] r26982 c26982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9832
  · exact u9833
  · exact u9834

def r26983 : Route 9 := (fun mask => (mask,id))

def c26983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26983 : Upper (D 7) (R 7) [36,288,66,80,130,1] 13 := by
  apply FastRouting.sound _ _ [36,288,66,80,130,1] 13 (by decide) (choices 1) [1,8,128] r26983 c26983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9835
  · exact u9836
  · exact u9837

def r26984 : Route 9 := (fun mask => (mask,id))

def c26984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26984 : Upper (D 7) (R 7) [36,288,66,80,130,8] 13 := by
  apply FastRouting.sound _ _ [36,288,66,80,130,8] 13 (by decide) (choices 1) [1,128] r26984 c26984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9838
  · exact u9839

def r26985 : Route 9 := (fun mask => (mask,id))

def c26985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26985 : Upper (D 7) (R 7) [36,288,66,80,130,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,80,130,128] 13 (by decide) (choices 1) [1,8] r26985 c26985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9840
  · exact u9841

def b26986 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 290 70 88 152 33 195 131 387), lower := (rows 37 290 70 88 152 33 64 128 256), losses := [] }

theorem u26986 : Upper (D 7) (R 7) [36,288,66,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26987 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 70 88 152 34 193 129 385), lower := (rows 37 290 70 88 152 34 64 128 256), losses := [] }

theorem u26987 : Upper (D 7) (R 7) [36,288,66,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26988 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 290 70 88 152 160 67 131 259), lower := (rows 37 290 70 88 152 160 64 128 256), losses := [] }

theorem u26988 : Upper (D 7) (R 7) [36,288,66,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26989 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 290 70 137 146 33 88 216 344), lower := (rows 37 290 70 137 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 22 41 22 0 67 131 259), good := (rows 477 478 470 457 470 457 64 128 256) }] }

theorem u26989 : Upper (D 7) (R 7) [36,288,66,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26990 : Route 9 := (fun mask => (mask,id))

def c26990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26990 : Upper (D 7) (R 7) [36,288,66,129,130,8] 13 := by
  apply FastRouting.sound _ _ [36,288,66,129,130,8] 13 (by decide) (choices 1) [1,16] r26990 c26990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9842
  · exact u9843

def r26991 : Route 9 := (fun mask => (mask,id))

def c26991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26991 : Upper (D 7) (R 7) [36,288,66,129,130,16] 13 := by
  apply FastRouting.sound _ _ [36,288,66,129,130,16] 13 (by decide) (choices 1) [1,8] r26991 c26991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9844
  · exact u9845

def b26992 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 70 137 146 96 89 153 281), lower := (rows 37 290 70 137 146 96 64 128 256), losses := [] }

theorem u26992 : Upper (D 7) (R 7) [36,288,66,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26993 : Route 9 := (fun mask => (mask,id))

def c26993 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26993 : Upper (D 7) (R 7) [36,288,66,129,192,1] 13 := by
  apply FastRouting.sound _ _ [36,288,66,129,192,1] 13 (by decide) (choices 1) [2,8,16] r26993 c26993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9846
  · exact u9847
  · exact u9848

def b26994 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 70 137 208 34 89 153 281), lower := (rows 37 290 70 137 208 34 64 128 256), losses := [] }

theorem u26994 : Upper (D 7) (R 7) [36,288,66,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26995 : Route 9 := (fun mask => (mask,id))

def c26995 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26995 : Upper (D 7) (R 7) [36,288,66,129,192,8] 13 := by
  apply FastRouting.sound _ _ [36,288,66,129,192,8] 13 (by decide) (choices 1) [1,2,16] r26995 c26995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9849
  · exact u9850
  · exact u9851

def r26996 : Route 9 := (fun mask => (mask,id))

def c26996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26996 : Upper (D 7) (R 7) [36,288,66,129,192,16] 13 := by
  apply FastRouting.sound _ _ [36,288,66,129,192,16] 13 (by decide) (choices 1) [1,2,8] r26996 c26996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9852
  · exact u9853
  · exact u9854

def r26997 : Route 9 := (fun mask => (mask,id))

def c26997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26997 : Upper (D 7) (R 7) [36,288,66,130,192,1] 13 := by
  apply FastRouting.sound _ _ [36,288,66,130,192,1] 13 (by decide) (choices 1) [1,8,16] r26997 c26997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9855
  · exact u9856
  · exact u9857

def r26998 : Route 9 := (fun mask => (mask,id))

def c26998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26998 : Upper (D 7) (R 7) [36,288,66,130,192,8] 13 := by
  apply FastRouting.sound _ _ [36,288,66,130,192,8] 13 (by decide) (choices 1) [1,16] r26998 c26998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9858
  · exact u9859

def r26999 : Route 9 := (fun mask => (mask,id))

def c26999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26999 : Upper (D 7) (R 7) [36,288,66,130,192,16] 13 := by
  apply FastRouting.sound _ _ [36,288,66,130,192,16] 13 (by decide) (choices 1) [1,8] r26999 c26999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9860
  · exact u9861

#print axioms u26999
end Delivery.IrregularNine14.P07
