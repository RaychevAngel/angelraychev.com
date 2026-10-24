import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0100
import IrregularNine14P07C0101

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20940 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 259 44 200 82 48 197 133 389), lower := (rows 35 259 44 200 82 48 64 128 256), losses := [] }

theorem u20940 : Upper (D 7) (R 7) [34,257,40,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20940 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20941 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 259 44 200 82 160 85 149 277), lower := (rows 35 259 44 200 82 160 64 128 256), losses := [] }

theorem u20941 : Upper (D 7) (R 7) [34,257,40,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20942 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 200 84 33 210 146 402), lower := (rows 35 259 44 200 84 33 64 128 256), losses := [] }

theorem u20942 : Upper (D 7) (R 7) [34,257,40,192,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20943 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 200 84 34 209 145 401), lower := (rows 35 259 44 200 84 34 64 128 256), losses := [] }

theorem u20943 : Upper (D 7) (R 7) [34,257,40,192,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20944 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 52, targets := 131 }], pairs := [(2,0),(2,1),(2,7)], upper := (rows 35 259 44 200 84 48 195 131 387), lower := (rows 35 259 44 200 84 48 64 128 256), losses := [] }

theorem u20944 : Upper (D 7) (R 7) [34,257,40,192,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20944 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20945 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 44 200 84 160 83 147 275), lower := (rows 35 259 44 200 84 160 64 128 256), losses := [] }

theorem u20945 : Upper (D 7) (R 7) [34,257,40,192,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20946 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(4,1)], upper := (rows 35 259 69 74 148 40 240 176 432), lower := (rows 35 259 69 74 148 40 64 128 256), losses := [] }

theorem u20946 : Upper (D 7) (R 7) [34,257,65,66,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20946 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20947 : Route 9 := (fun mask => (mask,id))

def c20947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20947 : Upper (D 7) (R 7) [34,257,65,66,132,16] 13 := by
  apply FastRouting.sound _ _ [34,257,65,66,132,16] 13 (by decide) (choices 1) [8,32,128] r20947 c20947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6006
  · exact u6007
  · exact u6008

def r20948 : Route 9 := (fun mask => (mask,id))

def c20948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20948 : Upper (D 7) (R 7) [34,257,65,66,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,66,132,128] 13 (by decide) (choices 1) [8,16,32] r20948 c20948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6009
  · exact u6010
  · exact u6011

def b20949 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(3,0),(4,0)], upper := (rows 35 259 69 74 152 36 240 176 432), lower := (rows 35 259 69 74 152 36 64 128 256), losses := [] }

theorem u20949 : Upper (D 7) (R 7) [34,257,65,66,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20949 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20950 : Route 9 := (fun mask => (mask,id))

def c20950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20950 : Upper (D 7) (R 7) [34,257,65,66,136,16] 13 := by
  apply FastRouting.sound _ _ [34,257,65,66,136,16] 13 (by decide) (choices 1) [4,32,128] r20950 c20950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6012
  · exact u6013
  · exact u6014

def r20951 : Route 9 := (fun mask => (mask,id))

def c20951 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20951 : Upper (D 7) (R 7) [34,257,65,66,136,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,66,136,128] 13 (by decide) (choices 1) [4,16,32] r20951 c20951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6015
  · exact u6016
  · exact u6017

def b20952 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(3,0),(4,0)], upper := (rows 35 259 69 74 176 36 216 152 408), lower := (rows 35 259 69 74 176 36 64 128 256), losses := [] }

theorem u20952 : Upper (D 7) (R 7) [34,257,65,66,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20952 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20953 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(4,1)], upper := (rows 35 259 69 74 176 40 212 148 404), lower := (rows 35 259 69 74 176 40 64 128 256), losses := [] }

theorem u20953 : Upper (D 7) (R 7) [34,257,65,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20953 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20954 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 69 74 176 48 204 140 396), lower := (rows 35 259 69 74 176 48 64 128 256), losses := [] }

theorem u20954 : Upper (D 7) (R 7) [34,257,65,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20954 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20955 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 69 74 176 160 92 156 284), lower := (rows 35 259 69 74 176 160 64 128 256), losses := [] }

theorem u20955 : Upper (D 7) (R 7) [34,257,65,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20956 : Route 9 := (fun mask => (mask,id))

def c20956 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20956 : Upper (D 7) (R 7) [34,257,65,80,130,4] 13 := by
  apply FastRouting.sound _ _ [34,257,65,80,130,4] 13 (by decide) (choices 1) [8,32,128] r20956 c20956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6018
  · exact u6019
  · exact u6020

def r20957 : Route 9 := (fun mask => (mask,id))

def c20957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20957 : Upper (D 7) (R 7) [34,257,65,80,130,8] 13 := by
  apply FastRouting.sound _ _ [34,257,65,80,130,8] 13 (by decide) (choices 1) [4,32,128] r20957 c20957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6021
  · exact u6022
  · exact u6023

def r20958 : Route 9 := (fun mask => (mask,id))

def c20958 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20958 : Upper (D 7) (R 7) [34,257,65,80,130,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,80,130,128] 13 (by decide) (choices 1) [4,8,32] r20958 c20958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6024
  · exact u6025
  · exact u6026

def b20959 : PairBound 9 := { available := 168, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 69 88 148 34 232 168 424), lower := (rows 35 259 69 88 148 34 64 128 256), losses := [] }

theorem u20959 : Upper (D 7) (R 7) [34,257,65,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20960 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,0)], upper := (rows 35 259 69 88 148 40 226 162 418), lower := (rows 35 259 69 88 148 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 60 65 129 257), good := (rows 482 450 508 120 188 40 64 128 256) }] }

theorem u20960 : Upper (D 7) (R 7) [34,257,65,80,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20960 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20961 : Route 9 := (fun mask => (mask,id))

def c20961 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20961 : Upper (D 7) (R 7) [34,257,65,80,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,80,132,128] 13 (by decide) (choices 1) [2,8,32] r20961 c20961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6027
  · exact u6028
  · exact u6029

def b20962 : PairBound 9 := { available := 164, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 69 88 152 34 228 164 420), lower := (rows 35 259 69 88 152 34 64 128 256), losses := [] }

theorem u20962 : Upper (D 7) (R 7) [34,257,65,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20963 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 259 69 88 152 36 226 162 418), lower := (rows 35 259 69 88 152 36 64 128 256), losses := [] }

theorem u20963 : Upper (D 7) (R 7) [34,257,65,80,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20963 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20964 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 35 259 69 88 152 160 102 166 294), lower := (rows 35 259 69 88 152 160 64 128 256), losses := [] }

theorem u20964 : Upper (D 7) (R 7) [34,257,65,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20965 : PairBound 9 := { available := 140, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 69 88 176 34 204 140 396), lower := (rows 35 259 69 88 176 34 64 128 256), losses := [] }

theorem u20965 : Upper (D 7) (R 7) [34,257,65,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20966 : Route 9 := (fun mask => (mask,id))

def c20966 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20966 : Upper (D 7) (R 7) [34,257,65,80,160,4] 13 := by
  apply FastRouting.sound _ _ [34,257,65,80,160,4] 13 (by decide) (choices 1) [2,8,128] r20966 c20966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6030
  · exact u6031
  · exact u6032

def b20967 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 259 69 88 176 40 198 134 390), lower := (rows 35 259 69 88 176 40 64 128 256), losses := [] }

theorem u20967 : Upper (D 7) (R 7) [34,257,65,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20967 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20968 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 69 88 176 160 78 142 270), lower := (rows 35 259 69 88 176 160 64 128 256), losses := [] }

theorem u20968 : Upper (D 7) (R 7) [34,257,65,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20969 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 40, targets := 131 }], pairs := [(3,0),(3,1),(3,7)], upper := (rows 35 259 69 104 146 36 216 152 408), lower := (rows 35 259 69 104 146 36 64 128 256), losses := [] }

theorem u20969 : Upper (D 7) (R 7) [34,257,65,96,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20969 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20970 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 259 69 104 146 40 212 148 404), lower := (rows 35 259 69 104 146 40 64 128 256), losses := [] }

theorem u20970 : Upper (D 7) (R 7) [34,257,65,96,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20970 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20971 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 259 69 104 146 48 204 140 396), lower := (rows 35 259 69 104 146 48 64 128 256), losses := [] }

theorem u20971 : Upper (D 7) (R 7) [34,257,65,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20971 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20972 : Route 9 := (fun mask => (mask,id))

def c20972 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20972 : Upper (D 7) (R 7) [34,257,65,96,130,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,96,130,128] 13 (by decide) (choices 1) [4,8,16] r20972 c20972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6033
  · exact u6034
  · exact u6035

def b20973 : PairBound 9 := { available := 152, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 69 104 148 34 216 152 408), lower := (rows 35 259 69 104 148 34 64 128 256), losses := [] }

theorem u20973 : Upper (D 7) (R 7) [34,257,65,96,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20974 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 259 69 104 148 40 210 146 402), lower := (rows 35 259 69 104 148 40 64 128 256), losses := [] }

theorem u20974 : Upper (D 7) (R 7) [34,257,65,96,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20974 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20975 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 387, targets := 64 },{ cop := 0, region := 200, targets := 1 }], pairs := [(0,6),(1,6),(3,0)], upper := (rows 35 259 69 104 148 48 202 138 394), lower := (rows 35 259 69 104 148 48 64 128 256), losses := [] }

theorem u20975 : Upper (D 7) (R 7) [34,257,65,96,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20975 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20976 : Route 9 := (fun mask => (mask,id))

def c20976 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20976 : Upper (D 7) (R 7) [34,257,65,96,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,96,132,128] 13 (by decide) (choices 1) [2,8,16] r20976 c20976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6036
  · exact u6037
  · exact u6038

def b20977 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 69 104 152 34 212 148 404), lower := (rows 35 259 69 104 152 34 64 128 256), losses := [] }

theorem u20977 : Upper (D 7) (R 7) [34,257,65,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20978 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 40, targets := 131 }], pairs := [(3,0),(3,1),(3,7)], upper := (rows 35 259 69 104 152 36 210 146 402), lower := (rows 35 259 69 104 152 36 64 128 256), losses := [] }

theorem u20978 : Upper (D 7) (R 7) [34,257,65,96,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20978 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20979 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 259 69 104 152 48 198 134 390), lower := (rows 35 259 69 104 152 48 64 128 256), losses := [] }

theorem u20979 : Upper (D 7) (R 7) [34,257,65,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20979 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20980 : Route 9 := (fun mask => (mask,id))

def c20980 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20980 : Upper (D 7) (R 7) [34,257,65,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,96,136,128] 13 (by decide) (choices 1) [2,4,16] r20980 c20980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6039
  · exact u6040
  · exact u6041

def b20981 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 259 69 138 148 40 112 240 368), lower := (rows 35 259 69 138 148 40 64 128 256), losses := [] }

theorem u20981 : Upper (D 7) (R 7) [34,257,65,130,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20981 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20982 : Route 9 := (fun mask => (mask,id))

def c20982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20982 : Upper (D 7) (R 7) [34,257,65,130,132,16] 13 := by
  apply FastRouting.sound _ _ [34,257,65,130,132,16] 13 (by decide) (choices 1) [8,32] r20982 c20982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6042
  · exact u6043

def r20983 : Route 9 := (fun mask => (mask,id))

def c20983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20983 : Upper (D 7) (R 7) [34,257,65,130,132,64] 13 := by
  apply FastRouting.sound _ _ [34,257,65,130,132,64] 13 (by decide) (choices 1) [8,16,32] r20983 c20983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6044
  · exact u6045
  · exact u6046

def r20984 : Route 9 := (fun mask => (mask,id))

def c20984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20984 : Upper (D 7) (R 7) [34,257,65,130,160,4] 13 := by
  apply FastRouting.sound _ _ [34,257,65,130,160,4] 13 (by decide) (choices 1) [8,16] r20984 c20984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6047
  · exact u6048

def b20985 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 69 138 176 40 84 212 340), lower := (rows 35 259 69 138 176 40 64 128 256), losses := [] }

theorem u20985 : Upper (D 7) (R 7) [34,257,65,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20985 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20986 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 69 138 176 48 76 204 332), lower := (rows 35 259 69 138 176 48 64 128 256), losses := [] }

theorem u20986 : Upper (D 7) (R 7) [34,257,65,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20986 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20987 : Route 9 := (fun mask => (mask,id))

def c20987 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20987 : Upper (D 7) (R 7) [34,257,65,130,160,64] 13 := by
  apply FastRouting.sound _ _ [34,257,65,130,160,64] 13 (by decide) (choices 1) [4,8,16] r20987 c20987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6049
  · exact u6050
  · exact u6051

def r20988 : Route 9 := (fun mask => (mask,id))

def c20988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20988 : Upper (D 7) (R 7) [34,257,65,130,192,4] 13 := by
  apply FastRouting.sound _ _ [34,257,65,130,192,4] 13 (by decide) (choices 1) [8,16,32] r20988 c20988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6052
  · exact u6053
  · exact u6054

def b20989 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 259 69 138 208 40 116 180 308), lower := (rows 35 259 69 138 208 40 64 128 256), losses := [] }

theorem u20989 : Upper (D 7) (R 7) [34,257,65,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20989 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20990 : Route 9 := (fun mask => (mask,id))

def c20990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20990 : Upper (D 7) (R 7) [34,257,65,130,192,16] 13 := by
  apply FastRouting.sound _ _ [34,257,65,130,192,16] 13 (by decide) (choices 1) [4,8,32] r20990 c20990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6055
  · exact u6056
  · exact u6057

def b20991 : PairBound 9 := { available := 88, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 69 140 176 34 88 216 344), lower := (rows 35 259 69 140 176 34 64 128 256), losses := [] }

theorem u20991 : Upper (D 7) (R 7) [34,257,65,132,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20992 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 259 69 140 176 40 82 210 338), lower := (rows 35 259 69 140 176 40 64 128 256), losses := [] }

theorem u20992 : Upper (D 7) (R 7) [34,257,65,132,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20992 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20993 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 69 140 176 48 74 202 330), lower := (rows 35 259 69 140 176 48 64 128 256), losses := [] }

theorem u20993 : Upper (D 7) (R 7) [34,257,65,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20993 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20994 : Route 9 := (fun mask => (mask,id))

def c20994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20994 : Upper (D 7) (R 7) [34,257,65,132,160,64] 13 := by
  apply FastRouting.sound _ _ [34,257,65,132,160,64] 13 (by decide) (choices 1) [2,8,16] r20994 c20994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6058
  · exact u6059
  · exact u6060

def b20995 : PairBound 9 := { available := 56, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 69 140 208 34 120 184 312), lower := (rows 35 259 69 140 208 34 64 128 256), losses := [] }

theorem u20995 : Upper (D 7) (R 7) [34,257,65,132,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20996 : Route 9 := (fun mask => (mask,id))

def c20996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20996 : Upper (D 7) (R 7) [34,257,65,132,192,8] 13 := by
  apply FastRouting.sound _ _ [34,257,65,132,192,8] 13 (by decide) (choices 1) [2,16,32] r20996 c20996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6061
  · exact u6062
  · exact u6063

def r20997 : Route 9 := (fun mask => (mask,id))

def c20997 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20997 : Upper (D 7) (R 7) [34,257,65,132,192,16] 13 := by
  apply FastRouting.sound _ _ [34,257,65,132,192,16] 13 (by decide) (choices 1) [2,8,32] r20997 c20997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6064
  · exact u6065
  · exact u6066

def b20998 : PairBound 9 := { available := 28, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 69 168 208 34 92 156 284), lower := (rows 35 259 69 168 208 34 64 128 256), losses := [] }

theorem u20998 : Upper (D 7) (R 7) [34,257,65,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20999 : Route 9 := (fun mask => (mask,id))

def c20999 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20999 : Upper (D 7) (R 7) [34,257,65,160,192,4] 13 := by
  apply FastRouting.sound _ _ [34,257,65,160,192,4] 13 (by decide) (choices 1) [2,8,16] r20999 c20999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6067
  · exact u6068
  · exact u6069

#print axioms u20999
end Delivery.IrregularNine14.P07
