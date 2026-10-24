import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0101

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21000 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 259 69 168 208 40 86 150 278), lower := (rows 35 259 69 168 208 40 64 128 256), losses := [] }

theorem u21000 : Upper (D 7) (R 7) [34,257,65,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21000 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21001 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 69 168 208 48 78 142 270), lower := (rows 35 259 69 168 208 48 64 128 256), losses := [] }

theorem u21001 : Upper (D 7) (R 7) [34,257,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21001 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21002 : PairBound 9 := { available := 168, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 70 88 148 33 232 168 424), lower := (rows 35 259 70 88 148 33 64 128 256), losses := [] }

theorem u21002 : Upper (D 7) (R 7) [34,257,66,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21003 : Route 9 := (fun mask => (mask,id))

def c21003 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21003 : Upper (D 7) (R 7) [34,257,66,80,132,8] 13 := by
  apply FastRouting.sound _ _ [34,257,66,80,132,8] 13 (by decide) (choices 1) [1,32,128] r21003 c21003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6070
  · exact u6071
  · exact u6072

def r21004 : Route 9 := (fun mask => (mask,id))

def c21004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21004 : Upper (D 7) (R 7) [34,257,66,80,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,66,80,132,128] 13 (by decide) (choices 1) [1,8,32] r21004 c21004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6073
  · exact u6074
  · exact u6075

def b21005 : PairBound 9 := { available := 164, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 70 88 152 33 228 164 420), lower := (rows 35 259 70 88 152 33 64 128 256), losses := [] }

theorem u21005 : Upper (D 7) (R 7) [34,257,66,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21006 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 259 70 88 152 36 225 161 417), lower := (rows 35 259 70 88 152 36 64 128 256), losses := [] }

theorem u21006 : Upper (D 7) (R 7) [34,257,66,80,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21006 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21007 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 35 259 70 88 152 160 101 165 293), lower := (rows 35 259 70 88 152 160 64 128 256), losses := [] }

theorem u21007 : Upper (D 7) (R 7) [34,257,66,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21008 : PairBound 9 := { available := 140, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 70 88 176 33 204 140 396), lower := (rows 35 259 70 88 176 33 64 128 256), losses := [] }

theorem u21008 : Upper (D 7) (R 7) [34,257,66,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21009 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 259 70 88 176 36 201 137 393), lower := (rows 35 259 70 88 176 36 64 128 256), losses := [] }

theorem u21009 : Upper (D 7) (R 7) [34,257,66,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21009 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21010 : Route 9 := (fun mask => (mask,id))

def c21010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21010 : Upper (D 7) (R 7) [34,257,66,80,160,8] 13 := by
  apply FastRouting.sound _ _ [34,257,66,80,160,8] 13 (by decide) (choices 1) [1,4,128] r21010 c21010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6076
  · exact u6077
  · exact u6078

def b21011 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 70 88 176 160 77 141 269), lower := (rows 35 259 70 88 176 160 64 128 256), losses := [] }

theorem u21011 : Upper (D 7) (R 7) [34,257,66,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21012 : PairBound 9 := { available := 152, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 70 104 148 33 216 152 408), lower := (rows 35 259 70 104 148 33 64 128 256), losses := [] }

theorem u21012 : Upper (D 7) (R 7) [34,257,66,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21013 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 259 70 104 148 40 209 145 401), lower := (rows 35 259 70 104 148 40 64 128 256), losses := [] }

theorem u21013 : Upper (D 7) (R 7) [34,257,66,96,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21013 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21014 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 387, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(1,6),(3,1)], upper := (rows 35 259 70 104 148 48 201 137 393), lower := (rows 35 259 70 104 148 48 64 128 256), losses := [] }

theorem u21014 : Upper (D 7) (R 7) [34,257,66,96,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21014 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21015 : Route 9 := (fun mask => (mask,id))

def c21015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21015 : Upper (D 7) (R 7) [34,257,66,96,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,66,96,132,128] 13 (by decide) (choices 1) [1,8,16] r21015 c21015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6079
  · exact u6080
  · exact u6081

def b21016 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 70 104 152 33 212 148 404), lower := (rows 35 259 70 104 152 33 64 128 256), losses := [] }

theorem u21016 : Upper (D 7) (R 7) [34,257,66,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21017 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 70 104 152 36 209 145 401), lower := (rows 35 259 70 104 152 36 64 128 256), losses := [] }

theorem u21017 : Upper (D 7) (R 7) [34,257,66,96,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21017 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21018 : Route 9 := (fun mask => (mask,id))

def c21018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21018 : Upper (D 7) (R 7) [34,257,66,96,136,16] 13 := by
  apply FastRouting.sound _ _ [34,257,66,96,136,16] 13 (by decide) (choices 1) [1,4,128] r21018 c21018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6082
  · exact u6083
  · exact u6084

def r21019 : Route 9 := (fun mask => (mask,id))

def c21019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21019 : Upper (D 7) (R 7) [34,257,66,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,257,66,96,136,128] 13 (by decide) (choices 1) [1,4,16] r21019 c21019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6085
  · exact u6086
  · exact u6087

def b21020 : PairBound 9 := { available := 88, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 70 140 176 33 88 216 344), lower := (rows 35 259 70 140 176 33 64 128 256), losses := [] }

theorem u21020 : Upper (D 7) (R 7) [34,257,66,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21021 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 259 70 140 176 40 81 209 337), lower := (rows 35 259 70 140 176 40 64 128 256), losses := [] }

theorem u21021 : Upper (D 7) (R 7) [34,257,66,132,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21021 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21022 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 70 140 176 48 73 201 329), lower := (rows 35 259 70 140 176 48 64 128 256), losses := [] }

theorem u21022 : Upper (D 7) (R 7) [34,257,66,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21022 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21023 : Route 9 := (fun mask => (mask,id))

def c21023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21023 : Upper (D 7) (R 7) [34,257,66,132,160,64] 13 := by
  apply FastRouting.sound _ _ [34,257,66,132,160,64] 13 (by decide) (choices 1) [1,8,16] r21023 c21023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6088
  · exact u6089
  · exact u6090

def b21024 : PairBound 9 := { available := 56, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 70 140 208 33 120 184 312), lower := (rows 35 259 70 140 208 33 64 128 256), losses := [] }

theorem u21024 : Upper (D 7) (R 7) [34,257,66,132,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21025 : Route 9 := (fun mask => (mask,id))

def c21025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21025 : Upper (D 7) (R 7) [34,257,66,132,192,8] 13 := by
  apply FastRouting.sound _ _ [34,257,66,132,192,8] 13 (by decide) (choices 1) [1,16,32] r21025 c21025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6091
  · exact u6092
  · exact u6093

def r21026 : Route 9 := (fun mask => (mask,id))

def c21026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21026 : Upper (D 7) (R 7) [34,257,66,132,192,16] 13 := by
  apply FastRouting.sound _ _ [34,257,66,132,192,16] 13 (by decide) (choices 1) [1,8,32] r21026 c21026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6094
  · exact u6095
  · exact u6096

def b21027 : PairBound 9 := { available := 28, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 70 168 208 33 92 156 284), lower := (rows 35 259 70 168 208 33 64 128 256), losses := [] }

theorem u21027 : Upper (D 7) (R 7) [34,257,66,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21028 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 259 70 168 208 36 89 153 281), lower := (rows 35 259 70 168 208 36 64 128 256), losses := [] }

theorem u21028 : Upper (D 7) (R 7) [34,257,66,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21028 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21029 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 259 70 168 208 40 85 149 277), lower := (rows 35 259 70 168 208 40 64 128 256), losses := [] }

theorem u21029 : Upper (D 7) (R 7) [34,257,66,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21029 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21030 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 70 168 208 48 77 141 269), lower := (rows 35 259 70 168 208 48 64 128 256), losses := [] }

theorem u21030 : Upper (D 7) (R 7) [34,257,66,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21030 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21031 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 76 140 112 33 210 146 402), lower := (rows 35 259 76 140 112 33 64 128 256), losses := [] }

theorem u21031 : Upper (D 7) (R 7) [34,257,72,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21032 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 76 140 112 34 209 145 401), lower := (rows 35 259 76 140 112 34 64 128 256), losses := [] }

theorem u21032 : Upper (D 7) (R 7) [34,257,72,132,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21033 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 76 140 112 48 195 131 387), lower := (rows 35 259 76 140 112 48 64 128 256), losses := [] }

theorem u21033 : Upper (D 7) (R 7) [34,257,72,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21033 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21034 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 4, region := 259, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,7)], upper := (rows 35 259 76 140 112 160 83 147 275), lower := (rows 35 259 76 140 112 160 64 128 256), losses := [] }

theorem u21034 : Upper (D 7) (R 7) [34,257,72,132,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21035 : PairBound 9 := { available := 134, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 76 152 112 33 198 134 390), lower := (rows 35 259 76 152 112 33 64 128 256), losses := [] }

theorem u21035 : Upper (D 7) (R 7) [34,257,72,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21036 : PairBound 9 := { available := 133, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 76 152 112 34 197 133 389), lower := (rows 35 259 76 152 112 34 64 128 256), losses := [] }

theorem u21036 : Upper (D 7) (R 7) [34,257,72,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21037 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 48, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 35 259 76 152 112 36 195 131 387), lower := (rows 35 259 76 152 112 36 64 128 256), losses := [] }

theorem u21037 : Upper (D 7) (R 7) [34,257,72,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21037 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21038 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 35 259 76 152 112 160 71 135 263), lower := (rows 35 259 76 152 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 34 258 124 184 112 160 64 160 256) },{ target := 1, region := (rows 1 0 4 8 20 168 64 128 256), good := (rows 33 257 124 184 112 160 64 160 256) }] }

theorem u21038 : Upper (D 7) (R 7) [34,257,72,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21039 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 76 168 208 33 86 150 278), lower := (rows 35 259 76 168 208 33 64 128 256), losses := [] }

theorem u21039 : Upper (D 7) (R 7) [34,257,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21040 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 76 168 208 34 85 149 277), lower := (rows 35 259 76 168 208 34 64 128 256), losses := [] }

theorem u21040 : Upper (D 7) (R 7) [34,257,72,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21041 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 259 76 168 208 36 83 147 275), lower := (rows 35 259 76 168 208 36 64 128 256), losses := [] }

theorem u21041 : Upper (D 7) (R 7) [34,257,72,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21041 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21042 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 259 76 168 208 48 71 135 263), lower := (rows 35 259 76 168 208 48 64 128 256), losses := [] }

theorem u21042 : Upper (D 7) (R 7) [34,257,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21042 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21043 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0),(1,6),(2,6),(4,1)], upper := (rows 35 262 13 26 81 96 224 160 416), lower := (rows 35 262 13 26 81 96 64 128 256), losses := [{ target := 6, region := (rows 1 22 20 24 16 32 0 161 289), good := (rows 419 262 399 30 415 416 0 128 256) }] }

theorem u21043 : Upper (D 7) (R 7) [34,260,9,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21044 : Route 9 := (fun mask => (mask,id))

def c21044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21044 : Upper (D 7) (R 7) [34,260,9,18,65,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,18,65,128] 13 (by decide) (choices 1) [32,128] r21044 c21044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6097
  · exact u6098

def b21045 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 262 13 26 112 33 192 192 448), lower := (rows 35 262 13 26 112 33 64 128 256), losses := [] }

theorem u21045 : Upper (D 7) (R 7) [34,260,9,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21046 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 35 262 13 26 112 96 193 129 385), lower := (rows 35 262 13 26 112 96 64 128 256), losses := [] }

theorem u21046 : Upper (D 7) (R 7) [34,260,9,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21047 : Route 9 := (fun mask => (mask,id))

def c21047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21047 : Upper (D 7) (R 7) [34,260,9,18,96,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,18,96,128] 13 (by decide) (choices 1) [1,128] r21047 c21047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6099
  · exact u6100

def b21048 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 262 13 26 208 33 224 224 480), lower := (rows 35 262 13 26 208 33 64 128 256), losses := [] }

theorem u21048 : Upper (D 7) (R 7) [34,260,9,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21049 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(0,7),(1,6),(2,7),(4,1)], upper := (rows 35 262 13 26 208 96 225 161 417), lower := (rows 35 262 13 26 208 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 32 0 129 257), good := (rows 419 262 399 26 144 32 0 128 256) },{ target := 7, region := (rows 9 2 12 8 16 112 64 0 256), good := (rows 35 262 13 63 112 96 96 0 256) }] }

theorem u21049 : Upper (D 7) (R 7) [34,260,9,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21050 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 262 13 56 82 33 192 192 448), lower := (rows 35 262 13 56 82 33 64 128 256), losses := [] }

theorem u21050 : Upper (D 7) (R 7) [34,260,9,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21051 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(2,6)], upper := (rows 35 262 13 56 82 96 193 129 385), lower := (rows 35 262 13 56 82 96 64 128 256), losses := [] }

theorem u21051 : Upper (D 7) (R 7) [34,260,9,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21052 : Route 9 := (fun mask => (mask,id))

def c21052 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21052 : Upper (D 7) (R 7) [34,260,9,48,66,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,48,66,128] 13 (by decide) (choices 1) [1,128] r21052 c21052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6101
  · exact u6102

def b21053 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 262 13 56 208 33 194 194 450), lower := (rows 35 262 13 56 208 33 64 128 256), losses := [] }

theorem u21053 : Upper (D 7) (R 7) [34,260,9,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21054 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 13 56 208 34 193 193 449), lower := (rows 35 262 13 56 208 34 64 128 256), losses := [] }

theorem u21054 : Upper (D 7) (R 7) [34,260,9,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21055 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 35 262 13 56 208 96 195 131 387), lower := (rows 35 262 13 56 208 96 64 128 256), losses := [] }

theorem u21055 : Upper (D 7) (R 7) [34,260,9,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21056 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 53, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 35 262 13 74 81 48 224 160 416), lower := (rows 35 262 13 74 81 48 64 128 256), losses := [] }

theorem u21056 : Upper (D 7) (R 7) [34,260,9,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21056 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21057 : Route 9 := (fun mask => (mask,id))

def c21057 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u21057 : Upper (D 7) (R 7) [34,260,9,66,65,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,66,65,128] 13 (by decide) (choices 1) [16,32,128] r21057 c21057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6103
  · exact u6104
  · exact u6105

def b21058 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 0, region := 216, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 35 262 13 74 112 33 208 144 400), lower := (rows 35 262 13 74 112 33 64 128 256), losses := [] }

theorem u21058 : Upper (D 7) (R 7) [34,260,9,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21059 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 13 74 112 48 193 129 385), lower := (rows 35 262 13 74 112 48 64 128 256), losses := [] }

theorem u21059 : Upper (D 7) (R 7) [34,260,9,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21059 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u21059
end Delivery.IrregularNine14.P07
