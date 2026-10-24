import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0110

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22140 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 76 266 81 48 100 164 292), lower := (rows 35 131 76 266 81 48 64 128 256), losses := [] }

theorem u22140 : Upper (D 6) (R 6) [34,129,72,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22140 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22141 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 266 112 33 84 148 276), lower := (rows 35 131 76 266 112 33 64 128 256), losses := [] }

theorem u22141 : Upper (D 6) (R 6) [34,129,72,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22142 : Route 9 := (fun mask => (mask,id))

def c22142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22142 : Upper (D 6) (R 6) [34,129,72,258,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,258,96,4] 13 (by decide) (choices 1) [1,4,16] r22142 c22142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6603
  · exact u6604
  · exact u6605

def b22143 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 266 112 48 69 133 261), lower := (rows 35 131 76 266 112 48 64 128 256), losses := [] }

theorem u22143 : Upper (D 6) (R 6) [34,129,72,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22143 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22144 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 268 21 34 112 240 368), lower := (rows 35 131 76 268 21 34 64 128 256), losses := [] }

theorem u22144 : Upper (D 6) (R 6) [34,129,72,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22145 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 76 268 21 48 98 226 354), lower := (rows 35 131 76 268 21 48 64 128 256), losses := [] }

theorem u22145 : Upper (D 6) (R 6) [34,129,72,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22145 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22146 : Route 9 := (fun mask => (mask,id))

def c22146 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22146 : Upper (D 6) (R 6) [34,129,72,260,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,260,5,64] 13 (by decide) (choices 1) [2,16,32] r22146 c22146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6606
  · exact u6607
  · exact u6608

def b22147 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 268 22 33 112 240 368), lower := (rows 35 131 76 268 22 33 64 128 256), losses := [] }

theorem u22147 : Upper (D 6) (R 6) [34,129,72,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22148 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 76 268 22 48 97 225 353), lower := (rows 35 131 76 268 22 48 64 128 256), losses := [] }

theorem u22148 : Upper (D 6) (R 6) [34,129,72,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22148 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22149 : Route 9 := (fun mask => (mask,id))

def c22149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22149 : Upper (D 6) (R 6) [34,129,72,260,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,260,6,64] 13 (by decide) (choices 1) [1,16,32] r22149 c22149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6609
  · exact u6610
  · exact u6611

def b22150 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 268 52 33 82 210 338), lower := (rows 35 131 76 268 52 33 64 128 256), losses := [] }

theorem u22150 : Upper (D 6) (R 6) [34,129,72,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22151 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 268 52 34 81 209 337), lower := (rows 35 131 76 268 52 34 64 128 256), losses := [] }

theorem u22151 : Upper (D 6) (R 6) [34,129,72,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22152 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 268 52 48 67 195 323), lower := (rows 35 131 76 268 52 48 64 128 256), losses := [] }

theorem u22152 : Upper (D 6) (R 6) [34,129,72,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22152 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22153 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 76 268 52 96 83 147 275), lower := (rows 35 131 76 268 52 96 64 128 256), losses := [] }

theorem u22153 : Upper (D 6) (R 6) [34,129,72,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22154 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 268 81 34 116 180 308), lower := (rows 35 131 76 268 81 34 64 128 256), losses := [] }

theorem u22154 : Upper (D 6) (R 6) [34,129,72,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22155 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 268 81 36 114 178 306), lower := (rows 35 131 76 268 81 36 64 128 256), losses := [] }

theorem u22155 : Upper (D 6) (R 6) [34,129,72,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22156 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 76 268 81 48 102 166 294), lower := (rows 35 131 76 268 81 48 64 128 256), losses := [] }

theorem u22156 : Upper (D 6) (R 6) [34,129,72,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22156 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22157 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 268 82 33 116 180 308), lower := (rows 35 131 76 268 82 33 64 128 256), losses := [] }

theorem u22157 : Upper (D 6) (R 6) [34,129,72,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22158 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 268 82 36 113 177 305), lower := (rows 35 131 76 268 82 36 64 128 256), losses := [] }

theorem u22158 : Upper (D 6) (R 6) [34,129,72,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22159 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 76 268 82 48 101 165 293), lower := (rows 35 131 76 268 82 48 64 128 256), losses := [] }

theorem u22159 : Upper (D 6) (R 6) [34,129,72,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22159 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22160 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 268 112 33 86 150 278), lower := (rows 35 131 76 268 112 33 64 128 256), losses := [] }

theorem u22160 : Upper (D 6) (R 6) [34,129,72,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22161 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 268 112 34 85 149 277), lower := (rows 35 131 76 268 112 34 64 128 256), losses := [] }

theorem u22161 : Upper (D 6) (R 6) [34,129,72,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22162 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 268 112 36 83 147 275), lower := (rows 35 131 76 268 112 36 64 128 256), losses := [] }

theorem u22162 : Upper (D 6) (R 6) [34,129,72,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22163 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 268 112 48 71 135 263), lower := (rows 35 131 76 268 112 48 64 128 256), losses := [] }

theorem u22163 : Upper (D 6) (R 6) [34,129,72,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22163 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22164 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 21 34 100 228 356), lower := (rows 35 131 76 280 21 34 64 128 256), losses := [] }

theorem u22164 : Upper (D 6) (R 6) [34,129,72,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22165 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 76 280 21 36 98 226 354), lower := (rows 35 131 76 280 21 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 60 65 129 257), good := (rows 482 450 108 316 508 36 64 128 256) }] }

theorem u22165 : Upper (D 6) (R 6) [34,129,72,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22166 : Route 9 := (fun mask => (mask,id))

def c22166 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22166 : Upper (D 6) (R 6) [34,129,72,272,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,272,5,64] 13 (by decide) (choices 1) [2,4,32] r22166 c22166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6612
  · exact u6613
  · exact u6614

def b22167 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 22 33 100 228 356), lower := (rows 35 131 76 280 22 33 64 128 256), losses := [] }

theorem u22167 : Upper (D 6) (R 6) [34,129,72,272,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22168 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 22 36 97 225 353), lower := (rows 35 131 76 280 22 36 64 128 256), losses := [] }

theorem u22168 : Upper (D 6) (R 6) [34,129,72,272,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22169 : Route 9 := (fun mask => (mask,id))

def c22169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22169 : Upper (D 6) (R 6) [34,129,72,272,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,272,6,64] 13 (by decide) (choices 1) [1,4,32] r22169 c22169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6615
  · exact u6616
  · exact u6617

def b22170 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 52 33 70 198 326), lower := (rows 35 131 76 280 52 33 64 128 256), losses := [] }

theorem u22170 : Upper (D 6) (R 6) [34,129,72,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22171 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 52 34 69 197 325), lower := (rows 35 131 76 280 52 34 64 128 256), losses := [] }

theorem u22171 : Upper (D 6) (R 6) [34,129,72,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22172 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 76 280 52 36 67 195 323), lower := (rows 35 131 76 280 52 36 64 128 256), losses := [] }

theorem u22172 : Upper (D 6) (R 6) [34,129,72,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22173 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 76 280 52 96 71 135 263), lower := (rows 35 131 76 280 52 96 64 128 256), losses := [] }

theorem u22173 : Upper (D 6) (R 6) [34,129,72,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22174 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 81 34 100 164 292), lower := (rows 35 131 76 280 81 34 64 128 256), losses := [] }

theorem u22174 : Upper (D 6) (R 6) [34,129,72,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22175 : Route 9 := (fun mask => (mask,id))

def c22175 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22175 : Upper (D 6) (R 6) [34,129,72,272,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,272,65,4] 13 (by decide) (choices 1) [2,4,32] r22175 c22175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6618
  · exact u6619
  · exact u6620

def b22176 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 82 33 100 164 292), lower := (rows 35 131 76 280 82 33 64 128 256), losses := [] }

theorem u22176 : Upper (D 6) (R 6) [34,129,72,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22177 : Route 9 := (fun mask => (mask,id))

def c22177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22177 : Upper (D 6) (R 6) [34,129,72,272,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,272,66,4] 13 (by decide) (choices 1) [1,4,32] r22177 c22177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6621
  · exact u6622
  · exact u6623

def b22178 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 112 33 70 134 262), lower := (rows 35 131 76 280 112 33 64 128 256), losses := [] }

theorem u22178 : Upper (D 6) (R 6) [34,129,72,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22179 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 112 34 69 133 261), lower := (rows 35 131 76 280 112 34 64 128 256), losses := [] }

theorem u22179 : Upper (D 6) (R 6) [34,129,72,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22180 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 76 280 112 36 71 135 263), lower := (rows 35 131 76 280 112 36 64 128 256), losses := [] }

theorem u22180 : Upper (D 6) (R 6) [34,129,72,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22181 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 296 21 34 84 212 340), lower := (rows 35 131 76 296 21 34 64 128 256), losses := [] }

theorem u22181 : Upper (D 6) (R 6) [34,129,72,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22182 : Route 9 := (fun mask => (mask,id))

def c22182 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22182 : Upper (D 6) (R 6) [34,129,72,288,5,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,288,5,4] 13 (by decide) (choices 1) [2,16] r22182 c22182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6624
  · exact u6625

def b22183 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 76 296 21 48 70 198 326), lower := (rows 35 131 76 296 21 48 64 128 256), losses := [] }

theorem u22183 : Upper (D 6) (R 6) [34,129,72,288,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22183 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22184 : Route 9 := (fun mask => (mask,id))

def c22184 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22184 : Upper (D 6) (R 6) [34,129,72,288,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,288,5,64] 13 (by decide) (choices 1) [2,4,16] r22184 c22184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6626
  · exact u6627
  · exact u6628

def b22185 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 296 22 33 84 212 340), lower := (rows 35 131 76 296 22 33 64 128 256), losses := [] }

theorem u22185 : Upper (D 6) (R 6) [34,129,72,288,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22186 : Route 9 := (fun mask => (mask,id))

def c22186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22186 : Upper (D 6) (R 6) [34,129,72,288,6,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,288,6,4] 13 (by decide) (choices 1) [1,16] r22186 c22186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6629
  · exact u6630

def b22187 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 76 296 22 48 69 197 325), lower := (rows 35 131 76 296 22 48 64 128 256), losses := [] }

theorem u22187 : Upper (D 6) (R 6) [34,129,72,288,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22187 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22188 : Route 9 := (fun mask => (mask,id))

def c22188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22188 : Upper (D 6) (R 6) [34,129,72,288,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,288,6,64] 13 (by decide) (choices 1) [1,4,16] r22188 c22188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6631
  · exact u6632
  · exact u6633

def b22189 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 296 81 34 84 148 276), lower := (rows 35 131 76 296 81 34 64 128 256), losses := [] }

theorem u22189 : Upper (D 6) (R 6) [34,129,72,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22190 : Route 9 := (fun mask => (mask,id))

def c22190 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22190 : Upper (D 6) (R 6) [34,129,72,288,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,288,65,4] 13 (by decide) (choices 1) [2,4,16] r22190 c22190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6634
  · exact u6635
  · exact u6636

def b22191 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 76 296 81 48 70 134 262), lower := (rows 35 131 76 296 81 48 64 128 256), losses := [] }

theorem u22191 : Upper (D 6) (R 6) [34,129,72,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22191 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22192 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 296 82 33 84 148 276), lower := (rows 35 131 76 296 82 33 64 128 256), losses := [] }

theorem u22192 : Upper (D 6) (R 6) [34,129,72,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22193 : Route 9 := (fun mask => (mask,id))

def c22193 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22193 : Upper (D 6) (R 6) [34,129,72,288,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,72,288,66,4] 13 (by decide) (choices 1) [1,4,16] r22193 c22193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6637
  · exact u6638
  · exact u6639

def b22194 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 76 296 82 48 69 133 261), lower := (rows 35 131 76 296 82 48 64 128 256), losses := [] }

theorem u22194 : Upper (D 6) (R 6) [34,129,72,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22194 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22195 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 100 13 22 40 336 464 336), lower := (rows 35 131 100 13 22 40 64 128 256), losses := [] }

theorem u22195 : Upper (D 6) (R 6) [34,129,96,5,6,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22195 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22196 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 100 13 22 48 328 456 328), lower := (rows 35 131 100 13 22 48 64 128 256), losses := [] }

theorem u22196 : Upper (D 6) (R 6) [34,129,96,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22196 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22197 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 13 22 96 344 408 280), lower := (rows 35 131 100 13 22 96 64 128 256), losses := [] }

theorem u22197 : Upper (D 6) (R 6) [34,129,96,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22198 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 131 100 13 22 288 88 216 344), lower := (rows 35 131 100 13 22 288 64 128 256), losses := [] }

theorem u22198 : Upper (D 6) (R 6) [34,129,96,5,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22198 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22199 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 100 13 82 36 344 408 280), lower := (rows 35 131 100 13 82 36 64 128 256), losses := [] }

theorem u22199 : Upper (D 6) (R 6) [34,129,96,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22199
end Delivery.IrregularNine14.P06
