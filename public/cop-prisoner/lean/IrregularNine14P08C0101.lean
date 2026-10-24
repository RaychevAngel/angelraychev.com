import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0012

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6060 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 164 41 152 33 112 240 368), lower := (rows 259 70 164 41 152 33 64 128 256), losses := [] }

theorem u6060 : Upper (D 8) (R 8) [258,68,160,33,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6061 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 259 70 164 41 152 48 97 225 353), lower := (rows 259 70 164 41 152 48 64 128 256), losses := [] }

theorem u6061 : Upper (D 8) (R 8) [258,68,160,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6061 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6062 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 148, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 164 41 152 96 113 177 305), lower := (rows 259 70 164 41 152 96 64 128 256), losses := [] }

theorem u6062 : Upper (D 8) (R 8) [258,68,160,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6063 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 164 41 208 33 120 184 312), lower := (rows 259 70 164 41 208 33 64 128 256), losses := [] }

theorem u6063 : Upper (D 8) (R 8) [258,68,160,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6064 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 70 164 41 208 40 113 177 305), lower := (rows 259 70 164 41 208 40 64 128 256), losses := [] }

theorem u6064 : Upper (D 8) (R 8) [258,68,160,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6064 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6065 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 259 70 164 41 208 48 105 169 297), lower := (rows 259 70 164 41 208 48 64 128 256), losses := [] }

theorem u6065 : Upper (D 8) (R 8) [258,68,160,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6065 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6066 : Route 9 := (fun mask => (mask,id))

def c6066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6066 : Upper (D 8) (R 8) [258,68,160,48,192,1] 13 := by
  apply FastRouting.sound _ _ [258,68,160,48,192,1] 13 (by decide) (choices 1) [1,8,32] r6066 c6066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u751
  · exact u752
  · exact u753

def b6067 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 70 164 56 208 40 97 161 289), lower := (rows 259 70 164 56 208 40 64 128 256), losses := [] }

theorem u6067 : Upper (D 8) (R 8) [258,68,160,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6067 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6068 : Route 9 := (fun mask => (mask,id))

def c6068 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6068 : Upper (D 8) (R 8) [258,68,160,96,136,1] 13 := by
  apply FastRouting.sound _ _ [258,68,160,96,136,1] 13 (by decide) (choices 1) [1,16,32] r6068 c6068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u754
  · exact u755
  · exact u756

def b6069 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 70 164 104 152 48 97 161 289), lower := (rows 259 70 164 104 152 48 64 128 256), losses := [] }

theorem u6069 : Upper (D 8) (R 8) [258,68,160,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6069 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6070 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 28 176 33 224 224 480), lower := (rows 259 98 13 28 176 33 64 128 256), losses := [] }

theorem u6070 : Upper (D 8) (R 8) [258,96,9,20,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6071 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 28 176 96 225 161 417), lower := (rows 259 98 13 28 176 96 64 128 256), losses := [] }

theorem u6071 : Upper (D 8) (R 8) [258,96,9,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6072 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 28 176 160 97 225 353), lower := (rows 259 98 13 28 176 160 64 128 256), losses := [] }

theorem u6072 : Upper (D 8) (R 8) [258,96,9,20,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6073 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 44 176 33 208 208 464), lower := (rows 259 98 13 44 176 33 64 128 256), losses := [] }

theorem u6073 : Upper (D 8) (R 8) [258,96,9,36,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6074 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 98 13 44 176 48 193 193 449), lower := (rows 259 98 13 44 176 48 64 128 256), losses := [] }

theorem u6074 : Upper (D 8) (R 8) [258,96,9,36,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6074 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6075 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 44 176 96 209 145 401), lower := (rows 259 98 13 44 176 96 64 128 256), losses := [] }

theorem u6075 : Upper (D 8) (R 8) [258,96,9,36,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6076 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 44 176 160 81 209 337), lower := (rows 259 98 13 44 176 160 64 128 256), losses := [] }

theorem u6076 : Upper (D 8) (R 8) [258,96,9,36,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6077 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 44 208 33 240 176 432), lower := (rows 259 98 13 44 208 33 64 128 256), losses := [] }

theorem u6077 : Upper (D 8) (R 8) [258,96,9,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6078 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 98 13 44 208 48 225 161 417), lower := (rows 259 98 13 44 208 48 64 128 256), losses := [] }

theorem u6078 : Upper (D 8) (R 8) [258,96,9,36,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6078 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6079 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 44 208 160 113 177 305), lower := (rows 259 98 13 44 208 160 64 128 256), losses := [] }

theorem u6079 : Upper (D 8) (R 8) [258,96,9,36,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6080 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 56 148 33 224 224 480), lower := (rows 259 98 13 56 148 33 64 128 256), losses := [] }

theorem u6080 : Upper (D 8) (R 8) [258,96,9,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6081 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 56 148 96 225 161 417), lower := (rows 259 98 13 56 148 96 64 128 256), losses := [] }

theorem u6081 : Upper (D 8) (R 8) [258,96,9,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6082 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 56 148 160 97 225 353), lower := (rows 259 98 13 56 148 160 64 128 256), losses := [] }

theorem u6082 : Upper (D 8) (R 8) [258,96,9,48,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6083 : Route 9 := (fun mask => (mask,id))

def c6083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u6083 : Upper (D 8) (R 8) [258,96,9,48,192,1] 13 := by
  apply FastRouting.sound _ _ [258,96,9,48,192,1] 13 (by decide) (choices 1) [4,32,128] r6083 c6083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u757
  · exact u758
  · exact u759

def b6084 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 98 13 56 208 36 225 161 417), lower := (rows 259 98 13 56 208 36 64 128 256), losses := [] }

theorem u6084 : Upper (D 8) (R 8) [258,96,9,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6084 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6085 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 56 208 160 101 165 293), lower := (rows 259 98 13 56 208 160 64 128 256), losses := [] }

theorem u6085 : Upper (D 8) (R 8) [258,96,9,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6086 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 259 98 13 152 52 33 224 224 480), lower := (rows 259 98 13 152 52 33 64 128 256), losses := [] }

theorem u6086 : Upper (D 8) (R 8) [258,96,9,144,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6087 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 152 52 96 225 161 417), lower := (rows 259 98 13 152 52 96 64 128 256), losses := [] }

theorem u6087 : Upper (D 8) (R 8) [258,96,9,144,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6088 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 152 52 160 97 225 353), lower := (rows 259 98 13 152 52 160 64 128 256), losses := [] }

theorem u6088 : Upper (D 8) (R 8) [258,96,9,144,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6089 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 259 98 13 168 49 36 208 208 464), lower := (rows 259 98 13 168 49 36 64 128 256), losses := [] }

theorem u6089 : Upper (D 8) (R 8) [258,96,9,160,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6089 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6090 : PairBound 9 := { available := 196, camps := [], pairs := [], upper := (rows 259 98 13 168 49 48 196 196 452), lower := (rows 259 98 13 168 49 48 64 128 256), losses := [] }

theorem u6090 : Upper (D 8) (R 8) [258,96,9,160,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6090 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6091 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 168 49 96 212 148 404), lower := (rows 259 98 13 168 49 96 64 128 256), losses := [] }

theorem u6091 : Upper (D 8) (R 8) [258,96,9,160,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6092 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 168 49 160 84 212 340), lower := (rows 259 98 13 168 49 160 64 128 256), losses := [] }

theorem u6092 : Upper (D 8) (R 8) [258,96,9,160,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6093 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 259 98 13 168 52 33 208 208 464), lower := (rows 259 98 13 168 52 33 64 128 256), losses := [] }

theorem u6093 : Upper (D 8) (R 8) [258,96,9,160,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6094 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 98 13 168 52 48 193 193 449), lower := (rows 259 98 13 168 52 48 64 128 256), losses := [] }

theorem u6094 : Upper (D 8) (R 8) [258,96,9,160,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6094 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6095 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 168 52 96 209 145 401), lower := (rows 259 98 13 168 52 96 64 128 256), losses := [] }

theorem u6095 : Upper (D 8) (R 8) [258,96,9,160,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6096 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 168 52 160 81 209 337), lower := (rows 259 98 13 168 52 160 64 128 256), losses := [] }

theorem u6096 : Upper (D 8) (R 8) [258,96,9,160,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6097 : PairBound 9 := { available := 176, camps := [], pairs := [(3,6)], upper := (rows 259 98 13 168 84 33 240 176 432), lower := (rows 259 98 13 168 84 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 24 16 37 0 144 272), good := (rows 291 34 45 168 444 33 0 128 256) }] }

theorem u6097 : Upper (D 8) (R 8) [258,96,9,160,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6098 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 98 13 168 84 48 225 161 417), lower := (rows 259 98 13 168 84 48 64 128 256), losses := [] }

theorem u6098 : Upper (D 8) (R 8) [258,96,9,160,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6098 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6099 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 168 84 160 113 177 305), lower := (rows 259 98 13 168 84 160 64 128 256), losses := [] }

theorem u6099 : Upper (D 8) (R 8) [258,96,9,160,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6100 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 259 98 13 168 145 36 112 240 368), lower := (rows 259 98 13 168 145 36 64 128 256), losses := [] }

theorem u6100 : Upper (D 8) (R 8) [258,96,9,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6100 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6101 : PairBound 9 := { available := 100, camps := [], pairs := [], upper := (rows 259 98 13 168 145 48 100 228 356), lower := (rows 259 98 13 168 145 48 64 128 256), losses := [] }

theorem u6101 : Upper (D 8) (R 8) [258,96,9,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6101 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6102 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 168 145 96 116 180 308), lower := (rows 259 98 13 168 145 96 64 128 256), losses := [] }

theorem u6102 : Upper (D 8) (R 8) [258,96,9,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6103 : Route 9 := (fun mask => (mask,id))

def c6103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6103 : Upper (D 8) (R 8) [258,96,9,160,192,1] 13 := by
  apply FastRouting.sound _ _ [258,96,9,160,192,1] 13 (by decide) (choices 1) [4,16,32] r6103 c6103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u760
  · exact u761
  · exact u762

def b6104 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 98 13 168 208 36 113 177 305), lower := (rows 259 98 13 168 208 36 64 128 256), losses := [] }

theorem u6104 : Upper (D 8) (R 8) [258,96,9,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6104 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6105 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 259 98 13 168 208 48 101 165 293), lower := (rows 259 98 13 168 208 48 64 128 256), losses := [] }

theorem u6105 : Upper (D 8) (R 8) [258,96,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6105 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6106 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 28 41 148 33 224 224 480), lower := (rows 259 98 28 41 148 33 64 128 256), losses := [] }

theorem u6106 : Upper (D 8) (R 8) [258,96,24,33,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6107 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 28 41 148 96 225 161 417), lower := (rows 259 98 28 41 148 96 64 128 256), losses := [] }

theorem u6107 : Upper (D 8) (R 8) [258,96,24,33,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6108 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 28 41 148 160 97 225 353), lower := (rows 259 98 28 41 148 160 64 128 256), losses := [] }

theorem u6108 : Upper (D 8) (R 8) [258,96,24,33,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6109 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 28 41 176 33 196 196 452), lower := (rows 259 98 28 41 176 33 64 128 256), losses := [] }

theorem u6109 : Upper (D 8) (R 8) [258,96,24,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6110 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 98 28 41 176 36 193 193 449), lower := (rows 259 98 28 41 176 36 64 128 256), losses := [] }

theorem u6110 : Upper (D 8) (R 8) [258,96,24,33,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6110 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6111 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 28 41 176 96 197 133 389), lower := (rows 259 98 28 41 176 96 64 128 256), losses := [] }

theorem u6111 : Upper (D 8) (R 8) [258,96,24,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6112 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 28 41 176 160 69 197 325), lower := (rows 259 98 28 41 176 160 64 128 256), losses := [] }

theorem u6112 : Upper (D 8) (R 8) [258,96,24,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6113 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 28 41 208 33 228 164 420), lower := (rows 259 98 28 41 208 33 64 128 256), losses := [] }

theorem u6113 : Upper (D 8) (R 8) [258,96,24,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6114 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 98 28 41 208 36 225 161 417), lower := (rows 259 98 28 41 208 36 64 128 256), losses := [] }

theorem u6114 : Upper (D 8) (R 8) [258,96,24,33,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6114 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6115 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 28 41 208 160 101 165 293), lower := (rows 259 98 28 41 208 160 64 128 256), losses := [] }

theorem u6115 : Upper (D 8) (R 8) [258,96,24,33,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6116 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 28 44 145 33 224 224 480), lower := (rows 259 98 28 44 145 33 64 128 256), losses := [] }

theorem u6116 : Upper (D 8) (R 8) [258,96,24,36,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6117 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 28 44 145 96 225 161 417), lower := (rows 259 98 28 44 145 96 64 128 256), losses := [] }

theorem u6117 : Upper (D 8) (R 8) [258,96,24,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6118 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 44, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 28 44 145 160 97 225 353), lower := (rows 259 98 28 44 145 160 64 128 256), losses := [] }

theorem u6118 : Upper (D 8) (R 8) [258,96,24,36,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6119 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 37 56 84 33 200 136 392), lower := (rows 259 98 37 56 84 33 64 128 256), losses := [] }

theorem u6119 : Upper (D 8) (R 8) [258,96,33,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6119
end Delivery.IrregularNine14.P08
