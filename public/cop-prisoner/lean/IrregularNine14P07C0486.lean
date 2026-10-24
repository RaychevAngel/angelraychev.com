import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0185

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29160 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 56, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 97 262 133 26 56 34 193 193 449), lower := (rows 97 262 133 26 56 34 64 128 256), losses := [] }

theorem u29160 : Upper (D 7) (R 7) [96,260,129,18,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29161 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 26 56 96 195 131 387), lower := (rows 97 262 133 26 56 96 64 128 256), losses := [] }

theorem u29161 : Upper (D 7) (R 7) [96,260,129,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29162 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 2, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,5),(3,0)], upper := (rows 97 262 133 26 56 160 67 195 323), lower := (rows 97 262 133 26 56 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 164 64 128 256), good := (rows 96 318 164 26 56 160 64 160 256) }] }

theorem u29162 : Upper (D 7) (R 7) [96,260,129,18,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29163 : Route 9 := (fun mask => (mask,id))

def c29163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29163 : Upper (D 7) (R 7) [96,260,129,18,136,1] 13 := by
  apply FastRouting.sound _ _ [96,260,129,18,136,1] 13 (by decide) (choices 1) [2,32] r29163 c29163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11111
  · exact u11112

def b29164 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,1)], upper := (rows 97 262 133 26 152 34 97 225 353), lower := (rows 97 262 133 26 152 34 64 128 256), losses := [] }

theorem u29164 : Upper (D 7) (R 7) [96,260,129,18,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29165 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 26 152 96 99 163 291), lower := (rows 97 262 133 26 152 96 64 128 256), losses := [] }

theorem u29165 : Upper (D 7) (R 7) [96,260,129,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29166 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,6)], upper := (rows 97 262 133 26 176 33 74 202 330), lower := (rows 97 262 133 26 176 33 64 128 256), losses := [] }

theorem u29166 : Upper (D 7) (R 7) [96,260,129,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29167 : Route 9 := (fun mask => (mask,id))

def c29167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29167 : Upper (D 7) (R 7) [96,260,129,18,160,2] 13 := by
  apply FastRouting.sound _ _ [96,260,129,18,160,2] 13 (by decide) (choices 1) [1,8] r29167 c29167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11113
  · exact u11114

def b29168 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 2, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 97 262 133 26 176 40 67 195 323), lower := (rows 97 262 133 26 176 40 64 128 256), losses := [] }

theorem u29168 : Upper (D 7) (R 7) [96,260,129,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29168 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29169 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 26 176 96 75 139 267), lower := (rows 97 262 133 26 176 96 64 128 256), losses := [] }

theorem u29169 : Upper (D 7) (R 7) [96,260,129,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29170 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 4, region := 41, targets := 128 }], pairs := [(0,7),(3,7),(4,0),(4,5)], upper := (rows 97 262 133 42 82 33 216 152 408), lower := (rows 97 262 133 42 82 33 64 128 256), losses := [] }

theorem u29170 : Upper (D 7) (R 7) [96,260,129,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29171 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 133 42 82 40 209 145 401), lower := (rows 97 262 133 42 82 40 64 128 256), losses := [] }

theorem u29171 : Upper (D 7) (R 7) [96,260,129,34,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29171 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29172 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 133 42 82 48 201 137 393), lower := (rows 97 262 133 42 82 48 64 128 256), losses := [] }

theorem u29172 : Upper (D 7) (R 7) [96,260,129,34,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29172 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29173 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 81, targets := 128 }], pairs := [(0,7),(3,0),(3,6),(4,7)], upper := (rows 97 262 133 42 82 160 89 153 281), lower := (rows 97 262 133 42 82 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 164 64 128 256), good := (rows 96 302 164 42 90 160 64 160 256) },{ target := 6, region := (rows 1 2 4 10 16 164 0 128 256), good := (rows 33 302 165 42 26 160 0 160 256) }] }

theorem u29173 : Upper (D 7) (R 7) [96,260,129,34,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29174 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 262 133 42 88 33 210 146 402), lower := (rows 97 262 133 42 88 33 64 128 256), losses := [] }

theorem u29174 : Upper (D 7) (R 7) [96,260,129,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29175 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 262 133 42 88 34 209 145 401), lower := (rows 97 262 133 42 88 34 64 128 256), losses := [] }

theorem u29175 : Upper (D 7) (R 7) [96,260,129,34,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29176 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 133 42 88 48 195 131 387), lower := (rows 97 262 133 42 88 48 64 128 256), losses := [] }

theorem u29176 : Upper (D 7) (R 7) [96,260,129,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29176 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29177 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 81, targets := 128 }], pairs := [(0,7),(3,0),(3,6),(4,7)], upper := (rows 97 262 133 42 88 160 83 147 275), lower := (rows 97 262 133 42 88 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 164 64 128 256), good := (rows 96 302 164 42 88 160 64 160 256) },{ target := 6, region := (rows 1 2 4 10 16 164 0 128 256), good := (rows 33 302 165 42 24 160 0 160 256) }] }

theorem u29177 : Upper (D 7) (R 7) [96,260,129,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29178 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(3,7),(4,0),(4,5)], upper := (rows 97 262 133 42 146 33 88 216 344), lower := (rows 97 262 133 42 146 33 64 128 256), losses := [] }

theorem u29178 : Upper (D 7) (R 7) [96,260,129,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29179 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 133 42 146 40 81 209 337), lower := (rows 97 262 133 42 146 40 64 128 256), losses := [] }

theorem u29179 : Upper (D 7) (R 7) [96,260,129,34,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29179 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29180 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 197, targets := 2 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,1),(2,1),(3,0)], upper := (rows 97 262 133 42 146 48 73 201 329), lower := (rows 97 262 133 42 146 48 64 128 256), losses := [] }

theorem u29180 : Upper (D 7) (R 7) [96,260,129,34,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29180 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29181 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 42 146 96 89 153 281), lower := (rows 97 262 133 42 146 96 64 128 256), losses := [] }

theorem u29181 : Upper (D 7) (R 7) [96,260,129,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29182 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 262 133 42 152 33 82 210 338), lower := (rows 97 262 133 42 152 33 64 128 256), losses := [] }

theorem u29182 : Upper (D 7) (R 7) [96,260,129,34,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29183 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 262 133 42 152 34 81 209 337), lower := (rows 97 262 133 42 152 34 64 128 256), losses := [] }

theorem u29183 : Upper (D 7) (R 7) [96,260,129,34,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29184 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 2, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 97 262 133 42 152 48 67 195 323), lower := (rows 97 262 133 42 152 48 64 128 256), losses := [] }

theorem u29184 : Upper (D 7) (R 7) [96,260,129,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29184 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29185 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 42 152 96 83 147 275), lower := (rows 97 262 133 42 152 96 64 128 256), losses := [] }

theorem u29185 : Upper (D 7) (R 7) [96,260,129,34,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29186 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,5)], upper := (rows 97 262 133 42 208 33 90 154 282), lower := (rows 97 262 133 42 208 33 64 128 256), losses := [] }

theorem u29186 : Upper (D 7) (R 7) [96,260,129,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29187 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 262 133 42 208 34 89 153 281), lower := (rows 97 262 133 42 208 34 64 128 256), losses := [] }

theorem u29187 : Upper (D 7) (R 7) [96,260,129,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29188 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 133 42 208 40 83 147 275), lower := (rows 97 262 133 42 208 40 64 128 256), losses := [] }

theorem u29188 : Upper (D 7) (R 7) [96,260,129,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29188 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29189 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 133 42 208 48 75 139 267), lower := (rows 97 262 133 42 208 48 64 128 256), losses := [] }

theorem u29189 : Upper (D 7) (R 7) [96,260,129,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29189 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29190 : Route 9 := (fun mask => (mask,id))

def c29190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29190 : Upper (D 7) (R 7) [96,260,129,48,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,129,48,130,1] 13 (by decide) (choices 1) [2,8] r29190 c29190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11115
  · exact u11116

def b29191 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 197, targets := 2 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,1),(2,1),(3,0),(3,6)], upper := (rows 97 262 133 56 146 34 73 201 329), lower := (rows 97 262 133 56 146 34 64 128 256), losses := [] }

theorem u29191 : Upper (D 7) (R 7) [96,260,129,48,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29192 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 133 56 146 40 67 195 323), lower := (rows 97 262 133 56 146 40 64 128 256), losses := [] }

theorem u29192 : Upper (D 7) (R 7) [96,260,129,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29192 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29193 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 56 146 96 75 139 267), lower := (rows 97 262 133 56 146 96 64 128 256), losses := [] }

theorem u29193 : Upper (D 7) (R 7) [96,260,129,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29194 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 262 133 56 208 33 74 138 266), lower := (rows 97 262 133 56 208 33 64 128 256), losses := [] }

theorem u29194 : Upper (D 7) (R 7) [96,260,129,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29195 : Route 9 := (fun mask => (mask,id))

def c29195 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29195 : Upper (D 7) (R 7) [96,260,129,48,192,2] 13 := by
  apply FastRouting.sound _ _ [96,260,129,48,192,2] 13 (by decide) (choices 1) [1,2,8] r29195 c29195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11117
  · exact u11118
  · exact u11119

def b29196 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 133 56 208 40 67 131 259), lower := (rows 97 262 133 56 208 40 64 128 256), losses := [] }

theorem u29196 : Upper (D 7) (R 7) [96,260,129,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29196 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29197 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 97 262 134 11 56 33 208 208 464), lower := (rows 97 262 134 11 56 33 64 128 256), losses := [] }

theorem u29197 : Upper (D 7) (R 7) [96,260,130,3,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29198 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 134 11 56 48 193 193 449), lower := (rows 97 262 134 11 56 48 64 128 256), losses := [] }

theorem u29198 : Upper (D 7) (R 7) [96,260,130,3,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29198 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29199 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 11 56 96 209 145 401), lower := (rows 97 262 134 11 56 96 64 128 256), losses := [] }

theorem u29199 : Upper (D 7) (R 7) [96,260,130,3,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29200 : Route 9 := (fun mask => (mask,id))

def c29200 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29200 : Upper (D 7) (R 7) [96,260,130,3,40,128] 13 := by
  apply FastRouting.sound _ _ [96,260,130,3,40,128] 13 (by decide) (choices 1) [1,16] r29200 c29200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11120
  · exact u11121

def r29201 : Route 9 := (fun mask => (mask,id))

def c29201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29201 : Upper (D 7) (R 7) [96,260,130,3,129,8] 13 := by
  apply FastRouting.sound _ _ [96,260,130,3,129,8] 13 (by decide) (choices 1) [16,32] r29201 c29201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11122
  · exact u11123

theorem m29202_8 : Upper (D 7) (R 7) [96,260,130,3,129,16,8] 13 :=
  permutation_upper _ _ _ [96,260,130,3,129,8,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11122

def r29202 : Route 9 := (fun mask => (mask,id))

def c29202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29202 : Upper (D 7) (R 7) [96,260,130,3,129,16] 13 := by
  apply FastRouting.sound _ _ [96,260,130,3,129,16] 13 (by decide) (choices 1) [8,32] r29202 c29202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m29202_8
  · exact u11124

def b29203 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 11 145 96 120 184 312), lower := (rows 97 262 134 11 145 96 64 128 256), losses := [] }

theorem u29203 : Upper (D 7) (R 7) [96,260,130,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29204 : Route 9 := (fun mask => (mask,id))

def c29204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29204 : Upper (D 7) (R 7) [96,260,130,3,136,1] 13 := by
  apply FastRouting.sound _ _ [96,260,130,3,136,1] 13 (by decide) (choices 1) [16,32] r29204 c29204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11125
  · exact u11126

def b29205 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 241, targets := 2 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 262 134 11 152 48 97 225 353), lower := (rows 97 262 134 11 152 48 64 128 256), losses := [] }

theorem u29205 : Upper (D 7) (R 7) [96,260,130,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29205 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29206 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 11 152 96 113 177 305), lower := (rows 97 262 134 11 152 96 64 128 256), losses := [] }

theorem u29206 : Upper (D 7) (R 7) [96,260,130,3,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29207 : Route 9 := (fun mask => (mask,id))

def c29207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29207 : Upper (D 7) (R 7) [96,260,130,3,160,1] 13 := by
  apply FastRouting.sound _ _ [96,260,130,3,160,1] 13 (by decide) (choices 1) [8,16] r29207 c29207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11127
  · exact u11128

def b29208 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 241, targets := 2 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 262 134 11 176 40 81 209 337), lower := (rows 97 262 134 11 176 40 64 128 256), losses := [] }

theorem u29208 : Upper (D 7) (R 7) [96,260,130,3,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29208 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29209 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 134 11 176 48 73 201 329), lower := (rows 97 262 134 11 176 48 64 128 256), losses := [] }

theorem u29209 : Upper (D 7) (R 7) [96,260,130,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29209 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29210 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 11 176 96 89 153 281), lower := (rows 97 262 134 11 176 96 64 128 256), losses := [] }

theorem u29210 : Upper (D 7) (R 7) [96,260,130,3,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29211 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 4, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(2,0),(3,1)], upper := (rows 97 262 134 25 26 33 224 224 480), lower := (rows 97 262 134 25 26 33 64 128 256), losses := [] }

theorem u29211 : Upper (D 7) (R 7) [96,260,130,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29212 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 25 26 96 225 161 417), lower := (rows 97 262 134 25 26 96 64 128 256), losses := [] }

theorem u29212 : Upper (D 7) (R 7) [96,260,130,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m29213_1 : Upper (D 7) (R 7) [96,260,130,17,10,128,1] 13 :=
  permutation_upper _ _ _ [96,260,130,17,10,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11129

theorem m29213_32 : Upper (D 7) (R 7) [96,260,130,17,10,128,32] 13 :=
  permutation_upper _ _ _ [96,260,130,17,10,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11130

def r29213 : Route 9 := (fun mask => (mask,id))

def c29213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29213 : Upper (D 7) (R 7) [96,260,130,17,10,128] 13 := by
  apply FastRouting.sound _ _ [96,260,130,17,10,128] 13 (by decide) (choices 1) [1,32] r29213 c29213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m29213_1
  · exact m29213_32

def b29214 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 97 262 134 25 152 33 98 226 354), lower := (rows 97 262 134 25 152 33 64 128 256), losses := [] }

theorem u29214 : Upper (D 7) (R 7) [96,260,130,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29215 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 97 262 134 25 152 34 97 225 353), lower := (rows 97 262 134 25 152 34 64 128 256), losses := [] }

theorem u29215 : Upper (D 7) (R 7) [96,260,130,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29216 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 25 152 96 99 163 291), lower := (rows 97 262 134 25 152 96 64 128 256), losses := [] }

theorem u29216 : Upper (D 7) (R 7) [96,260,130,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29217 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 97 262 134 25 176 33 74 202 330), lower := (rows 97 262 134 25 176 33 64 128 256), losses := [] }

theorem u29217 : Upper (D 7) (R 7) [96,260,130,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29218 : PairBound 9 := { available := 73, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 2, region := 48, targets := 1 }], pairs := [(0,1),(3,1),(4,0),(4,1)], upper := (rows 97 262 134 25 176 34 73 201 329), lower := (rows 97 262 134 25 176 34 64 128 256), losses := [] }

theorem u29218 : Upper (D 7) (R 7) [96,260,130,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29219 : Route 9 := (fun mask => (mask,id))

def c29219 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29219 : Upper (D 7) (R 7) [96,260,130,17,160,8] 13 := by
  apply FastRouting.sound _ _ [96,260,130,17,160,8] 13 (by decide) (choices 1) [1,2] r29219 c29219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11131
  · exact u11132

#print axioms u29219
end Delivery.IrregularNine14.P07
