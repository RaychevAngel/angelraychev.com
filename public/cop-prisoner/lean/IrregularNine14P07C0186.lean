import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0013
import IrregularNine14P07C0014

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11160 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 262 140 42 145 33 80 194 322), lower := (rows 97 262 140 42 145 33 80 128 256), losses := [] }

theorem u11160 : Upper (D 7) (R 7) [96,260,136,34,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11160 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11161 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 262 140 42 145 48 65 194 322), lower := (rows 97 262 140 42 145 48 65 128 256), losses := [] }

theorem u11161 : Upper (D 7) (R 7) [96,260,136,34,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11161 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11162 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 177, targets := 2 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,1),(4,1),(4,5)], upper := (rows 97 262 140 42 145 48 66 193 321), lower := (rows 97 262 140 42 145 48 66 128 256), losses := [] }

theorem u11162 : Upper (D 7) (R 7) [96,260,136,34,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11162 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11163 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 140 42 146 33 65 208 336), lower := (rows 97 262 140 42 146 33 65 128 256), losses := [] }

theorem u11163 : Upper (D 7) (R 7) [96,260,136,34,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11164 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 105, targets := 128 },{ cop := 4, region := 97, targets := 2 }], pairs := [(0,1),(0,7),(3,7)], upper := (rows 97 262 140 42 146 33 80 193 321), lower := (rows 97 262 140 42 146 33 80 128 256), losses := [] }

theorem u11164 : Upper (D 7) (R 7) [96,260,136,34,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11164 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11165 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 140 42 208 33 65 146 274), lower := (rows 97 262 140 42 208 33 65 128 256), losses := [] }

theorem u11165 : Upper (D 7) (R 7) [96,260,136,34,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11166 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 105, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,1)], upper := (rows 97 262 140 42 208 33 66 145 273), lower := (rows 97 262 140 42 208 33 66 128 256), losses := [] }

theorem u11166 : Upper (D 7) (R 7) [96,260,136,34,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11167 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 140 42 208 33 80 131 259), lower := (rows 97 262 140 42 208 33 80 128 256), losses := [] }

theorem u11167 : Upper (D 7) (R 7) [96,260,136,34,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11167 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11168 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(1,7),(4,7)], upper := (rows 97 262 140 56 82 160 65 131 259), lower := (rows 97 262 140 56 82 160 65 128 256), losses := [{ target := 7, region := (rows 41 6 4 8 22 32 109 0 260), good := (rows 97 342 351 121 82 97 65 0 256) }] }

theorem u11168 : Upper (D 7) (R 7) [96,260,136,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11169 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 80, targets := 161 },{ cop := 4, region := 161, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 97 262 140 56 82 160 66 129 257), lower := (rows 97 262 140 56 82 160 66 128 256), losses := [] }

theorem u11169 : Upper (D 7) (R 7) [96,260,136,48,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11170 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 262 140 56 145 34 65 194 322), lower := (rows 97 262 140 56 145 34 65 128 256), losses := [{ target := 1, region := (rows 41 0 4 8 20 32 125 128 256), good := (rows 97 340 221 121 209 97 65 128 256) }] }

theorem u11170 : Upper (D 7) (R 7) [96,260,136,48,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11171 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 262 140 56 145 34 66 193 321), lower := (rows 97 262 140 56 145 34 66 128 256), losses := [] }

theorem u11171 : Upper (D 7) (R 7) [96,260,136,48,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11172 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 262 140 56 208 34 65 131 259), lower := (rows 97 262 140 56 208 34 65 128 256), losses := [{ target := 1, region := (rows 41 0 4 8 20 32 109 128 256), good := (rows 97 340 221 121 208 97 65 128 256) }] }

theorem u11172 : Upper (D 7) (R 7) [96,260,136,48,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11173 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 262 140 56 208 34 66 129 257), lower := (rows 97 262 140 56 208 34 66 128 256), losses := [] }

theorem u11173 : Upper (D 7) (R 7) [96,260,136,48,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11174 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 262 164 11 88 34 65 144 400), lower := (rows 97 262 164 11 88 34 65 128 256), losses := [] }

theorem u11174 : Upper (D 7) (R 7) [96,260,160,3,72,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11175 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 164 11 88 34 80 129 385), lower := (rows 97 262 164 11 88 34 80 128 256), losses := [] }

theorem u11175 : Upper (D 7) (R 7) [96,260,160,3,72,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11175 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11176 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 208, targets := 34 },{ cop := 2, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(4,1),(4,5)], upper := (rows 97 262 164 11 88 34 192 145 273), lower := (rows 97 262 164 11 88 34 192 128 256), losses := [{ target := 7, region := (rows 17 2 4 8 16 42 64 0 272), good := (rows 97 294 36 43 377 34 64 0 256) }] }

theorem u11176 : Upper (D 7) (R 7) [96,260,160,3,72,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11177 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 148, targets := 2 },{ cop := 1, region := 105, targets := 128 }], pairs := [(0,7),(2,1),(4,1)], upper := (rows 97 262 164 11 145 34 72 208 336), lower := (rows 97 262 164 11 145 34 72 128 256), losses := [] }

theorem u11177 : Upper (D 7) (R 7) [96,260,160,3,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11177 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11178 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 81, targets := 2 },{ cop := 3, region := 208, targets := 32 }], pairs := [(0,1),(4,1),(4,5)], upper := (rows 97 262 164 11 145 34 80 200 328), lower := (rows 97 262 164 11 145 34 80 128 256), losses := [] }

theorem u11178 : Upper (D 7) (R 7) [96,260,160,3,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11178 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11179 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 148, targets := 2 },{ cop := 1, region := 105, targets := 128 }], pairs := [(0,7),(2,1),(4,1)], upper := (rows 97 262 164 11 145 40 66 208 336), lower := (rows 97 262 164 11 145 40 66 128 256), losses := [] }

theorem u11179 : Upper (D 7) (R 7) [96,260,160,3,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11179 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11180 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 390, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 97 262 164 11 145 40 80 194 322), lower := (rows 97 262 164 11 145 40 80 128 256), losses := [] }

theorem u11180 : Upper (D 7) (R 7) [96,260,160,3,129,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11180 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11181 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 105, targets := 128 },{ cop := 2, region := 81, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,1)], upper := (rows 97 262 164 11 208 34 65 152 280), lower := (rows 97 262 164 11 208 34 65 128 256), losses := [] }

theorem u11181 : Upper (D 7) (R 7) [96,260,160,3,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11182 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 148, targets := 2 },{ cop := 1, region := 105, targets := 128 }], pairs := [(0,7),(2,1),(4,1)], upper := (rows 97 262 164 11 208 34 72 145 273), lower := (rows 97 262 164 11 208 34 72 128 256), losses := [] }

theorem u11182 : Upper (D 7) (R 7) [96,260,160,3,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11182 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11183 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 164 11 208 34 80 137 265), lower := (rows 97 262 164 11 208 34 80 128 256), losses := [] }

theorem u11183 : Upper (D 7) (R 7) [96,260,160,3,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11183 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11184 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 262 164 11 208 40 65 146 274), lower := (rows 97 262 164 11 208 40 65 128 256), losses := [] }

theorem u11184 : Upper (D 7) (R 7) [96,260,160,3,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11184 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11185 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 148, targets := 2 },{ cop := 1, region := 105, targets := 128 }], pairs := [(0,7),(2,1),(4,1)], upper := (rows 97 262 164 11 208 40 66 145 273), lower := (rows 97 262 164 11 208 40 66 128 256), losses := [] }

theorem u11185 : Upper (D 7) (R 7) [96,260,160,3,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11185 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11186 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 262 164 11 208 40 80 131 259), lower := (rows 97 262 164 11 208 40 80 128 256), losses := [] }

theorem u11186 : Upper (D 7) (R 7) [96,260,160,3,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11186 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11187 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 121, targets := 128 },{ cop := 0, region := 390, targets := 1 }], pairs := [(0,7),(1,0),(3,7),(4,7)], upper := (rows 97 262 164 25 26 34 65 192 448), lower := (rows 97 262 164 25 26 34 65 128 256), losses := [] }

theorem u11187 : Upper (D 7) (R 7) [96,260,160,17,10,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11188 : Route 9 := (fun mask => (mask,id))

def c11188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11188 : Upper (D 7) (R 7) [96,260,160,17,10,2,128] 13 := by
  apply FastRouting.sound _ _ [96,260,160,17,10,2,128] 13 (by decide) (choices 1) [1,64] r11188 c11188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u837
  · exact u838

def r11189 : Route 9 := (fun mask => (mask,id))

def c11189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11189 : Upper (D 7) (R 7) [96,260,160,17,130,1,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,17,130,1,2] 13 (by decide) (choices 1) [8,64] r11189 c11189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u839
  · exact u840

def b11190 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 262 164 25 146 33 72 194 322), lower := (rows 97 262 164 25 146 33 72 128 256), losses := [] }

theorem u11190 : Upper (D 7) (R 7) [96,260,160,17,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11190 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11191 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 89, targets := 2 },{ cop := 0, region := 390, targets := 1 }], pairs := [(0,1),(1,0),(3,1),(4,1)], upper := (rows 97 262 164 25 152 34 65 194 322), lower := (rows 97 262 164 25 152 34 65 128 256), losses := [] }

theorem u11191 : Upper (D 7) (R 7) [96,260,160,17,136,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11192 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 97 262 164 25 152 34 66 193 321), lower := (rows 97 262 164 25 152 34 66 128 256), losses := [] }

theorem u11192 : Upper (D 7) (R 7) [96,260,160,17,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11193 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 262 164 25 208 34 65 138 266), lower := (rows 97 262 164 25 208 34 65 128 256), losses := [] }

theorem u11193 : Upper (D 7) (R 7) [96,260,160,17,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11194 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 97 262 164 25 208 34 66 137 265), lower := (rows 97 262 164 25 208 34 66 128 256), losses := [] }

theorem u11194 : Upper (D 7) (R 7) [96,260,160,17,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11195 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 262 164 25 208 34 72 131 259), lower := (rows 97 262 164 25 208 34 72 128 256), losses := [] }

theorem u11195 : Upper (D 7) (R 7) [96,260,160,17,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11195 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11196 : Route 9 := (fun mask => (mask,id))

def c11196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11196 : Upper (D 7) (R 7) [96,260,160,18,129,2,1] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18,129,2,1] 13 (by decide) (choices 1) [8,64] r11196 c11196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u841
  · exact u842

def b11197 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 148, targets := 2 },{ cop := 0, region := 144, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 97 262 164 26 145 34 72 193 321), lower := (rows 97 262 164 26 145 34 72 128 256), losses := [] }

theorem u11197 : Upper (D 7) (R 7) [96,260,160,18,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11197 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11198 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 2, region := 65, targets := 2 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 97 262 164 26 145 40 65 194 322), lower := (rows 97 262 164 26 145 40 65 128 256), losses := [] }

theorem u11198 : Upper (D 7) (R 7) [96,260,160,18,129,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11198 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11199 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 148, targets := 2 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(2,1),(4,1)], upper := (rows 97 262 164 26 145 40 66 193 321), lower := (rows 97 262 164 26 145 40 66 128 256), losses := [] }

theorem u11199 : Upper (D 7) (R 7) [96,260,160,18,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11199 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11200 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 164 26 152 33 65 194 322), lower := (rows 97 262 164 26 152 33 65 128 256), losses := [] }

theorem u11200 : Upper (D 7) (R 7) [96,260,160,18,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11201 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 6, region := 165, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,1)], upper := (rows 97 262 164 26 152 33 66 193 321), lower := (rows 97 262 164 26 152 33 66 128 256), losses := [] }

theorem u11201 : Upper (D 7) (R 7) [96,260,160,18,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11202 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 164 26 208 33 65 138 266), lower := (rows 97 262 164 26 208 33 65 128 256), losses := [] }

theorem u11202 : Upper (D 7) (R 7) [96,260,160,18,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11203 : Route 9 := (fun mask => (mask,id))

def c11203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11203 : Upper (D 7) (R 7) [96,260,160,18,192,1,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18,192,1,2] 13 (by decide) (choices 1) [1,8] r11203 c11203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u843
  · exact u844

def b11204 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 97 262 164 26 208 33 72 131 259), lower := (rows 97 262 164 26 208 33 72 128 256), losses := [] }

theorem u11204 : Upper (D 7) (R 7) [96,260,160,18,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11204 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11205 : Route 9 := (fun mask => (mask,id))

def c11205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11205 : Upper (D 7) (R 7) [96,260,160,18,192,2,1] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18,192,2,1] 13 (by decide) (choices 1) [1,8] r11205 c11205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u845
  · exact u846

def b11206 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 148, targets := 2 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,1),(4,1)], upper := (rows 97 262 164 26 208 34 72 129 257), lower := (rows 97 262 164 26 208 34 72 128 256), losses := [] }

theorem u11206 : Upper (D 7) (R 7) [96,260,160,18,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11206 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11207 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 105, targets := 128 },{ cop := 2, region := 81, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,1)], upper := (rows 97 262 164 74 145 34 65 152 280), lower := (rows 97 262 164 74 145 34 65 128 256), losses := [] }

theorem u11207 : Upper (D 7) (R 7) [96,260,160,66,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11208 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 164 74 145 34 72 145 273), lower := (rows 97 262 164 74 145 34 72 128 256), losses := [] }

theorem u11208 : Upper (D 7) (R 7) [96,260,160,66,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11208 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11209 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 81, targets := 2 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 262 164 74 145 34 80 137 265), lower := (rows 97 262 164 74 145 34 80 128 256), losses := [] }

theorem u11209 : Upper (D 7) (R 7) [96,260,160,66,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11209 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11210 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 164 74 146 33 65 152 280), lower := (rows 97 262 164 74 146 33 65 128 256), losses := [] }

theorem u11210 : Upper (D 7) (R 7) [96,260,160,66,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11211 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 164 74 146 33 72 145 273), lower := (rows 97 262 164 74 146 33 72 128 256), losses := [] }

theorem u11211 : Upper (D 7) (R 7) [96,260,160,66,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11211 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11212 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 165, targets := 2 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,1),(2,1),(3,0)], upper := (rows 97 262 164 74 146 33 80 137 265), lower := (rows 97 262 164 74 146 33 80 128 256), losses := [] }

theorem u11212 : Upper (D 7) (R 7) [96,260,160,66,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11212 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11213 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 164 74 152 33 65 146 274), lower := (rows 97 262 164 74 152 33 65 128 256), losses := [] }

theorem u11213 : Upper (D 7) (R 7) [96,260,160,66,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11214 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 181, targets := 2 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 97 262 164 74 152 33 66 145 273), lower := (rows 97 262 164 74 152 33 66 128 256), losses := [] }

theorem u11214 : Upper (D 7) (R 7) [96,260,160,66,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11215 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 4, region := 97, targets := 2 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 97 262 164 74 152 33 80 131 259), lower := (rows 97 262 164 74 152 33 80 128 256), losses := [] }

theorem u11215 : Upper (D 7) (R 7) [96,260,160,66,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11215 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11216 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 105, targets := 128 },{ cop := 2, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(2,0),(3,7)], upper := (rows 97 262 164 74 152 34 65 145 273), lower := (rows 97 262 164 74 152 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 42 64 128 256), good := (rows 96 294 164 106 188 34 64 128 256) }] }

theorem u11216 : Upper (D 7) (R 7) [96,260,160,66,136,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11217 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 0, region := 132, targets := 2 }], pairs := [(1,6),(2,1),(2,6)], upper := (rows 97 262 164 74 152 34 80 129 257), lower := (rows 97 262 164 74 152 34 80 128 256), losses := [] }

theorem u11217 : Upper (D 7) (R 7) [96,260,160,66,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11217 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11218 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 262 164 88 145 34 65 138 266), lower := (rows 97 262 164 88 145 34 65 128 256), losses := [] }

theorem u11218 : Upper (D 7) (R 7) [96,260,160,80,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11219 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 97 262 164 88 145 34 66 137 265), lower := (rows 97 262 164 88 145 34 66 128 256), losses := [] }

theorem u11219 : Upper (D 7) (R 7) [96,260,160,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11219
end Delivery.IrregularNine14.P07
