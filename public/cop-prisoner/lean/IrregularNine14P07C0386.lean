import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0121
import IrregularNine14P07C0122

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r23160 : Route 9 := (fun mask => (mask,id))

def c23160 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23160 : Upper (D 7) (R 7) [36,72,129,144,257,64] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,257,64] 13 (by decide) (choices 1) [2,32] r23160 c23160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7291
  · exact u7292

def b23161 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 152 274 33 98 226 354), lower := (rows 37 74 133 152 274 33 64 128 256), losses := [] }

theorem u23161 : Upper (D 7) (R 7) [36,72,129,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23162 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 152 274 34 97 225 353), lower := (rows 37 74 133 152 274 34 64 128 256), losses := [{ target := 6, region := (rows 11 2 12 8 16 50 0 128 256), good := (rows 37 47 133 189 307 35 0 128 256) }] }

theorem u23162 : Upper (D 7) (R 7) [36,72,129,144,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23163 : Route 9 := (fun mask => (mask,id))

def c23163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23163 : Upper (D 7) (R 7) [36,72,129,144,258,64] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,258,64] 13 (by decide) (choices 1) [1,2,32] r23163 c23163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7293
  · exact u7294
  · exact u7295

def b23164 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 152 304 33 66 194 322), lower := (rows 37 74 133 152 304 33 64 128 256), losses := [] }

theorem u23164 : Upper (D 7) (R 7) [36,72,129,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23165 : Route 9 := (fun mask => (mask,id))

def c23165 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23165 : Upper (D 7) (R 7) [36,72,129,144,288,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,288,2] 13 (by decide) (choices 1) [1,2] r23165 c23165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7296
  · exact u7297

def r23166 : Route 9 := (fun mask => (mask,id))

def c23166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23166 : Upper (D 7) (R 7) [36,72,129,144,288,64] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,288,64] 13 (by decide) (choices 1) [1,2] r23166 c23166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7298
  · exact u7299

def b23167 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 152 336 33 98 162 290), lower := (rows 37 74 133 152 336 33 64 128 256), losses := [] }

theorem u23167 : Upper (D 7) (R 7) [36,72,129,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23168 : Route 9 := (fun mask => (mask,id))

def c23168 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23168 : Upper (D 7) (R 7) [36,72,129,144,320,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,320,2] 13 (by decide) (choices 1) [1,2,32] r23168 c23168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7300
  · exact u7301
  · exact u7302

def b23169 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 461, targets := 2 },{ cop := 1, region := 48, targets := 64 }], pairs := [(0,1),(2,1),(3,1),(4,6)], upper := (rows 37 74 133 265 50 34 208 208 464), lower := (rows 37 74 133 265 50 34 64 128 256), losses := [] }

theorem u23169 : Upper (D 7) (R 7) [36,72,129,257,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23170 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 133 265 50 48 194 194 450), lower := (rows 37 74 133 265 50 48 64 128 256), losses := [] }

theorem u23170 : Upper (D 7) (R 7) [36,72,129,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23170 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23171 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 37 74 133 265 50 96 210 146 402), lower := (rows 37 74 133 265 50 96 64 128 256), losses := [] }

theorem u23171 : Upper (D 7) (R 7) [36,72,129,257,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23172 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 265 50 160 82 210 338), lower := (rows 37 74 133 265 50 160 64 128 256), losses := [] }

theorem u23172 : Upper (D 7) (R 7) [36,72,129,257,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23173 : Route 9 := (fun mask => (mask,id))

def c23173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23173 : Upper (D 7) (R 7) [36,72,129,257,96,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,257,96,2] 13 (by decide) (choices 1) [2,16,128] r23173 c23173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7303
  · exact u7304
  · exact u7305

def b23174 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 133 265 112 48 194 130 386), lower := (rows 37 74 133 265 112 48 64 128 256), losses := [] }

theorem u23174 : Upper (D 7) (R 7) [36,72,129,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23174 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23175 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 265 112 160 82 146 274), lower := (rows 37 74 133 265 112 160 64 128 256), losses := [] }

theorem u23175 : Upper (D 7) (R 7) [36,72,129,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23176 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 74 133 265 146 34 112 240 368), lower := (rows 37 74 133 265 146 34 64 128 256), losses := [] }

theorem u23176 : Upper (D 7) (R 7) [36,72,129,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23177 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 133 265 146 48 98 226 354), lower := (rows 37 74 133 265 146 48 64 128 256), losses := [] }

theorem u23177 : Upper (D 7) (R 7) [36,72,129,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23177 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23178 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 242, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 74 133 265 146 96 114 178 306), lower := (rows 37 74 133 265 146 96 64 128 256), losses := [{ target := 1, region := (rows 17 0 20 8 16 98 64 128 256), good := (rows 37 104 133 265 181 96 96 128 256) }] }

theorem u23178 : Upper (D 7) (R 7) [36,72,129,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23179 : Route 9 := (fun mask => (mask,id))

def c23179 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23179 : Upper (D 7) (R 7) [36,72,129,257,192,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,257,192,2] 13 (by decide) (choices 1) [2,16,32] r23179 c23179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7306
  · exact u7307
  · exact u7308

def b23180 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 133 265 208 48 98 162 290), lower := (rows 37 74 133 265 208 48 64 128 256), losses := [] }

theorem u23180 : Upper (D 7) (R 7) [36,72,129,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23180 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23181 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 133 266 50 33 208 208 464), lower := (rows 37 74 133 266 50 33 64 128 256), losses := [] }

theorem u23181 : Upper (D 7) (R 7) [36,72,129,258,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23182 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 133 266 50 48 193 193 449), lower := (rows 37 74 133 266 50 48 64 128 256), losses := [] }

theorem u23182 : Upper (D 7) (R 7) [36,72,129,258,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23182 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23183 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 74 133 266 50 96 209 145 401), lower := (rows 37 74 133 266 50 96 64 128 256), losses := [] }

theorem u23183 : Upper (D 7) (R 7) [36,72,129,258,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23184 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 266 50 160 81 209 337), lower := (rows 37 74 133 266 50 160 64 128 256), losses := [] }

theorem u23184 : Upper (D 7) (R 7) [36,72,129,258,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23185 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 74 133 266 81 34 240 176 432), lower := (rows 37 74 133 266 81 34 64 128 256), losses := [] }

theorem u23185 : Upper (D 7) (R 7) [36,72,129,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23186 : Route 9 := (fun mask => (mask,id))

def c23186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u23186 : Upper (D 7) (R 7) [36,72,129,258,65,16] 13 := by
  apply FastRouting.sound _ _ [36,72,129,258,65,16] 13 (by decide) (choices 1) [2,32,128] r23186 c23186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7309
  · exact u7310
  · exact u7311

def b23187 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 266 81 160 114 178 306), lower := (rows 37 74 133 266 81 160 64 128 256), losses := [] }

theorem u23187 : Upper (D 7) (R 7) [36,72,129,258,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23188 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 133 266 112 33 210 146 402), lower := (rows 37 74 133 266 112 33 64 128 256), losses := [] }

theorem u23188 : Upper (D 7) (R 7) [36,72,129,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23189 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,1),(2,1),(4,0),(4,1)], upper := (rows 37 74 133 266 112 34 209 145 401), lower := (rows 37 74 133 266 112 34 64 128 256), losses := [] }

theorem u23189 : Upper (D 7) (R 7) [36,72,129,258,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23190 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 133 266 112 48 195 131 387), lower := (rows 37 74 133 266 112 48 64 128 256), losses := [] }

theorem u23190 : Upper (D 7) (R 7) [36,72,129,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23190 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23191 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 266 112 160 83 147 275), lower := (rows 37 74 133 266 112 160 64 128 256), losses := [] }

theorem u23191 : Upper (D 7) (R 7) [36,72,129,258,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23192 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 266 146 33 112 240 368), lower := (rows 37 74 133 266 146 33 64 128 256), losses := [] }

theorem u23192 : Upper (D 7) (R 7) [36,72,129,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23193 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 74 133 266 146 48 97 225 353), lower := (rows 37 74 133 266 146 48 64 128 256), losses := [] }

theorem u23193 : Upper (D 7) (R 7) [36,72,129,258,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23193 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23194 : Route 9 := (fun mask => (mask,id))

def c23194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23194 : Upper (D 7) (R 7) [36,72,129,258,130,64] 13 := by
  apply FastRouting.sound _ _ [36,72,129,258,130,64] 13 (by decide) (choices 1) [1,16,32] r23194 c23194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7312
  · exact u7313
  · exact u7314

def b23195 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 266 208 33 114 178 306), lower := (rows 37 74 133 266 208 33 64 128 256), losses := [] }

theorem u23195 : Upper (D 7) (R 7) [36,72,129,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23196 : Route 9 := (fun mask => (mask,id))

def c23196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23196 : Upper (D 7) (R 7) [36,72,129,258,192,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,258,192,2] 13 (by decide) (choices 1) [1,16,32] r23196 c23196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7315
  · exact u7316
  · exact u7317

def b23197 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 133 266 208 48 99 163 291), lower := (rows 37 74 133 266 208 48 64 128 256), losses := [] }

theorem u23197 : Upper (D 7) (R 7) [36,72,129,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23197 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23198 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 133 280 19 34 224 224 480), lower := (rows 37 74 133 280 19 34 64 128 256), losses := [] }

theorem u23198 : Upper (D 7) (R 7) [36,72,129,272,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23199 : Route 9 := (fun mask => (mask,id))

def c23199 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u23199 : Upper (D 7) (R 7) [36,72,129,272,3,64] 13 := by
  apply FastRouting.sound _ _ [36,72,129,272,3,64] 13 (by decide) (choices 1) [2,32,128] r23199 c23199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7318
  · exact u7319
  · exact u7320

def b23200 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 280 19 160 98 226 354), lower := (rows 37 74 133 280 19 160 64 128 256), losses := [] }

theorem u23200 : Upper (D 7) (R 7) [36,72,129,272,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23201 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 133 280 50 33 194 194 450), lower := (rows 37 74 133 280 50 33 64 128 256), losses := [] }

theorem u23201 : Upper (D 7) (R 7) [36,72,129,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23202 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 74 133 280 50 34 193 193 449), lower := (rows 37 74 133 280 50 34 64 128 256), losses := [] }

theorem u23202 : Upper (D 7) (R 7) [36,72,129,272,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23203 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 74 133 280 50 96 195 131 387), lower := (rows 37 74 133 280 50 96 64 128 256), losses := [] }

theorem u23203 : Upper (D 7) (R 7) [36,72,129,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23204 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 280 50 160 67 195 323), lower := (rows 37 74 133 280 50 160 64 128 256), losses := [] }

theorem u23204 : Upper (D 7) (R 7) [36,72,129,272,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23205 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 133 280 112 33 194 130 386), lower := (rows 37 74 133 280 112 33 64 128 256), losses := [] }

theorem u23205 : Upper (D 7) (R 7) [36,72,129,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23206 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 48, targets := 129 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(4,0),(4,7)], upper := (rows 37 74 133 280 112 34 195 131 387), lower := (rows 37 74 133 280 112 34 64 128 256), losses := [] }

theorem u23206 : Upper (D 7) (R 7) [36,72,129,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23207 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 280 112 160 67 131 259), lower := (rows 37 74 133 280 112 160 64 128 256), losses := [] }

theorem u23207 : Upper (D 7) (R 7) [36,72,129,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23208 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 280 146 33 98 226 354), lower := (rows 37 74 133 280 146 33 64 128 256), losses := [] }

theorem u23208 : Upper (D 7) (R 7) [36,72,129,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23209 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 37, targets := 64 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 280 146 34 97 225 353), lower := (rows 37 74 133 280 146 34 64 128 256), losses := [] }

theorem u23209 : Upper (D 7) (R 7) [36,72,129,272,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23210 : Route 9 := (fun mask => (mask,id))

def c23210 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23210 : Upper (D 7) (R 7) [36,72,129,272,130,64] 13 := by
  apply FastRouting.sound _ _ [36,72,129,272,130,64] 13 (by decide) (choices 1) [1,2,32] r23210 c23210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7321
  · exact u7322
  · exact u7323

def b23211 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 280 208 33 98 162 290), lower := (rows 37 74 133 280 208 33 64 128 256), losses := [] }

theorem u23211 : Upper (D 7) (R 7) [36,72,129,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23212 : Route 9 := (fun mask => (mask,id))

def c23212 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23212 : Upper (D 7) (R 7) [36,72,129,272,192,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,272,192,2] 13 (by decide) (choices 1) [1,2,32] r23212 c23212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7324
  · exact u7325
  · exact u7326

def b23213 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 196, targets := 34 }], pairs := [(1,0),(2,1),(2,5),(3,0)], upper := (rows 37 74 133 296 19 34 208 208 464), lower := (rows 37 74 133 296 19 34 64 128 256), losses := [] }

theorem u23213 : Upper (D 7) (R 7) [36,72,129,288,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23214 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 133 296 19 48 194 194 450), lower := (rows 37 74 133 296 19 48 64 128 256), losses := [] }

theorem u23214 : Upper (D 7) (R 7) [36,72,129,288,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23214 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23215 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 132, targets := 32 },{ cop := 4, region := 132, targets := 64 }], pairs := [(1,0),(2,5),(2,6),(3,0)], upper := (rows 37 74 133 296 19 96 210 146 402), lower := (rows 37 74 133 296 19 96 64 128 256), losses := [] }

theorem u23215 : Upper (D 7) (R 7) [36,72,129,288,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23216 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 296 19 160 82 210 338), lower := (rows 37 74 133 296 19 160 64 128 256), losses := [] }

theorem u23216 : Upper (D 7) (R 7) [36,72,129,288,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23217 : Route 9 := (fun mask => (mask,id))

def c23217 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23217 : Upper (D 7) (R 7) [36,72,129,288,65,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,288,65,2] 13 (by decide) (choices 1) [2,16,128] r23217 c23217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7327
  · exact u7328
  · exact u7329

def b23218 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 133 296 81 48 194 130 386), lower := (rows 37 74 133 296 81 48 64 128 256), losses := [] }

theorem u23218 : Upper (D 7) (R 7) [36,72,129,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23218 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23219 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 296 81 160 82 146 274), lower := (rows 37 74 133 296 81 160 64 128 256), losses := [] }

theorem u23219 : Upper (D 7) (R 7) [36,72,129,288,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u23219
end Delivery.IrregularNine14.P07
