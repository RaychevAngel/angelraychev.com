import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0055
import IrregularNine14P08C0056

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11160 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 268 81 176 240 176 432), lower := (rows 67 131 44 268 81 32 64 128 256), losses := [] }

theorem u11160 : Upper (D 8) (R 8) [66,129,40,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11161 : Route 9 := (fun mask => (mask,id))

def c11161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11161 : Upper (D 8) (R 8) [66,129,40,260,96] 13 := by
  apply FastRouting.sound _ _ [66,129,40,260,96] 13 (by decide) (choices 1) [1,16,128] r11161 c11161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3321
  · exact u3322
  · exact u3323

def b11162 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 131 44 268 145 112 112 240 368), lower := (rows 67 131 44 268 145 32 64 128 256), losses := [] }

theorem u11162 : Upper (D 8) (R 8) [66,129,40,260,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11163 : Route 9 := (fun mask => (mask,id))

def c11163 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11163 : Upper (D 8) (R 8) [66,129,40,260,160] 13 := by
  apply FastRouting.sound _ _ [66,129,40,260,160] 13 (by decide) (choices 1) [1,16,64] r11163 c11163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3324
  · exact u3325
  · exact u3326

def b11164 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 131 44 268 208 49 113 177 305), lower := (rows 67 131 44 268 208 32 64 128 256), losses := [] }

theorem u11164 : Upper (D 8) (R 8) [66,129,40,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11165 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 280 81 164 228 164 420), lower := (rows 67 131 44 280 81 32 64 128 256), losses := [] }

theorem u11165 : Upper (D 8) (R 8) [66,129,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11166 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 280 84 161 225 161 417), lower := (rows 67 131 44 280 84 32 64 128 256), losses := [] }

theorem u11166 : Upper (D 8) (R 8) [66,129,40,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11167 : Route 9 := (fun mask => (mask,id))

def c11167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11167 : Upper (D 8) (R 8) [66,129,40,272,96] 13 := by
  apply FastRouting.sound _ _ [66,129,40,272,96] 13 (by decide) (choices 1) [1,4,128] r11167 c11167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3327
  · exact u3328
  · exact u3329

def b11168 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 131 44 280 145 100 100 228 356), lower := (rows 67 131 44 280 145 32 64 128 256), losses := [] }

theorem u11168 : Upper (D 8) (R 8) [66,129,40,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11169 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 44 280 148 97 97 225 353), lower := (rows 67 131 44 280 148 32 64 128 256), losses := [] }

theorem u11169 : Upper (D 8) (R 8) [66,129,40,272,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11170 : Route 9 := (fun mask => (mask,id))

def c11170 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11170 : Upper (D 8) (R 8) [66,129,40,272,160] 13 := by
  apply FastRouting.sound _ _ [66,129,40,272,160] 13 (by decide) (choices 1) [1,4,64] r11170 c11170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3330
  · exact u3331
  · exact u3332

def b11171 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 131 44 280 208 37 101 165 293), lower := (rows 67 131 44 280 208 32 64 128 256), losses := [] }

theorem u11171 : Upper (D 8) (R 8) [66,129,40,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11172 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 296 84 177 241 177 433), lower := (rows 67 131 44 296 84 32 64 128 256), losses := [] }

theorem u11172 : Upper (D 8) (R 8) [66,129,40,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11173 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 296 112 181 213 149 405), lower := (rows 67 131 44 296 112 32 64 128 256), losses := [] }

theorem u11173 : Upper (D 8) (R 8) [66,129,40,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11173 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11174 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 296 148 113 113 241 369), lower := (rows 67 131 44 296 148 32 64 128 256), losses := [] }

theorem u11174 : Upper (D 8) (R 8) [66,129,40,288,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11175 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 296 176 117 85 213 341), lower := (rows 67 131 44 296 176 32 64 128 256), losses := [] }

theorem u11175 : Upper (D 8) (R 8) [66,129,40,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11176 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 131 44 328 145 52 116 180 308), lower := (rows 67 131 44 328 145 32 64 128 256), losses := [] }

theorem u11176 : Upper (D 8) (R 8) [66,129,40,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11177 : Route 9 := (fun mask => (mask,id))

def c11177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11177 : Upper (D 8) (R 8) [66,129,40,320,132] 13 := by
  apply FastRouting.sound _ _ [66,129,40,320,132] 13 (by decide) (choices 1) [1,16] r11177 c11177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3333
  · exact u3334

def r11178 : Route 9 := (fun mask => (mask,id))

def c11178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11178 : Upper (D 8) (R 8) [66,129,40,320,160] 13 := by
  apply FastRouting.sound _ _ [66,129,40,320,160] 13 (by decide) (choices 1) [1,4,16] r11178 c11178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3335
  · exact u3336
  · exact u3337

def b11179 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 44 392 81 52 116 180 308), lower := (rows 67 131 44 392 81 32 64 128 256), losses := [] }

theorem u11179 : Upper (D 8) (R 8) [66,129,40,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11180 : Route 9 := (fun mask => (mask,id))

def c11180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11180 : Upper (D 8) (R 8) [66,129,40,384,68] 13 := by
  apply FastRouting.sound _ _ [66,129,40,384,68] 13 (by decide) (choices 1) [1,16] r11180 c11180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3338
  · exact u3339

def r11181 : Route 9 := (fun mask => (mask,id))

def c11181 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11181 : Upper (D 8) (R 8) [66,129,40,384,96] 13 := by
  apply FastRouting.sound _ _ [66,129,40,384,96] 13 (by decide) (choices 1) [1,4,16] r11181 c11181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3340
  · exact u3341
  · exact u3342

def b11182 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 69 140 280 48 112 176 304), lower := (rows 67 131 69 140 280 32 64 128 256), losses := [] }

theorem u11182 : Upper (D 8) (R 8) [66,129,65,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11183 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 69 140 304 56 120 184 312), lower := (rows 67 131 69 140 304 32 64 128 256), losses := [] }

theorem u11183 : Upper (D 8) (R 8) [66,129,65,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11184 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 69 152 276 40 104 168 296), lower := (rows 67 131 69 152 276 32 64 128 256), losses := [] }

theorem u11184 : Upper (D 8) (R 8) [66,129,65,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11185 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 69 152 304 44 108 172 300), lower := (rows 67 131 69 152 304 32 64 128 256), losses := [] }

theorem u11185 : Upper (D 8) (R 8) [66,129,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11186 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 69 168 276 56 120 184 312), lower := (rows 67 131 69 168 276 32 64 128 256), losses := [] }

theorem u11186 : Upper (D 8) (R 8) [66,129,65,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11187 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 69 168 280 52 116 180 308), lower := (rows 67 131 69 168 280 32 64 128 256), losses := [] }

theorem u11187 : Upper (D 8) (R 8) [66,129,65,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11188 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 69 168 304 60 124 188 316), lower := (rows 67 131 69 168 304 32 64 128 256), losses := [] }

theorem u11188 : Upper (D 8) (R 8) [66,129,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11189 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 76 137 276 48 112 176 304), lower := (rows 67 131 76 137 276 32 64 128 256), losses := [] }

theorem u11189 : Upper (D 8) (R 8) [66,129,72,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11190 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 76 137 304 52 116 180 308), lower := (rows 67 131 76 137 304 32 64 128 256), losses := [] }

theorem u11190 : Upper (D 8) (R 8) [66,129,72,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11191 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 76 140 304 49 113 177 305), lower := (rows 67 131 76 140 304 32 64 128 256), losses := [] }

theorem u11191 : Upper (D 8) (R 8) [66,129,72,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11192 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 76 152 273 36 100 164 292), lower := (rows 67 131 76 152 273 32 64 128 256), losses := [] }

theorem u11192 : Upper (D 8) (R 8) [66,129,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11193 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 76 152 276 33 97 161 289), lower := (rows 67 131 76 152 276 32 64 128 256), losses := [] }

theorem u11193 : Upper (D 8) (R 8) [66,129,72,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11194 : Route 9 := (fun mask => (mask,id))

def c11194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11194 : Upper (D 8) (R 8) [66,129,72,144,288] 13 := by
  apply FastRouting.sound _ _ [66,129,72,144,288] 13 (by decide) (choices 1) [1,4] r11194 c11194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3343
  · exact u3344

def b11195 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 76 168 273 52 116 180 308), lower := (rows 67 131 76 168 273 32 64 128 256), losses := [] }

theorem u11195 : Upper (D 8) (R 8) [66,129,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11196 : Route 9 := (fun mask => (mask,id))

def c11196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11196 : Upper (D 8) (R 8) [66,129,72,160,260] 13 := by
  apply FastRouting.sound _ _ [66,129,72,160,260] 13 (by decide) (choices 1) [1,16] r11196 c11196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3345
  · exact u3346

def r11197 : Route 9 := (fun mask => (mask,id))

def c11197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11197 : Upper (D 8) (R 8) [66,129,72,160,288] 13 := by
  apply FastRouting.sound _ _ [66,129,72,160,288] 13 (by decide) (choices 1) [1,4,16] r11197 c11197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3347
  · exact u3348
  · exact u3349

def b11198 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 76 265 148 48 112 176 304), lower := (rows 67 131 76 265 148 32 64 128 256), losses := [] }

theorem u11198 : Upper (D 8) (R 8) [66,129,72,257,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11199 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 76 265 176 52 116 180 308), lower := (rows 67 131 76 265 176 32 64 128 256), losses := [] }

theorem u11199 : Upper (D 8) (R 8) [66,129,72,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11200 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 76 268 176 49 113 177 305), lower := (rows 67 131 76 268 176 32 64 128 256), losses := [] }

theorem u11200 : Upper (D 8) (R 8) [66,129,72,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11201 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 131 76 280 145 36 100 164 292), lower := (rows 67 131 76 280 145 32 64 128 256), losses := [] }

theorem u11201 : Upper (D 8) (R 8) [66,129,72,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11202 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 76 280 148 33 97 161 289), lower := (rows 67 131 76 280 148 32 64 128 256), losses := [] }

theorem u11202 : Upper (D 8) (R 8) [66,129,72,272,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11203 : Route 9 := (fun mask => (mask,id))

def c11203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11203 : Upper (D 8) (R 8) [66,129,72,272,160] 13 := by
  apply FastRouting.sound _ _ [66,129,72,272,160] 13 (by decide) (choices 1) [1,4] r11203 c11203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3350
  · exact u3351

def b11204 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 131 76 296 145 52 116 180 308), lower := (rows 67 131 76 296 145 32 64 128 256), losses := [] }

theorem u11204 : Upper (D 8) (R 8) [66,129,72,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11205 : Route 9 := (fun mask => (mask,id))

def c11205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11205 : Upper (D 8) (R 8) [66,129,72,288,132] 13 := by
  apply FastRouting.sound _ _ [66,129,72,288,132] 13 (by decide) (choices 1) [1,16] r11205 c11205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3352
  · exact u3353

def r11206 : Route 9 := (fun mask => (mask,id))

def c11206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11206 : Upper (D 8) (R 8) [66,129,72,288,160] 13 := by
  apply FastRouting.sound _ _ [66,129,72,288,160] 13 (by decide) (choices 1) [1,4,16] r11206 c11206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3354
  · exact u3355
  · exact u3356

def b11207 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 100 137 276 56 120 184 312), lower := (rows 67 131 100 137 276 32 64 128 256), losses := [] }

theorem u11207 : Upper (D 8) (R 8) [66,129,96,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11208 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 100 137 280 52 116 180 308), lower := (rows 67 131 100 137 280 32 64 128 256), losses := [] }

theorem u11208 : Upper (D 8) (R 8) [66,129,96,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11209 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 100 137 304 60 124 188 316), lower := (rows 67 131 100 137 304 32 64 128 256), losses := [] }

theorem u11209 : Upper (D 8) (R 8) [66,129,96,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11210 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 100 140 273 56 120 184 312), lower := (rows 67 131 100 140 273 32 64 128 256), losses := [] }

theorem u11210 : Upper (D 8) (R 8) [66,129,96,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11211 : Route 9 := (fun mask => (mask,id))

def c11211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11211 : Upper (D 8) (R 8) [66,129,96,132,264] 13 := by
  apply FastRouting.sound _ _ [66,129,96,132,264] 13 (by decide) (choices 1) [1,16] r11211 c11211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3357
  · exact u3358

def r11212 : Route 9 := (fun mask => (mask,id))

def c11212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11212 : Upper (D 8) (R 8) [66,129,96,132,288] 13 := by
  apply FastRouting.sound _ _ [66,129,96,132,288] 13 (by decide) (choices 1) [1,8,16] r11212 c11212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3359
  · exact u3360
  · exact u3361

def b11213 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 100 152 273 44 108 172 300), lower := (rows 67 131 100 152 273 32 64 128 256), losses := [] }

theorem u11213 : Upper (D 8) (R 8) [66,129,96,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11214 : Route 9 := (fun mask => (mask,id))

def c11214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11214 : Upper (D 8) (R 8) [66,129,96,144,260] 13 := by
  apply FastRouting.sound _ _ [66,129,96,144,260] 13 (by decide) (choices 1) [1,8] r11214 c11214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3362
  · exact u3363

def b11215 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 100 152 280 37 101 165 293), lower := (rows 67 131 100 152 280 32 64 128 256), losses := [] }

theorem u11215 : Upper (D 8) (R 8) [66,129,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11216 : Route 9 := (fun mask => (mask,id))

def c11216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11216 : Upper (D 8) (R 8) [66,129,96,144,288] 13 := by
  apply FastRouting.sound _ _ [66,129,96,144,288] 13 (by decide) (choices 1) [1,4,8] r11216 c11216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3364
  · exact u3365
  · exact u3366

def b11217 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 100 168 273 60 124 188 316), lower := (rows 67 131 100 168 273 32 64 128 256), losses := [] }

theorem u11217 : Upper (D 8) (R 8) [66,129,96,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11218 : Route 9 := (fun mask => (mask,id))

def c11218 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11218 : Upper (D 8) (R 8) [66,129,96,160,260] 13 := by
  apply FastRouting.sound _ _ [66,129,96,160,260] 13 (by decide) (choices 1) [1,8,16] r11218 c11218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3367
  · exact u3368
  · exact u3369

def r11219 : Route 9 := (fun mask => (mask,id))

def c11219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11219 : Upper (D 8) (R 8) [66,129,96,160,264] 13 := by
  apply FastRouting.sound _ _ [66,129,96,160,264] 13 (by decide) (choices 1) [1,4,16] r11219 c11219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3370
  · exact u3371
  · exact u3372

#print axioms u11219
end Delivery.IrregularNine14.P08
