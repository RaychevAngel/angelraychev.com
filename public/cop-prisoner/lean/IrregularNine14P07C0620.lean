import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0389
import IrregularNine14P07C0390
import IrregularNine14P07C0391

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37200 : Route 9 := (fun mask => (mask,id))

def c37200 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37200 : Upper (D 7) (R 7) [36,72,144,257,96] 13 := by
  apply FastRouting.sound _ _ [36,72,144,257,96] 13 (by decide) (choices 1) [1,2,128] r37200 c37200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23385
  · exact u23386
  · exact u23387

def b37201 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 74 148 265 145 98 98 226 354), lower := (rows 37 74 148 265 145 32 64 128 256), losses := [] }

theorem u37201 : Upper (D 7) (R 7) [36,72,144,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37202 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 74 148 265 146 99 99 227 355), lower := (rows 37 74 148 265 146 32 64 128 256), losses := [] }

theorem u37202 : Upper (D 7) (R 7) [36,72,144,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37203 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 148 265 176 99 67 195 323), lower := (rows 37 74 148 265 176 32 64 128 256), losses := [] }

theorem u37203 : Upper (D 7) (R 7) [36,72,144,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37204 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 74 148 265 208 35 99 163 291), lower := (rows 37 74 148 265 208 32 64 128 256), losses := [] }

theorem u37204 : Upper (D 7) (R 7) [36,72,144,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37205 : Route 9 := (fun mask => (mask,id))

def c37205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37205 : Upper (D 7) (R 7) [36,72,144,258,3] 13 := by
  apply FastRouting.sound _ _ [36,72,144,258,3] 13 (by decide) (choices 1) [1,64,128] r37205 c37205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23388
  · exact u23389
  · exact u23390

def b37206 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 148 266 49 227 195 195 451), lower := (rows 37 74 148 266 49 32 64 128 256), losses := [] }

theorem u37206 : Upper (D 7) (R 7) [36,72,144,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37207 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(3,5)], upper := (rows 37 74 148 266 50 225 193 193 449), lower := (rows 37 74 148 266 50 32 64 128 256), losses := [] }

theorem u37207 : Upper (D 7) (R 7) [36,72,144,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37208 : Route 9 := (fun mask => (mask,id))

def c37208 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37208 : Upper (D 7) (R 7) [36,72,144,258,65] 13 := by
  apply FastRouting.sound _ _ [36,72,144,258,65] 13 (by decide) (choices 1) [1,2,128] r37208 c37208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23391
  · exact u23392
  · exact u23393

def b37209 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 148 266 82 161 225 161 417), lower := (rows 37 74 148 266 82 32 64 128 256), losses := [] }

theorem u37209 : Upper (D 7) (R 7) [36,72,144,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37210 : Route 9 := (fun mask => (mask,id))

def c37210 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37210 : Upper (D 7) (R 7) [36,72,144,258,96] 13 := by
  apply FastRouting.sound _ _ [36,72,144,258,96] 13 (by decide) (choices 1) [1,2,128] r37210 c37210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23394
  · exact u23395
  · exact u23396

def b37211 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 74 148 266 145 99 99 227 355), lower := (rows 37 74 148 266 145 32 64 128 256), losses := [] }

theorem u37211 : Upper (D 7) (R 7) [36,72,144,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37212 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 363, targets := 128 },{ cop := 4, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 37 74 148 266 146 97 97 225 353), lower := (rows 37 74 148 266 146 32 64 128 256), losses := [] }

theorem u37212 : Upper (D 7) (R 7) [36,72,144,258,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37213 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 148 266 176 99 67 195 323), lower := (rows 37 74 148 266 176 32 64 128 256), losses := [] }

theorem u37213 : Upper (D 7) (R 7) [36,72,144,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37214 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 74 148 266 208 35 99 163 291), lower := (rows 37 74 148 266 208 32 64 128 256), losses := [] }

theorem u37214 : Upper (D 7) (R 7) [36,72,144,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37215 : Route 9 := (fun mask => (mask,id))

def c37215 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37215 : Upper (D 7) (R 7) [36,72,144,288,3] 13 := by
  apply FastRouting.sound _ _ [36,72,144,288,3] 13 (by decide) (choices 1) [1,2,64,128] r37215 c37215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23397
  · exact u23398
  · exact u23399
  · exact u23400

def r37216 : Route 9 := (fun mask => (mask,id))

def c37216 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37216 : Upper (D 7) (R 7) [36,72,144,288,65] 13 := by
  apply FastRouting.sound _ _ [36,72,144,288,65] 13 (by decide) (choices 1) [1,2,128] r37216 c37216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23401
  · exact u23402
  · exact u23403

def b37217 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 148 296 82 163 195 131 387), lower := (rows 37 74 148 296 82 32 64 128 256), losses := [] }

theorem u37217 : Upper (D 7) (R 7) [36,72,144,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37218 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 74 148 296 145 99 67 195 323), lower := (rows 37 74 148 296 145 32 64 128 256), losses := [] }

theorem u37218 : Upper (D 7) (R 7) [36,72,144,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37219 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 74 148 296 146 99 67 195 323), lower := (rows 37 74 148 296 146 32 64 128 256), losses := [] }

theorem u37219 : Upper (D 7) (R 7) [36,72,144,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37220 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 74 148 296 208 35 67 131 259), lower := (rows 37 74 148 296 208 32 64 128 256), losses := [] }

theorem u37220 : Upper (D 7) (R 7) [36,72,144,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37221 : Route 9 := (fun mask => (mask,id))

def c37221 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37221 : Upper (D 7) (R 7) [36,72,144,384,3] 13 := by
  apply FastRouting.sound _ _ [36,72,144,384,3] 13 (by decide) (choices 1) [1,2,64] r37221 c37221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23404
  · exact u23405
  · exact u23406

def b37222 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 148 392 49 99 67 195 323), lower := (rows 37 74 148 392 49 32 64 128 256), losses := [] }

theorem u37222 : Upper (D 7) (R 7) [36,72,144,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37223 : Route 9 := (fun mask => (mask,id))

def c37223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37223 : Upper (D 7) (R 7) [36,72,144,384,34] 13 := by
  apply FastRouting.sound _ _ [36,72,144,384,34] 13 (by decide) (choices 1) [1,2,64] r37223 c37223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23407
  · exact u23408
  · exact u23409

def r37224 : Route 9 := (fun mask => (mask,id))

def c37224 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37224 : Upper (D 7) (R 7) [36,72,144,384,65] 13 := by
  apply FastRouting.sound _ _ [36,72,144,384,65] 13 (by decide) (choices 1) [1,2] r37224 c37224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23410
  · exact u23411

def b37225 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 148 392 82 35 99 163 291), lower := (rows 37 74 148 392 82 32 64 128 256), losses := [] }

theorem u37225 : Upper (D 7) (R 7) [36,72,144,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37226 : Route 9 := (fun mask => (mask,id))

def c37226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37226 : Upper (D 7) (R 7) [36,72,144,384,96] 13 := by
  apply FastRouting.sound _ _ [36,72,144,384,96] 13 (by decide) (choices 1) [1,2] r37226 c37226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23412
  · exact u23413

def r37227 : Route 9 := (fun mask => (mask,id))

def c37227 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37227 : Upper (D 7) (R 7) [36,72,192,160,3] 13 := by
  apply FastRouting.sound _ _ [36,72,192,160,3] 13 (by decide) (choices 1) [1,2,16,256] r37227 c37227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23414
  · exact u23415
  · exact u23416
  · exact u23417

def r37228 : Route 9 := (fun mask => (mask,id))

def c37228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37228 : Upper (D 7) (R 7) [36,72,192,160,257] 13 := by
  apply FastRouting.sound _ _ [36,72,192,160,257] 13 (by decide) (choices 1) [1,2,16] r37228 c37228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23418
  · exact u23419
  · exact u23420

def r37229 : Route 9 := (fun mask => (mask,id))

def c37229 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37229 : Upper (D 7) (R 7) [36,72,192,257,3] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257,3] 13 (by decide) (choices 1) [2,16,128] r37229 c37229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23421
  · exact u23422
  · exact u23423

def b37230 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 196 265 49 178 210 146 402), lower := (rows 37 74 196 265 49 32 64 128 256), losses := [] }

theorem u37230 : Upper (D 7) (R 7) [36,72,192,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37231 : Route 9 := (fun mask => (mask,id))

def c37231 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37231 : Upper (D 7) (R 7) [36,72,192,257,34] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257,34] 13 (by decide) (choices 1) [1,2,16,128] r37231 c37231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23424
  · exact u23425
  · exact u23426
  · exact u23427

def r37232 : Route 9 := (fun mask => (mask,id))

def c37232 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37232 : Upper (D 7) (R 7) [36,72,192,257,129] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257,129] 13 (by decide) (choices 1) [2,16] r37232 c37232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23428
  · exact u23429

def r37233 : Route 9 := (fun mask => (mask,id))

def c37233 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37233 : Upper (D 7) (R 7) [36,72,192,257,130] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257,130] 13 (by decide) (choices 1) [1,2,16] r37233 c37233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23430
  · exact u23431
  · exact u23432

def r37234 : Route 9 := (fun mask => (mask,id))

def c37234 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37234 : Upper (D 7) (R 7) [36,72,192,257,160] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257,160] 13 (by decide) (choices 1) [1,2,16] r37234 c37234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23433
  · exact u23434
  · exact u23435

def r37235 : Route 9 := (fun mask => (mask,id))

def c37235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37235 : Upper (D 7) (R 7) [36,72,192,258,3] 13 := by
  apply FastRouting.sound _ _ [36,72,192,258,3] 13 (by decide) (choices 1) [1,16,128] r37235 c37235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23436
  · exact u23437
  · exact u23438

def b37236 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 196 266 49 179 211 147 403), lower := (rows 37 74 196 266 49 32 64 128 256), losses := [] }

theorem u37236 : Upper (D 7) (R 7) [36,72,192,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37237 : Route 9 := (fun mask => (mask,id))

def c37237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37237 : Upper (D 7) (R 7) [36,72,192,258,34] 13 := by
  apply FastRouting.sound _ _ [36,72,192,258,34] 13 (by decide) (choices 1) [1,16,128] r37237 c37237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23439
  · exact u23440
  · exact u23441

def r37238 : Route 9 := (fun mask => (mask,id))

def c37238 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37238 : Upper (D 7) (R 7) [36,72,192,258,129] 13 := by
  apply FastRouting.sound _ _ [36,72,192,258,129] 13 (by decide) (choices 1) [1,2,16] r37238 c37238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23442
  · exact u23443
  · exact u23444

def r37239 : Route 9 := (fun mask => (mask,id))

def c37239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37239 : Upper (D 7) (R 7) [36,72,192,258,130] 13 := by
  apply FastRouting.sound _ _ [36,72,192,258,130] 13 (by decide) (choices 1) [1,16] r37239 c37239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23445
  · exact u23446

def r37240 : Route 9 := (fun mask => (mask,id))

def c37240 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37240 : Upper (D 7) (R 7) [36,72,192,258,160] 13 := by
  apply FastRouting.sound _ _ [36,72,192,258,160] 13 (by decide) (choices 1) [1,2,16] r37240 c37240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23447
  · exact u23448
  · exact u23449

def r37241 : Route 9 := (fun mask => (mask,id))

def c37241 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37241 : Upper (D 7) (R 7) [36,72,192,272,3] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272,3] 13 (by decide) (choices 1) [1,2,128] r37241 c37241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23450
  · exact u23451
  · exact u23452

def b37242 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 196 280 49 163 195 131 387), lower := (rows 37 74 196 280 49 32 64 128 256), losses := [] }

theorem u37242 : Upper (D 7) (R 7) [36,72,192,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37243 : Route 9 := (fun mask => (mask,id))

def c37243 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37243 : Upper (D 7) (R 7) [36,72,192,272,34] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272,34] 13 (by decide) (choices 1) [1,2,128] r37243 c37243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23453
  · exact u23454
  · exact u23455

def r37244 : Route 9 := (fun mask => (mask,id))

def c37244 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37244 : Upper (D 7) (R 7) [36,72,192,272,129] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272,129] 13 (by decide) (choices 1) [1,2] r37244 c37244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23456
  · exact u23457

def r37245 : Route 9 := (fun mask => (mask,id))

def c37245 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37245 : Upper (D 7) (R 7) [36,72,192,272,130] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272,130] 13 (by decide) (choices 1) [1,2] r37245 c37245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23458
  · exact u23459

def r37246 : Route 9 := (fun mask => (mask,id))

def c37246 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37246 : Upper (D 7) (R 7) [36,72,192,272,160] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272,160] 13 (by decide) (choices 1) [1,2] r37246 c37246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23460
  · exact u23461

def r37247 : Route 9 := (fun mask => (mask,id))

def c37247 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37247 : Upper (D 7) (R 7) [36,72,192,288,3] 13 := by
  apply FastRouting.sound _ _ [36,72,192,288,3] 13 (by decide) (choices 1) [1,2,16,128] r37247 c37247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23462
  · exact u23463
  · exact u23464
  · exact u23465

def r37248 : Route 9 := (fun mask => (mask,id))

def c37248 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37248 : Upper (D 7) (R 7) [36,72,192,288,129] 13 := by
  apply FastRouting.sound _ _ [36,72,192,288,129] 13 (by decide) (choices 1) [1,2,16] r37248 c37248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23466
  · exact u23467
  · exact u23468

def r37249 : Route 9 := (fun mask => (mask,id))

def c37249 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37249 : Upper (D 7) (R 7) [36,72,192,288,130] 13 := by
  apply FastRouting.sound _ _ [36,72,192,288,130] 13 (by decide) (choices 1) [1,2,16] r37249 c37249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23469
  · exact u23470
  · exact u23471

def r37250 : Route 9 := (fun mask => (mask,id))

def c37250 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37250 : Upper (D 7) (R 7) [36,72,192,384,3] 13 := by
  apply FastRouting.sound _ _ [36,72,192,384,3] 13 (by decide) (choices 1) [1,2,16] r37250 c37250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23472
  · exact u23473
  · exact u23474

def b37251 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 196 392 49 51 83 147 275), lower := (rows 37 74 196 392 49 32 64 128 256), losses := [] }

theorem u37251 : Upper (D 7) (R 7) [36,72,192,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37252 : Route 9 := (fun mask => (mask,id))

def c37252 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37252 : Upper (D 7) (R 7) [36,72,192,384,34] 13 := by
  apply FastRouting.sound _ _ [36,72,192,384,34] 13 (by decide) (choices 1) [1,2,16] r37252 c37252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23475
  · exact u23476
  · exact u23477

def b37253 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 26 19 480 448 448 448), lower := (rows 37 98 13 26 19 32 64 128 256), losses := [] }

theorem u37253 : Upper (D 7) (R 7) [36,96,9,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37254 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 13 26 81 418 450 386 386), lower := (rows 37 98 13 26 81 32 64 128 256), losses := [] }

theorem u37254 : Upper (D 7) (R 7) [36,96,9,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37255 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 13 26 82 417 449 385 385), lower := (rows 37 98 13 26 82 32 64 128 256), losses := [] }

theorem u37255 : Upper (D 7) (R 7) [36,96,9,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37256 : Route 9 := (fun mask => (mask,id))

def c37256 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u37256 : Upper (D 7) (R 7) [36,96,9,18,129] 13 := by
  apply FastRouting.sound _ _ [36,96,9,18,129] 13 (by decide) (choices 1) [2,64,128,256] r37256 c37256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23478
  · exact u23479
  · exact u23480
  · exact u23481

def b37257 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 13 26 146 481 449 449 449), lower := (rows 37 98 13 26 146 32 64 128 256), losses := [] }

theorem u37257 : Upper (D 7) (R 7) [36,96,9,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37258 : Route 9 := (fun mask => (mask,id))

def c37258 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37258 : Upper (D 7) (R 7) [36,96,9,18,192] 13 := by
  apply FastRouting.sound _ _ [36,96,9,18,192] 13 (by decide) (choices 1) [1,2,128,256] r37258 c37258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23482
  · exact u23483
  · exact u23484
  · exact u23485

def r37259 : Route 9 := (fun mask => (mask,id))

def c37259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37259 : Upper (D 7) (R 7) [36,96,9,18,257] 13 := by
  apply FastRouting.sound _ _ [36,96,9,18,257] 13 (by decide) (choices 1) [2,64,128] r37259 c37259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23486
  · exact u23487
  · exact u23488

#print axioms u37259
end Delivery.IrregularNine14.P07
