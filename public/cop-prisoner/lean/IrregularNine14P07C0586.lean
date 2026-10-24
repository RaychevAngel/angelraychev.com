import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0335
import IrregularNine14P07C0336

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35160 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 28 208 291 355 419 291), lower := (rows 35 194 13 28 208 32 64 128 256), losses := [] }

theorem u35160 : Upper (D 7) (R 7) [34,192,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35161 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 28 273 226 226 226 482), lower := (rows 35 194 13 28 273 32 64 128 256), losses := [] }

theorem u35161 : Upper (D 7) (R 7) [34,192,9,20,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35162 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35162 : Upper (D 7) (R 7) [34,192,9,20,258] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20,258] 13 (by decide) (choices 1) [1,64] r35162 c35162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20148
  · exact u20149

def r35163 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35163 : Upper (D 7) (R 7) [34,192,9,20,288] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20,288] 13 (by decide) (choices 1) [1,2,64] r35163 c35163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20150
  · exact u20151
  · exact u20152

def r35164 : Route 9 := (fun mask => (mask,id))

def c35164 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35164 : Upper (D 7) (R 7) [34,192,9,20,320] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20,320] 13 (by decide) (choices 1) [1,2,128] r35164 c35164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20153
  · exact u20154
  · exact u20155

def b35165 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 41 22 496 464 464 464), lower := (rows 35 194 13 41 22 32 64 128 256), losses := [] }

theorem u35165 : Upper (D 7) (R 7) [34,192,9,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35166 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 13 41 84 434 466 402 402), lower := (rows 35 194 13 41 84 32 64 128 256), losses := [] }

theorem u35166 : Upper (D 7) (R 7) [34,192,9,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35167 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 13 41 274 244 212 212 468), lower := (rows 35 194 13 41 274 32 64 128 256), losses := [] }

theorem u35167 : Upper (D 7) (R 7) [34,192,9,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35168 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 13 41 276 242 210 210 466), lower := (rows 35 194 13 41 276 32 64 128 256), losses := [] }

theorem u35168 : Upper (D 7) (R 7) [34,192,9,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35169 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 13 41 336 182 214 150 406), lower := (rows 35 194 13 41 336 32 64 128 256), losses := [] }

theorem u35169 : Upper (D 7) (R 7) [34,192,9,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35170 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 42 81 436 468 404 404), lower := (rows 35 194 13 42 81 32 64 128 256), losses := [] }

theorem u35170 : Upper (D 7) (R 7) [34,192,9,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35171 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 42 84 433 465 401 401), lower := (rows 35 194 13 42 84 32 64 128 256), losses := [] }

theorem u35171 : Upper (D 7) (R 7) [34,192,9,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35172 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 42 273 244 212 212 468), lower := (rows 35 194 13 42 273 32 64 128 256), losses := [] }

theorem u35172 : Upper (D 7) (R 7) [34,192,9,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35173 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 42 276 241 209 209 465), lower := (rows 35 194 13 42 276 32 64 128 256), losses := [] }

theorem u35173 : Upper (D 7) (R 7) [34,192,9,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35174 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 42 336 181 213 149 405), lower := (rows 35 194 13 42 336 32 64 128 256), losses := [] }

theorem u35174 : Upper (D 7) (R 7) [34,192,9,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35175 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 13 44 81 434 466 402 402), lower := (rows 35 194 13 44 81 32 64 128 256), losses := [] }

theorem u35175 : Upper (D 7) (R 7) [34,192,9,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35176 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 13 44 273 242 210 210 466), lower := (rows 35 194 13 44 273 32 64 128 256), losses := [] }

theorem u35176 : Upper (D 7) (R 7) [34,192,9,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35177 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 13 44 274 241 209 209 465), lower := (rows 35 194 13 44 274 32 64 128 256), losses := [] }

theorem u35177 : Upper (D 7) (R 7) [34,192,9,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35178 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 13 44 336 179 211 147 403), lower := (rows 35 194 13 44 336 32 64 128 256), losses := [] }

theorem u35178 : Upper (D 7) (R 7) [34,192,9,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35179 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 56 22 481 449 449 449), lower := (rows 35 194 13 56 22 32 64 128 256), losses := [] }

theorem u35179 : Upper (D 7) (R 7) [34,192,9,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35180 : Route 9 := (fun mask => (mask,id))

def c35180 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u35180 : Upper (D 7) (R 7) [34,192,9,48,65] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,65] 13 (by decide) (choices 1) [2,4,128,256] r35180 c35180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20156
  · exact u20157
  · exact u20158
  · exact u20159

def b35181 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 194 13 56 82 421 453 389 389), lower := (rows 35 194 13 56 82 32 64 128 256), losses := [] }

theorem u35181 : Upper (D 7) (R 7) [34,192,9,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35182 : Route 9 := (fun mask => (mask,id))

def c35182 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u35182 : Upper (D 7) (R 7) [34,192,9,48,68] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,68] 13 (by decide) (choices 1) [1,2,128,256] r35182 c35182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20160
  · exact u20161
  · exact u20162
  · exact u20163

def b35183 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 56 208 295 327 391 263), lower := (rows 35 194 13 56 208 32 64 128 256), losses := [] }

theorem u35183 : Upper (D 7) (R 7) [34,192,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35184 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35184 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35184 : Upper (D 7) (R 7) [34,192,9,48,257] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,257] 13 (by decide) (choices 1) [2,4,64] r35184 c35184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20164
  · exact u20165
  · exact u20166

def r35185 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35185 : Upper (D 7) (R 7) [34,192,9,48,258] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,258] 13 (by decide) (choices 1) [1,4,64] r35185 c35185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20167
  · exact u20168
  · exact u20169

def r35186 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35186 : Upper (D 7) (R 7) [34,192,9,48,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,260] 13 (by decide) (choices 1) [1,2,64] r35186 c35186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20170
  · exact u20171
  · exact u20172

def r35187 : Route 9 := (fun mask => (mask,id))

def c35187 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35187 : Upper (D 7) (R 7) [34,192,9,48,320] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,320] 13 (by decide) (choices 1) [1,2,4,128] r35187 c35187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20173
  · exact u20174
  · exact u20175
  · exact u20176

def b35188 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 73 22 432 496 432 432), lower := (rows 35 194 13 73 22 32 64 128 256), losses := [] }

theorem u35188 : Upper (D 7) (R 7) [34,192,9,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35189 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 73 52 434 466 402 402), lower := (rows 35 194 13 73 52 32 64 128 256), losses := [] }

theorem u35189 : Upper (D 7) (R 7) [34,192,9,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35190 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 73 148 306 370 434 306), lower := (rows 35 194 13 73 148 32 64 128 256), losses := [] }

theorem u35190 : Upper (D 7) (R 7) [34,192,9,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35191 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 73 176 310 342 406 278), lower := (rows 35 194 13 73 176 32 64 128 256), losses := [] }

theorem u35191 : Upper (D 7) (R 7) [34,192,9,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35192 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 73 274 180 244 180 436), lower := (rows 35 194 13 73 274 32 64 128 256), losses := [] }

theorem u35192 : Upper (D 7) (R 7) [34,192,9,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35193 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 73 276 178 242 178 434), lower := (rows 35 194 13 73 276 32 64 128 256), losses := [] }

theorem u35193 : Upper (D 7) (R 7) [34,192,9,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35194 : PairBound 9 := { available := 150, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 73 304 182 214 150 406), lower := (rows 35 194 13 73 304 32 64 128 256), losses := [] }

theorem u35194 : Upper (D 7) (R 7) [34,192,9,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35195 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 73 400 54 118 182 310), lower := (rows 35 194 13 73 400 32 64 128 256), losses := [] }

theorem u35195 : Upper (D 7) (R 7) [34,192,9,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35196 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 13 74 52 433 465 401 401), lower := (rows 35 194 13 74 52 32 64 128 256), losses := [] }

theorem u35196 : Upper (D 7) (R 7) [34,192,9,66,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35197 : PairBound 9 := { available := 308, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 13 74 145 308 372 436 308), lower := (rows 35 194 13 74 145 32 64 128 256), losses := [] }

theorem u35197 : Upper (D 7) (R 7) [34,192,9,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35198 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 13 74 148 305 369 433 305), lower := (rows 35 194 13 74 148 32 64 128 256), losses := [] }

theorem u35198 : Upper (D 7) (R 7) [34,192,9,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35199 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 13 74 176 309 341 405 277), lower := (rows 35 194 13 74 176 32 64 128 256), losses := [] }

theorem u35199 : Upper (D 7) (R 7) [34,192,9,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35200 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 13 74 273 180 244 180 436), lower := (rows 35 194 13 74 273 32 64 128 256), losses := [] }

theorem u35200 : Upper (D 7) (R 7) [34,192,9,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35201 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 13 74 276 177 241 177 433), lower := (rows 35 194 13 74 276 32 64 128 256), losses := [] }

theorem u35201 : Upper (D 7) (R 7) [34,192,9,66,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35202 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 13 74 304 181 213 149 405), lower := (rows 35 194 13 74 304 32 64 128 256), losses := [] }

theorem u35202 : Upper (D 7) (R 7) [34,192,9,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35203 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 13 74 400 53 117 181 309), lower := (rows 35 194 13 74 400 32 64 128 256), losses := [] }

theorem u35203 : Upper (D 7) (R 7) [34,192,9,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35204 : PairBound 9 := { available := 402, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 194 13 76 49 434 466 402 402), lower := (rows 35 194 13 76 49 32 64 128 256), losses := [] }

theorem u35204 : Upper (D 7) (R 7) [34,192,9,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35205 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 128 }], pairs := [(0,6),(4,0),(4,6),(4,7)], upper := (rows 35 194 13 76 50 433 465 401 401), lower := (rows 35 194 13 76 50 32 64 128 256), losses := [] }

theorem u35205 : Upper (D 7) (R 7) [34,192,9,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35206 : Route 9 := (fun mask => (mask,id))

def c35206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35206 : Upper (D 7) (R 7) [34,192,9,68,129] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,129] 13 (by decide) (choices 1) [2,16,256] r35206 c35206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20177
  · exact u20178
  · exact u20179

def b35207 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 365, targets := 128 },{ cop := 1, region := 16, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 35 194 13 76 146 305 369 433 305), lower := (rows 35 194 13 76 146 32 64 128 256), losses := [] }

theorem u35207 : Upper (D 7) (R 7) [34,192,9,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35208 : Route 9 := (fun mask => (mask,id))

def c35208 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35208 : Upper (D 7) (R 7) [34,192,9,68,160] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,160] 13 (by decide) (choices 1) [1,2,16,256] r35208 c35208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20180
  · exact u20181
  · exact u20182
  · exact u20183

def r35209 : Route 9 := (fun mask => (mask,id))

def c35209 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35209 : Upper (D 7) (R 7) [34,192,9,68,257] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,257] 13 (by decide) (choices 1) [2,16,128] r35209 c35209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20184
  · exact u20185
  · exact u20186

def r35210 : Route 9 := (fun mask => (mask,id))

def c35210 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35210 : Upper (D 7) (R 7) [34,192,9,68,258] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,258] 13 (by decide) (choices 1) [1,16,128] r35210 c35210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20187
  · exact u20188
  · exact u20189

def r35211 : Route 9 := (fun mask => (mask,id))

def c35211 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35211 : Upper (D 7) (R 7) [34,192,9,68,288] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,288] 13 (by decide) (choices 1) [1,2,16,128] r35211 c35211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20190
  · exact u20191
  · exact u20192
  · exact u20193

def r35212 : Route 9 := (fun mask => (mask,id))

def c35212 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35212 : Upper (D 7) (R 7) [34,192,9,68,384] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,384] 13 (by decide) (choices 1) [1,2,16] r35212 c35212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20194
  · exact u20195
  · exact u20196

def r35213 : Route 9 := (fun mask => (mask,id))

def c35213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u35213 : Upper (D 7) (R 7) [34,192,9,80,6] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,6] 13 (by decide) (choices 1) [1,128,256] r35213 c35213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20197
  · exact u20198
  · exact u20199

def b35214 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 194 13 88 49 422 454 390 390), lower := (rows 35 194 13 88 49 32 64 128 256), losses := [] }

theorem u35214 : Upper (D 7) (R 7) [34,192,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35215 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 194 13 88 50 421 453 389 389), lower := (rows 35 194 13 88 50 32 64 128 256), losses := [] }

theorem u35215 : Upper (D 7) (R 7) [34,192,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35216 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(1,5),(3,5),(4,6)], upper := (rows 35 194 13 88 52 419 451 387 387), lower := (rows 35 194 13 88 52 32 64 128 256), losses := [{ target := 5, region := (rows 1 23 4 24 16 0 69 133 261), good := (rows 451 194 463 90 478 0 64 128 256) },{ target := 6, region := (rows 3 2 4 8 20 35 0 131 259), good := (rows 419 419 445 24 52 32 0 128 256) }] }

theorem u35216 : Upper (D 7) (R 7) [34,192,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35217 : Route 9 := (fun mask => (mask,id))

def c35217 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35217 : Upper (D 7) (R 7) [34,192,9,80,129] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,129] 13 (by decide) (choices 1) [2,4,256] r35217 c35217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20200
  · exact u20201
  · exact u20202

def b35218 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 194 13 88 146 293 357 421 293), lower := (rows 35 194 13 88 146 32 64 128 256), losses := [] }

theorem u35218 : Upper (D 7) (R 7) [34,192,9,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35219 : Route 9 := (fun mask => (mask,id))

def c35219 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35219 : Upper (D 7) (R 7) [34,192,9,80,132] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,132] 13 (by decide) (choices 1) [1,2,256] r35219 c35219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20203
  · exact u20204
  · exact u20205

#print axioms u35219
end Delivery.IrregularNine14.P07
