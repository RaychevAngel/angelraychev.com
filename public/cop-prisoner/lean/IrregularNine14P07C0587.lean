import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0336
import IrregularNine14P07C0337
import IrregularNine14P07C0338

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35220 : Route 9 := (fun mask => (mask,id))

def c35220 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35220 : Upper (D 7) (R 7) [34,192,9,80,160] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,160] 13 (by decide) (choices 1) [1,2,4,256] r35220 c35220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20206
  · exact u20207
  · exact u20208
  · exact u20209

def r35221 : Route 9 := (fun mask => (mask,id))

def c35221 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35221 : Upper (D 7) (R 7) [34,192,9,80,257] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,257] 13 (by decide) (choices 1) [2,4,128] r35221 c35221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20210
  · exact u20211
  · exact u20212

def r35222 : Route 9 := (fun mask => (mask,id))

def c35222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35222 : Upper (D 7) (R 7) [34,192,9,80,258] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,258] 13 (by decide) (choices 1) [1,4,128] r35222 c35222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20213
  · exact u20214
  · exact u20215

def r35223 : Route 9 := (fun mask => (mask,id))

def c35223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35223 : Upper (D 7) (R 7) [34,192,9,80,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,260] 13 (by decide) (choices 1) [1,2,128] r35223 c35223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20216
  · exact u20217
  · exact u20218

def r35224 : Route 9 := (fun mask => (mask,id))

def c35224 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35224 : Upper (D 7) (R 7) [34,192,9,80,288] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,288] 13 (by decide) (choices 1) [1,2,4,128] r35224 c35224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20219
  · exact u20220
  · exact u20221
  · exact u20222

def r35225 : Route 9 := (fun mask => (mask,id))

def c35225 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35225 : Upper (D 7) (R 7) [34,192,9,80,384] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,384] 13 (by decide) (choices 1) [1,2,4] r35225 c35225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20223
  · exact u20224
  · exact u20225

def r35226 : Route 9 := (fun mask => (mask,id))

def c35226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u35226 : Upper (D 7) (R 7) [34,192,9,96,6] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,6] 13 (by decide) (choices 1) [1,16,128,256] r35226 c35226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20226
  · exact u20227
  · exact u20228
  · exact u20229

def r35227 : Route 9 := (fun mask => (mask,id))

def c35227 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35227 : Upper (D 7) (R 7) [34,192,9,96,129] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,129] 13 (by decide) (choices 1) [2,4,16,256] r35227 c35227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20230
  · exact u20231
  · exact u20232
  · exact u20233

def b35228 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 35 194 13 104 146 309 341 405 277), lower := (rows 35 194 13 104 146 32 64 128 256), losses := [] }

theorem u35228 : Upper (D 7) (R 7) [34,192,9,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35229 : Route 9 := (fun mask => (mask,id))

def c35229 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35229 : Upper (D 7) (R 7) [34,192,9,96,132] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,132] 13 (by decide) (choices 1) [1,2,16,256] r35229 c35229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20234
  · exact u20235
  · exact u20236
  · exact u20237

def r35230 : Route 9 := (fun mask => (mask,id))

def c35230 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35230 : Upper (D 7) (R 7) [34,192,9,96,257] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,257] 13 (by decide) (choices 1) [2,4,16,128] r35230 c35230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20238
  · exact u20239
  · exact u20240
  · exact u20241

def r35231 : Route 9 := (fun mask => (mask,id))

def c35231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35231 : Upper (D 7) (R 7) [34,192,9,96,258] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,258] 13 (by decide) (choices 1) [1,4,16,128] r35231 c35231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20242
  · exact u20243
  · exact u20244
  · exact u20245

def r35232 : Route 9 := (fun mask => (mask,id))

def c35232 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35232 : Upper (D 7) (R 7) [34,192,9,96,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,260] 13 (by decide) (choices 1) [1,2,16,128] r35232 c35232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20246
  · exact u20247
  · exact u20248
  · exact u20249

def r35233 : Route 9 := (fun mask => (mask,id))

def c35233 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35233 : Upper (D 7) (R 7) [34,192,9,96,384] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,384] 13 (by decide) (choices 1) [1,2,4,16] r35233 c35233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20250
  · exact u20251
  · exact u20252
  · exact u20253

def b35234 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 200 22 305 369 433 305), lower := (rows 35 194 13 200 22 32 64 128 256), losses := [] }

theorem u35234 : Upper (D 7) (R 7) [34,192,9,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35235 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 200 52 307 339 403 275), lower := (rows 35 194 13 200 52 32 64 128 256), losses := [] }

theorem u35235 : Upper (D 7) (R 7) [34,192,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35236 : PairBound 9 := { available := 54, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 200 273 54 118 182 310), lower := (rows 35 194 13 200 273 32 64 128 256), losses := [] }

theorem u35236 : Upper (D 7) (R 7) [34,192,9,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35237 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 200 274 53 117 181 309), lower := (rows 35 194 13 200 274 32 64 128 256), losses := [] }

theorem u35237 : Upper (D 7) (R 7) [34,192,9,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35238 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 200 276 51 115 179 307), lower := (rows 35 194 13 200 276 32 64 128 256), losses := [] }

theorem u35238 : Upper (D 7) (R 7) [34,192,9,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35239 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 200 304 55 87 151 279), lower := (rows 35 194 13 200 304 32 64 128 256), losses := [] }

theorem u35239 : Upper (D 7) (R 7) [34,192,9,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35240 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 265 22 240 240 240 496), lower := (rows 35 194 13 265 22 32 64 128 256), losses := [] }

theorem u35240 : Upper (D 7) (R 7) [34,192,9,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35241 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 265 52 242 210 210 466), lower := (rows 35 194 13 265 52 32 64 128 256), losses := [] }

theorem u35241 : Upper (D 7) (R 7) [34,192,9,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35242 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 265 84 178 242 178 434), lower := (rows 35 194 13 265 84 32 64 128 256), losses := [] }

theorem u35242 : Upper (D 7) (R 7) [34,192,9,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35243 : PairBound 9 := { available := 150, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 265 112 182 214 150 406), lower := (rows 35 194 13 265 112 32 64 128 256), losses := [] }

theorem u35243 : Upper (D 7) (R 7) [34,192,9,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35244 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 194 13 266 49 244 212 212 468), lower := (rows 35 194 13 266 49 32 64 128 256), losses := [] }

theorem u35244 : Upper (D 7) (R 7) [34,192,9,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35245 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35245 : Upper (D 7) (R 7) [34,192,9,258,36] 13 := by
  apply FastRouting.sound _ _ [34,192,9,258,36] 13 (by decide) (choices 1) [1,16,64] r35245 c35245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20254
  · exact u20255
  · exact u20256

def r35246 : Route 9 := (fun mask => (mask,id))

def c35246 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35246 : Upper (D 7) (R 7) [34,192,9,258,65] 13 := by
  apply FastRouting.sound _ _ [34,192,9,258,65] 13 (by decide) (choices 1) [4,16,128] r35246 c35246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20257
  · exact u20258
  · exact u20259

def r35247 : Route 9 := (fun mask => (mask,id))

def c35247 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35247 : Upper (D 7) (R 7) [34,192,9,258,68] 13 := by
  apply FastRouting.sound _ _ [34,192,9,258,68] 13 (by decide) (choices 1) [1,16,128] r35247 c35247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20260
  · exact u20261
  · exact u20262

def r35248 : Route 9 := (fun mask => (mask,id))

def c35248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35248 : Upper (D 7) (R 7) [34,192,9,258,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,258,96] 13 (by decide) (choices 1) [1,4,16,128] r35248 c35248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20263
  · exact u20264
  · exact u20265
  · exact u20266

def b35249 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 266 208 53 117 181 309), lower := (rows 35 194 13 266 208 32 64 128 256), losses := [] }

theorem u35249 : Upper (D 7) (R 7) [34,192,9,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35250 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 194 13 268 49 242 210 210 466), lower := (rows 35 194 13 268 49 32 64 128 256), losses := [] }

theorem u35250 : Upper (D 7) (R 7) [34,192,9,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35251 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 194 13 268 50 241 209 209 465), lower := (rows 35 194 13 268 50 32 64 128 256), losses := [] }

theorem u35251 : Upper (D 7) (R 7) [34,192,9,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35252 : Route 9 := (fun mask => (mask,id))

def c35252 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35252 : Upper (D 7) (R 7) [34,192,9,260,65] 13 := by
  apply FastRouting.sound _ _ [34,192,9,260,65] 13 (by decide) (choices 1) [2,16,128] r35252 c35252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20267
  · exact u20268
  · exact u20269

def b35253 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 194 13 268 82 177 241 177 433), lower := (rows 35 194 13 268 82 32 64 128 256), losses := [] }

theorem u35253 : Upper (D 7) (R 7) [34,192,9,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35254 : Route 9 := (fun mask => (mask,id))

def c35254 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35254 : Upper (D 7) (R 7) [34,192,9,260,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,260,96] 13 (by decide) (choices 1) [1,2,16,128] r35254 c35254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20270
  · exact u20271
  · exact u20272
  · exact u20273

def b35255 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 268 208 51 115 179 307), lower := (rows 35 194 13 268 208 32 64 128 256), losses := [] }

theorem u35255 : Upper (D 7) (R 7) [34,192,9,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35256 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35256 : Upper (D 7) (R 7) [34,192,9,272,6] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,6] 13 (by decide) (choices 1) [1,64] r35256 c35256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20274
  · exact u20275

def b35257 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 194 13 280 49 230 198 198 454), lower := (rows 35 194 13 280 49 32 64 128 256), losses := [] }

theorem u35257 : Upper (D 7) (R 7) [34,192,9,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35258 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 194 13 280 50 229 197 197 453), lower := (rows 35 194 13 280 50 32 64 128 256), losses := [] }

theorem u35258 : Upper (D 7) (R 7) [34,192,9,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35259 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35259 : Upper (D 7) (R 7) [34,192,9,272,36] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,36] 13 (by decide) (choices 1) [1,2,64] r35259 c35259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20276
  · exact u20277
  · exact u20278

def r35260 : Route 9 := (fun mask => (mask,id))

def c35260 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35260 : Upper (D 7) (R 7) [34,192,9,272,65] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,65] 13 (by decide) (choices 1) [2,4,128] r35260 c35260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20279
  · exact u20280
  · exact u20281

def b35261 : PairBound 9 := { available := 165, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 194 13 280 82 165 229 165 421), lower := (rows 35 194 13 280 82 32 64 128 256), losses := [] }

theorem u35261 : Upper (D 7) (R 7) [34,192,9,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35262 : Route 9 := (fun mask => (mask,id))

def c35262 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35262 : Upper (D 7) (R 7) [34,192,9,272,68] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,68] 13 (by decide) (choices 1) [1,2,128] r35262 c35262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20282
  · exact u20283
  · exact u20284

def r35263 : Route 9 := (fun mask => (mask,id))

def c35263 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35263 : Upper (D 7) (R 7) [34,192,9,272,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,96] 13 (by decide) (choices 1) [1,2,4,128] r35263 c35263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20285
  · exact u20286
  · exact u20287
  · exact u20288

def b35264 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 280 208 39 103 167 295), lower := (rows 35 194 13 280 208 32 64 128 256), losses := [] }

theorem u35264 : Upper (D 7) (R 7) [34,192,9,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35265 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35265 : Upper (D 7) (R 7) [34,192,9,288,6] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288,6] 13 (by decide) (choices 1) [1,16,64] r35265 c35265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20289
  · exact u20290
  · exact u20291

def r35266 : Route 9 := (fun mask => (mask,id))

def c35266 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35266 : Upper (D 7) (R 7) [34,192,9,288,65] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288,65] 13 (by decide) (choices 1) [2,4,16,128] r35266 c35266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20292
  · exact u20293
  · exact u20294
  · exact u20295

def b35267 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 194 13 296 82 181 213 149 405), lower := (rows 35 194 13 296 82 32 64 128 256), losses := [] }

theorem u35267 : Upper (D 7) (R 7) [34,192,9,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35268 : Route 9 := (fun mask => (mask,id))

def c35268 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35268 : Upper (D 7) (R 7) [34,192,9,288,68] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288,68] 13 (by decide) (choices 1) [1,2,16,128] r35268 c35268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20296
  · exact u20297
  · exact u20298
  · exact u20299

def b35269 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 296 208 55 87 151 279), lower := (rows 35 194 13 296 208 32 64 128 256), losses := [] }

theorem u35269 : Upper (D 7) (R 7) [34,192,9,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35270 : Route 9 := (fun mask => (mask,id))

def c35270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35270 : Upper (D 7) (R 7) [34,192,9,320,6] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,6] 13 (by decide) (choices 1) [1,16,128] r35270 c35270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20300
  · exact u20301
  · exact u20302

def b35271 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 194 13 328 49 182 214 150 406), lower := (rows 35 194 13 328 49 32 64 128 256), losses := [] }

theorem u35271 : Upper (D 7) (R 7) [34,192,9,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35272 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 194 13 328 50 181 213 149 405), lower := (rows 35 194 13 328 50 32 64 128 256), losses := [] }

theorem u35272 : Upper (D 7) (R 7) [34,192,9,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35273 : Route 9 := (fun mask => (mask,id))

def c35273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35273 : Upper (D 7) (R 7) [34,192,9,320,36] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,36] 13 (by decide) (choices 1) [1,2,16,128] r35273 c35273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20303
  · exact u20304
  · exact u20305
  · exact u20306

def r35274 : Route 9 := (fun mask => (mask,id))

def c35274 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35274 : Upper (D 7) (R 7) [34,192,9,320,129] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,129] 13 (by decide) (choices 1) [2,4,16] r35274 c35274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20307
  · exact u20308
  · exact u20309

def b35275 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 35 194 13 328 146 53 117 181 309), lower := (rows 35 194 13 328 146 32 64 128 256), losses := [] }

theorem u35275 : Upper (D 7) (R 7) [34,192,9,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35276 : Route 9 := (fun mask => (mask,id))

def c35276 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35276 : Upper (D 7) (R 7) [34,192,9,320,132] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,132] 13 (by decide) (choices 1) [1,2,16] r35276 c35276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20310
  · exact u20311
  · exact u20312

def r35277 : Route 9 := (fun mask => (mask,id))

def c35277 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35277 : Upper (D 7) (R 7) [34,192,9,320,160] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,160] 13 (by decide) (choices 1) [1,2,4,16] r35277 c35277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20313
  · exact u20314
  · exact u20315
  · exact u20316

def b35278 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 14 28 49 481 449 449 449), lower := (rows 35 194 14 28 49 32 64 128 256), losses := [] }

theorem u35278 : Upper (D 7) (R 7) [34,192,10,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35279 : Route 9 := (fun mask => (mask,id))

def c35279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u35279 : Upper (D 7) (R 7) [34,192,10,20,65] 13 := by
  apply FastRouting.sound _ _ [34,192,10,20,65] 13 (by decide) (choices 1) [1,128,256] r35279 c35279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20317
  · exact u20318
  · exact u20319

#print axioms u35279
end Delivery.IrregularNine14.P07
