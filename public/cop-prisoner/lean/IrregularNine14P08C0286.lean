import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0104

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17160 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 44 73 146 240 240 240 496), lower := (rows 289 7 44 73 146 32 64 128 256), losses := [] }

theorem u17160 : Upper (D 8) (R 8) [288,5,40,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17161 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 44 73 176 242 210 210 466), lower := (rows 289 7 44 73 176 32 64 128 256), losses := [] }

theorem u17161 : Upper (D 8) (R 8) [288,5,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17162 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 44 73 208 178 242 178 434), lower := (rows 289 7 44 73 208 32 64 128 256), losses := [] }

theorem u17162 : Upper (D 8) (R 8) [288,5,40,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17163 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 44 74 49 240 208 208 464), lower := (rows 289 7 44 74 49 32 64 128 256), losses := [] }

theorem u17163 : Upper (D 8) (R 8) [288,5,40,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17164 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 74 81 176 240 176 432), lower := (rows 289 7 44 74 81 32 64 128 256), losses := [] }

theorem u17164 : Upper (D 8) (R 8) [288,5,40,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17165 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 74 112 177 209 145 401), lower := (rows 289 7 44 74 112 32 64 128 256), losses := [] }

theorem u17165 : Upper (D 8) (R 8) [288,5,40,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17166 : Route 9 := (fun mask => (mask,id))

def c17166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17166 : Upper (D 8) (R 8) [288,5,40,66,129] 13 := by
  apply FastRouting.sound _ _ [288,5,40,66,129] 13 (by decide) (choices 1) [16,64,128] r17166 c17166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6256
  · exact u6257
  · exact u6258

def r17167 : Route 9 := (fun mask => (mask,id))

def c17167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17167 : Upper (D 8) (R 8) [288,5,40,66,160] 13 := by
  apply FastRouting.sound _ _ [288,5,40,66,160] 13 (by decide) (choices 1) [1,16,64,128] r17167 c17167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6259
  · exact u6260
  · exact u6261
  · exact u6262

def b17168 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 74 208 177 241 177 433), lower := (rows 289 7 44 74 208 32 64 128 256), losses := [] }

theorem u17168 : Upper (D 8) (R 8) [288,5,40,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17169 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 44 88 49 226 194 194 450), lower := (rows 289 7 44 88 49 32 64 128 256), losses := [] }

theorem u17169 : Upper (D 8) (R 8) [288,5,40,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17170 : PairBound 9 := { available := 193, camps := [], pairs := [(3,5)], upper := (rows 289 7 44 88 50 225 193 193 449), lower := (rows 289 7 44 88 50 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 67 131 259), good := (rows 449 455 12 88 474 0 64 128 256) }] }

theorem u17170 : Upper (D 8) (R 8) [288,5,40,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17171 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 88 81 162 226 162 418), lower := (rows 289 7 44 88 81 32 64 128 256), losses := [] }

theorem u17171 : Upper (D 8) (R 8) [288,5,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17172 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 88 82 161 225 161 417), lower := (rows 289 7 44 88 82 32 64 128 256), losses := [] }

theorem u17172 : Upper (D 8) (R 8) [288,5,40,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17173 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 44 88 112 163 195 131 387), lower := (rows 289 7 44 88 112 32 64 128 256), losses := [] }

theorem u17173 : Upper (D 8) (R 8) [288,5,40,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17173 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17174 : Route 9 := (fun mask => (mask,id))

def c17174 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17174 : Upper (D 8) (R 8) [288,5,40,80,129] 13 := by
  apply FastRouting.sound _ _ [288,5,40,80,129] 13 (by decide) (choices 1) [2,64,128] r17174 c17174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6263
  · exact u6264
  · exact u6265

def r17175 : Route 9 := (fun mask => (mask,id))

def c17175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17175 : Upper (D 8) (R 8) [288,5,40,80,130] 13 := by
  apply FastRouting.sound _ _ [288,5,40,80,130] 13 (by decide) (choices 1) [1,64,128] r17175 c17175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6266
  · exact u6267
  · exact u6268

def r17176 : Route 9 := (fun mask => (mask,id))

def c17176 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17176 : Upper (D 8) (R 8) [288,5,40,80,160] 13 := by
  apply FastRouting.sound _ _ [288,5,40,80,160] 13 (by decide) (choices 1) [1,2,64,128] r17176 c17176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6269
  · exact u6270
  · exact u6271
  · exact u6272

def b17177 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 88 208 163 227 163 419), lower := (rows 289 7 44 88 208 32 64 128 256), losses := [] }

theorem u17177 : Upper (D 8) (R 8) [288,5,40,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17178 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 44 104 81 178 210 146 402), lower := (rows 289 7 44 104 81 32 64 128 256), losses := [] }

theorem u17178 : Upper (D 8) (R 8) [288,5,40,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17179 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 44 104 82 177 209 145 401), lower := (rows 289 7 44 104 82 32 64 128 256), losses := [] }

theorem u17179 : Upper (D 8) (R 8) [288,5,40,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17180 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 44 104 145 242 210 210 466), lower := (rows 289 7 44 104 145 32 64 128 256), losses := [] }

theorem u17180 : Upper (D 8) (R 8) [288,5,40,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17181 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 44 104 146 241 209 209 465), lower := (rows 289 7 44 104 146 32 64 128 256), losses := [] }

theorem u17181 : Upper (D 8) (R 8) [288,5,40,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17182 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 44 104 208 179 211 147 403), lower := (rows 289 7 44 104 208 32 64 128 256), losses := [] }

theorem u17182 : Upper (D 8) (R 8) [288,5,40,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17183 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 44 200 49 242 210 210 466), lower := (rows 289 7 44 200 49 32 64 128 256), losses := [] }

theorem u17183 : Upper (D 8) (R 8) [288,5,40,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17184 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c17184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17184 : Upper (D 8) (R 8) [288,5,40,192,34] 13 := by
  apply FastRouting.sound _ _ [288,5,40,192,34] 13 (by decide) (choices 1) [1,16,64] r17184 c17184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6273
  · exact u6274
  · exact u6275

def r17185 : Route 9 := (fun mask => (mask,id))

def c17185 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17185 : Upper (D 8) (R 8) [288,5,40,192,65] 13 := by
  apply FastRouting.sound _ _ [288,5,40,192,65] 13 (by decide) (choices 1) [2,16,128] r17185 c17185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6276
  · exact u6277
  · exact u6278

def b17186 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 200 82 177 241 177 433), lower := (rows 289 7 44 200 82 32 64 128 256), losses := [] }

theorem u17186 : Upper (D 8) (R 8) [288,5,40,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17187 : Route 9 := (fun mask => (mask,id))

def c17187 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17187 : Upper (D 8) (R 8) [288,5,40,192,96] 13 := by
  apply FastRouting.sound _ _ [288,5,40,192,96] 13 (by decide) (choices 1) [1,2,16,128] r17187 c17187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6279
  · exact u6280
  · exact u6281
  · exact u6282

def b17188 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 44 200 208 51 115 179 307), lower := (rows 289 7 44 200 208 32 64 128 256), losses := [] }

theorem u17188 : Upper (D 8) (R 8) [288,5,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17189 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 56 224 224 224 480), lower := (rows 289 7 69 26 56 32 64 128 256), losses := [] }

theorem u17189 : Upper (D 8) (R 8) [288,5,65,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17190 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 88 160 224 160 416), lower := (rows 289 7 69 26 88 32 64 128 256), losses := [] }

theorem u17190 : Upper (D 8) (R 8) [288,5,65,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17191 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 112 168 232 168 424), lower := (rows 289 7 69 26 112 32 64 128 256), losses := [] }

theorem u17191 : Upper (D 8) (R 8) [288,5,65,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17192 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 152 224 224 224 480), lower := (rows 289 7 69 26 152 32 64 128 256), losses := [] }

theorem u17192 : Upper (D 8) (R 8) [288,5,65,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17193 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 176 232 232 232 488), lower := (rows 289 7 69 26 176 32 64 128 256), losses := [] }

theorem u17193 : Upper (D 8) (R 8) [288,5,65,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17194 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 208 168 232 168 424), lower := (rows 289 7 69 26 208 32 64 128 256), losses := [] }

theorem u17194 : Upper (D 8) (R 8) [288,5,65,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17195 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 42 88 176 240 176 432), lower := (rows 289 7 69 42 88 32 64 128 256), losses := [] }

theorem u17195 : Upper (D 8) (R 8) [288,5,65,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17196 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 42 112 184 216 152 408), lower := (rows 289 7 69 42 112 32 64 128 256), losses := [] }

theorem u17196 : Upper (D 8) (R 8) [288,5,65,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17197 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 42 152 240 240 240 496), lower := (rows 289 7 69 42 152 32 64 128 256), losses := [] }

theorem u17197 : Upper (D 8) (R 8) [288,5,65,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17198 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 42 176 248 216 216 472), lower := (rows 289 7 69 42 176 32 64 128 256), losses := [] }

theorem u17198 : Upper (D 8) (R 8) [288,5,65,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17199 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 42 208 184 248 184 440), lower := (rows 289 7 69 42 208 32 64 128 256), losses := [] }

theorem u17199 : Upper (D 8) (R 8) [288,5,65,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17200 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 56 82 168 232 168 424), lower := (rows 289 7 69 56 82 32 64 128 256), losses := [] }

theorem u17200 : Upper (D 8) (R 8) [288,5,65,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17201 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 69 56 88 162 226 162 418), lower := (rows 289 7 69 56 88 32 64 128 256), losses := [] }

theorem u17201 : Upper (D 8) (R 8) [288,5,65,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17202 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 56 146 232 232 232 488), lower := (rows 289 7 69 56 146 32 64 128 256), losses := [] }

theorem u17202 : Upper (D 8) (R 8) [288,5,65,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17203 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 56 152 226 226 226 482), lower := (rows 289 7 69 56 152 32 64 128 256), losses := [] }

theorem u17203 : Upper (D 8) (R 8) [288,5,65,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17203 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17204 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 56 208 170 234 170 426), lower := (rows 289 7 69 56 208 32 64 128 256), losses := [] }

theorem u17204 : Upper (D 8) (R 8) [288,5,65,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17205 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 74 152 176 240 176 432), lower := (rows 289 7 69 74 152 32 64 128 256), losses := [] }

theorem u17205 : Upper (D 8) (R 8) [288,5,65,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17206 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 74 176 184 248 184 440), lower := (rows 289 7 69 74 176 32 64 128 256), losses := [] }

theorem u17206 : Upper (D 8) (R 8) [288,5,65,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17207 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 88 146 168 232 168 424), lower := (rows 289 7 69 88 146 32 64 128 256), losses := [] }

theorem u17207 : Upper (D 8) (R 8) [288,5,65,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17208 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 69 88 152 162 226 162 418), lower := (rows 289 7 69 88 152 32 64 128 256), losses := [] }

theorem u17208 : Upper (D 8) (R 8) [288,5,65,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17209 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 88 176 170 234 170 426), lower := (rows 289 7 69 88 176 32 64 128 256), losses := [] }

theorem u17209 : Upper (D 8) (R 8) [288,5,65,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17210 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 104 146 184 248 184 440), lower := (rows 289 7 69 104 146 32 64 128 256), losses := [] }

theorem u17210 : Upper (D 8) (R 8) [288,5,65,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17211 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 104 152 178 242 178 434), lower := (rows 289 7 69 104 152 32 64 128 256), losses := [] }

theorem u17211 : Upper (D 8) (R 8) [288,5,65,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17211 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17212 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 104 176 186 218 154 410), lower := (rows 289 7 69 104 176 32 64 128 256), losses := [] }

theorem u17212 : Upper (D 8) (R 8) [288,5,65,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17213 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 138 176 120 120 248 376), lower := (rows 289 7 69 138 176 32 64 128 256), losses := [] }

theorem u17213 : Upper (D 8) (R 8) [288,5,65,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17214 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 138 208 56 120 184 312), lower := (rows 289 7 69 138 208 32 64 128 256), losses := [] }

theorem u17214 : Upper (D 8) (R 8) [288,5,65,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17214 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17215 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 168 208 58 122 186 314), lower := (rows 289 7 69 168 208 32 64 128 256), losses := [] }

theorem u17215 : Upper (D 8) (R 8) [288,5,65,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17216 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 393, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 25 112 168 232 168 424), lower := (rows 289 7 70 25 112 32 64 128 256), losses := [] }

theorem u17216 : Upper (D 8) (R 8) [288,5,66,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17217 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 70 25 152 224 224 224 480), lower := (rows 289 7 70 25 152 32 64 128 256), losses := [] }

theorem u17217 : Upper (D 8) (R 8) [288,5,66,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17218 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 70 25 176 232 232 232 488), lower := (rows 289 7 70 25 176 32 64 128 256), losses := [] }

theorem u17218 : Upper (D 8) (R 8) [288,5,66,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17219 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 25 208 168 232 168 424), lower := (rows 289 7 70 25 208 32 64 128 256), losses := [] }

theorem u17219 : Upper (D 8) (R 8) [288,5,66,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17219 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17219
end Delivery.IrregularNine14.P08
