import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0144
import IrregularNine14P07C0145

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25260 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 194 76 11 304 48 195 131 387), lower := (rows 37 194 76 11 304 48 64 128 256), losses := [] }

theorem u25260 : Upper (D 7) (R 7) [36,192,72,3,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25260 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25261 : Route 9 := (fun mask => (mask,id))

def c25261 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25261 : Upper (D 7) (R 7) [36,192,72,3,288,128] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,288,128] 13 (by decide) (choices 1) [1,2,16] r25261 c25261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8659
  · exact u8660
  · exact u8661

def b25262 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 76 11 400 33 114 178 306), lower := (rows 37 194 76 11 400 33 64 128 256), losses := [] }

theorem u25262 : Upper (D 7) (R 7) [36,192,72,3,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25263 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 400, targets := 2 }], pairs := [(0,7),(2,7),(3,7),(4,1)], upper := (rows 37 194 76 11 400 34 113 177 305), lower := (rows 37 194 76 11 400 34 64 128 256), losses := [] }

theorem u25263 : Upper (D 7) (R 7) [36,192,72,3,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25264 : Route 9 := (fun mask => (mask,id))

def c25264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25264 : Upper (D 7) (R 7) [36,192,72,3,384,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,384,16] 13 (by decide) (choices 1) [1,2,32] r25264 c25264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8662
  · exact u8663
  · exact u8664

def b25265 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 76 25 50 33 450 386 386), lower := (rows 37 194 76 25 50 33 64 128 256), losses := [] }

theorem u25265 : Upper (D 7) (R 7) [36,192,72,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25266 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 76 25 50 34 449 385 385), lower := (rows 37 194 76 25 50 34 64 128 256), losses := [] }

theorem u25266 : Upper (D 7) (R 7) [36,192,72,17,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25267 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 76 25 50 160 323 387 259), lower := (rows 37 194 76 25 50 160 64 128 256), losses := [] }

theorem u25267 : Upper (D 7) (R 7) [36,192,72,17,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25268 : Route 9 := (fun mask => (mask,id))

def c25268 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25268 : Upper (D 7) (R 7) [36,192,72,17,34,256] 13 := by
  apply FastRouting.sound _ _ [36,192,72,17,34,256] 13 (by decide) (choices 1) [1,2,128] r25268 c25268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8665
  · exact u8666
  · exact u8667

def b25269 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 61, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 194 76 25 176 33 322 386 258), lower := (rows 37 194 76 25 176 33 64 128 256), losses := [] }

theorem u25269 : Upper (D 7) (R 7) [36,192,72,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25270 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(4,0),(4,6)], upper := (rows 37 194 76 25 176 34 323 387 259), lower := (rows 37 194 76 25 176 34 64 128 256), losses := [] }

theorem u25270 : Upper (D 7) (R 7) [36,192,72,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25271 : Route 9 := (fun mask => (mask,id))

def c25271 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25271 : Upper (D 7) (R 7) [36,192,72,17,160,256] 13 := by
  apply FastRouting.sound _ _ [36,192,72,17,160,256] 13 (by decide) (choices 1) [1,2] r25271 c25271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8668
  · exact u8669

def b25272 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 76 25 274 33 226 162 418), lower := (rows 37 194 76 25 274 33 64 128 256), losses := [] }

theorem u25272 : Upper (D 7) (R 7) [36,192,72,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25273 : Route 9 := (fun mask => (mask,id))

def c25273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25273 : Upper (D 7) (R 7) [36,192,72,17,258,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,17,258,2] 13 (by decide) (choices 1) [1,32,128] r25273 c25273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8670
  · exact u8671
  · exact u8672

def r25274 : Route 9 := (fun mask => (mask,id))

def c25274 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25274 : Upper (D 7) (R 7) [36,192,72,17,258,128] 13 := by
  apply FastRouting.sound _ _ [36,192,72,17,258,128] 13 (by decide) (choices 1) [1,2,32] r25274 c25274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8673
  · exact u8674
  · exact u8675

def b25275 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 76 25 304 33 194 130 386), lower := (rows 37 194 76 25 304 33 64 128 256), losses := [] }

theorem u25275 : Upper (D 7) (R 7) [36,192,72,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25276 : Route 9 := (fun mask => (mask,id))

def c25276 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25276 : Upper (D 7) (R 7) [36,192,72,17,288,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,17,288,2] 13 (by decide) (choices 1) [1,2,128] r25276 c25276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8676
  · exact u8677
  · exact u8678

def r25277 : Route 9 := (fun mask => (mask,id))

def c25277 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25277 : Upper (D 7) (R 7) [36,192,72,17,288,128] 13 := by
  apply FastRouting.sound _ _ [36,192,72,17,288,128] 13 (by decide) (choices 1) [1,2] r25277 c25277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8679
  · exact u8680

def b25278 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 76 25 400 33 98 162 290), lower := (rows 37 194 76 25 400 33 64 128 256), losses := [] }

theorem u25278 : Upper (D 7) (R 7) [36,192,72,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25279 : Route 9 := (fun mask => (mask,id))

def c25279 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25279 : Upper (D 7) (R 7) [36,192,72,17,384,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,17,384,2] 13 (by decide) (choices 1) [1,2,32] r25279 c25279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8681
  · exact u8682
  · exact u8683

def b25280 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 76 26 145 33 354 418 290), lower := (rows 37 194 76 26 145 33 64 128 256), losses := [] }

theorem u25280 : Upper (D 7) (R 7) [36,192,72,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25281 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 0, region := 400, targets := 2 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,7),(2,7),(4,1),(4,6)], upper := (rows 37 194 76 26 145 34 353 417 289), lower := (rows 37 194 76 26 145 34 64 128 256), losses := [] }

theorem u25281 : Upper (D 7) (R 7) [36,192,72,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25282 : Route 9 := (fun mask => (mask,id))

def c25282 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25282 : Upper (D 7) (R 7) [36,192,72,18,129,256] 13 := by
  apply FastRouting.sound _ _ [36,192,72,18,129,256] 13 (by decide) (choices 1) [1,2,32] r25282 c25282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8684
  · exact u8685
  · exact u8686

def b25283 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 76 26 176 33 323 387 259), lower := (rows 37 194 76 26 176 33 64 128 256), losses := [] }

theorem u25283 : Upper (D 7) (R 7) [36,192,72,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25284 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 60, targets := 1 },{ cop := 1, region := 56, targets := 64 }], pairs := [(2,0),(3,0),(3,6),(4,0)], upper := (rows 37 194 76 26 176 34 321 385 257), lower := (rows 37 194 76 26 176 34 64 128 256), losses := [] }

theorem u25284 : Upper (D 7) (R 7) [36,192,72,18,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25285 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,7),(1,5),(2,7)], upper := (rows 37 194 76 26 176 288 67 131 259), lower := (rows 37 194 76 26 176 288 64 128 256), losses := [] }

theorem u25285 : Upper (D 7) (R 7) [36,192,72,18,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25285 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25286 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 76 26 273 33 226 162 418), lower := (rows 37 194 76 26 273 33 64 128 256), losses := [] }

theorem u25286 : Upper (D 7) (R 7) [36,192,72,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25287 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 2 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 37 194 76 26 273 34 225 161 417), lower := (rows 37 194 76 26 273 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 21 42 0 133 261), good := (rows 437 162 445 58 401 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 42 64 0 256), good := (rows 37 98 109 58 273 34 64 0 256) }] }

theorem u25287 : Upper (D 7) (R 7) [36,192,72,18,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25288 : Route 9 := (fun mask => (mask,id))

def c25288 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25288 : Upper (D 7) (R 7) [36,192,72,18,257,128] 13 := by
  apply FastRouting.sound _ _ [36,192,72,18,257,128] 13 (by decide) (choices 1) [1,2,32] r25288 c25288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8687
  · exact u8688
  · exact u8689

def b25289 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 76 26 304 33 195 131 387), lower := (rows 37 194 76 26 304 33 64 128 256), losses := [] }

theorem u25289 : Upper (D 7) (R 7) [36,192,72,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25290 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 2 },{ cop := 0, region := 194, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,6),(1,5),(4,1),(4,6)], upper := (rows 37 194 76 26 304 34 193 129 385), lower := (rows 37 194 76 26 304 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 21 42 0 133 261), good := (rows 437 162 445 58 304 34 0 128 256) }] }

theorem u25290 : Upper (D 7) (R 7) [36,192,72,18,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25291 : Route 9 := (fun mask => (mask,id))

def c25291 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25291 : Upper (D 7) (R 7) [36,192,72,18,288,128] 13 := by
  apply FastRouting.sound _ _ [36,192,72,18,288,128] 13 (by decide) (choices 1) [1,2] r25291 c25291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8690
  · exact u8691

def b25292 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,7)], upper := (rows 37 194 76 26 400 33 99 163 291), lower := (rows 37 194 76 26 400 33 64 128 256), losses := [] }

theorem u25292 : Upper (D 7) (R 7) [36,192,72,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25293 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 400, targets := 2 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,7),(2,7),(4,1),(4,6)], upper := (rows 37 194 76 26 400 34 97 161 289), lower := (rows 37 194 76 26 400 34 64 128 256), losses := [] }

theorem u25293 : Upper (D 7) (R 7) [36,192,72,18,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25294 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 76 42 19 33 464 400 400), lower := (rows 37 194 76 42 19 33 64 128 256), losses := [] }

theorem u25294 : Upper (D 7) (R 7) [36,192,72,34,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25295 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 76 42 19 48 449 385 385), lower := (rows 37 194 76 42 19 48 64 128 256), losses := [] }

theorem u25295 : Upper (D 7) (R 7) [36,192,72,34,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25295 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25296 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 37 194 76 42 19 160 337 401 273), lower := (rows 37 194 76 42 19 160 64 128 256), losses := [] }

theorem u25296 : Upper (D 7) (R 7) [36,192,72,34,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25297 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 37 194 76 42 19 288 209 145 401), lower := (rows 37 194 76 42 19 288 64 128 256), losses := [] }

theorem u25297 : Upper (D 7) (R 7) [36,192,72,34,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25297 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25298 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 37 194 76 42 145 33 338 402 274), lower := (rows 37 194 76 42 145 33 64 128 256), losses := [] }

theorem u25298 : Upper (D 7) (R 7) [36,192,72,34,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25299 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 469, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 194 76 42 145 34 337 401 273), lower := (rows 37 194 76 42 145 34 64 128 256), losses := [] }

theorem u25299 : Upper (D 7) (R 7) [36,192,72,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25300 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 3, region := 325, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 37 194 76 42 145 48 323 387 259), lower := (rows 37 194 76 42 145 48 64 128 256), losses := [] }

theorem u25300 : Upper (D 7) (R 7) [36,192,72,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25300 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25301 : Route 9 := (fun mask => (mask,id))

def c25301 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25301 : Upper (D 7) (R 7) [36,192,72,34,129,256] 13 := by
  apply FastRouting.sound _ _ [36,192,72,34,129,256] 13 (by decide) (choices 1) [1,2,16] r25301 c25301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8692
  · exact u8693
  · exact u8694

def b25302 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 37 194 76 42 273 33 210 146 402), lower := (rows 37 194 76 42 273 33 64 128 256), losses := [] }

theorem u25302 : Upper (D 7) (R 7) [36,192,72,34,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25303 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 469, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 194 76 42 273 34 209 145 401), lower := (rows 37 194 76 42 273 34 64 128 256), losses := [] }

theorem u25303 : Upper (D 7) (R 7) [36,192,72,34,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25304 : Route 9 := (fun mask => (mask,id))

def c25304 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25304 : Upper (D 7) (R 7) [36,192,72,34,257,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,34,257,16] 13 (by decide) (choices 1) [1,2,128] r25304 c25304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8695
  · exact u8696
  · exact u8697

def b25305 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 37 194 76 42 273 160 83 147 275), lower := (rows 37 194 76 42 273 160 64 128 256), losses := [] }

theorem u25305 : Upper (D 7) (R 7) [36,192,72,34,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25306 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 37 194 76 42 274 33 209 145 401), lower := (rows 37 194 76 42 274 33 64 128 256), losses := [] }

theorem u25306 : Upper (D 7) (R 7) [36,192,72,34,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25307 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 37 194 76 42 274 48 193 129 385), lower := (rows 37 194 76 42 274 48 64 128 256), losses := [] }

theorem u25307 : Upper (D 7) (R 7) [36,192,72,34,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25307 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25308 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 37 194 76 42 274 160 81 145 273), lower := (rows 37 194 76 42 274 160 64 128 256), losses := [] }

theorem u25308 : Upper (D 7) (R 7) [36,192,72,34,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25309 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 37 194 76 42 400 33 83 147 275), lower := (rows 37 194 76 42 400 33 64 128 256), losses := [] }

theorem u25309 : Upper (D 7) (R 7) [36,192,72,34,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25310 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 469, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 194 76 42 400 34 81 145 273), lower := (rows 37 194 76 42 400 34 64 128 256), losses := [] }

theorem u25310 : Upper (D 7) (R 7) [36,192,72,34,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25311 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 37 194 76 42 400 48 67 131 259), lower := (rows 37 194 76 42 400 48 64 128 256), losses := [] }

theorem u25311 : Upper (D 7) (R 7) [36,192,72,34,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25311 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25312 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 61, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 194 76 56 145 33 322 386 258), lower := (rows 37 194 76 56 145 33 64 128 256), losses := [] }

theorem u25312 : Upper (D 7) (R 7) [36,192,72,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25313 : Route 9 := (fun mask => (mask,id))

def c25313 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u25313 : Upper (D 7) (R 7) [36,192,72,48,129,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,48,129,2] 13 (by decide) (choices 1) [1,2,256] r25313 c25313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8698
  · exact u8699
  · exact u8700

def b25314 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 76 56 145 288 67 131 259), lower := (rows 37 194 76 56 145 288 64 128 256), losses := [{ target := 5, region := (rows 1 27 12 8 17 0 81 145 273), good := (rows 471 194 78 478 467 256 64 128 256) }] }

theorem u25314 : Upper (D 7) (R 7) [36,192,72,48,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25314 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25315 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 76 56 273 33 194 130 386), lower := (rows 37 194 76 56 273 33 64 128 256), losses := [] }

theorem u25315 : Upper (D 7) (R 7) [36,192,72,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25316 : Route 9 := (fun mask => (mask,id))

def c25316 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25316 : Upper (D 7) (R 7) [36,192,72,48,257,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,48,257,2] 13 (by decide) (choices 1) [1,2,128] r25316 c25316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8701
  · exact u8702
  · exact u8703

def r25317 : Route 9 := (fun mask => (mask,id))

def c25317 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25317 : Upper (D 7) (R 7) [36,192,72,48,257,128] 13 := by
  apply FastRouting.sound _ _ [36,192,72,48,257,128] 13 (by decide) (choices 1) [1,2] r25317 c25317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8704
  · exact u8705

def b25318 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 76 56 274 33 195 131 387), lower := (rows 37 194 76 56 274 33 64 128 256), losses := [] }

theorem u25318 : Upper (D 7) (R 7) [36,192,72,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25319 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(3,7)], upper := (rows 37 194 76 56 274 34 193 129 385), lower := (rows 37 194 76 56 274 34 64 128 256), losses := [] }

theorem u25319 : Upper (D 7) (R 7) [36,192,72,48,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u25319
end Delivery.IrregularNine14.P07
