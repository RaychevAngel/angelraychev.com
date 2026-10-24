import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0480
import IrregularNine14P07C0481
import IrregularNine14P07C0482

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40260 : Route 9 := (fun mask => (mask,id))

def c40260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40260 : Upper (D 7) (R 7) [96,260,9,130,34] 13 := by
  apply FastRouting.sound _ _ [96,260,9,130,34] 13 (by decide) (choices 1) [1,16,64,128] r40260 c40260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28835
  · exact u28836
  · exact u28837
  · exact u28838

def b40261 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 13 138 112 179 211 147 403), lower := (rows 97 262 13 138 112 32 64 128 256), losses := [] }

theorem u40261 : Upper (D 7) (R 7) [96,260,9,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40262 : Route 9 := (fun mask => (mask,id))

def c40262 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40262 : Upper (D 7) (R 7) [96,260,9,130,129] 13 := by
  apply FastRouting.sound _ _ [96,260,9,130,129] 13 (by decide) (choices 1) [2,16,64] r40262 c40262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28839
  · exact u28840
  · exact u28841

def b40263 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 97 262 13 138 146 113 113 241 369), lower := (rows 97 262 13 138 146 32 64 128 256), losses := [] }

theorem u40263 : Upper (D 7) (R 7) [96,260,9,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40264 : Route 9 := (fun mask => (mask,id))

def c40264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40264 : Upper (D 7) (R 7) [96,260,9,130,160] 13 := by
  apply FastRouting.sound _ _ [96,260,9,130,160] 13 (by decide) (choices 1) [1,2,16,64] r40264 c40264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28842
  · exact u28843
  · exact u28844
  · exact u28845

def r40265 : Route 9 := (fun mask => (mask,id))

def c40265 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40265 : Upper (D 7) (R 7) [96,260,9,144,3] 13 := by
  apply FastRouting.sound _ _ [96,260,9,144,3] 13 (by decide) (choices 1) [2,64,128] r40265 c40265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28846
  · exact u28847
  · exact u28848

def b40266 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 262 13 152 49 226 194 194 450), lower := (rows 97 262 13 152 49 32 64 128 256), losses := [] }

theorem u40266 : Upper (D 7) (R 7) [96,260,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40267 : Route 9 := (fun mask => (mask,id))

def c40267 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40267 : Upper (D 7) (R 7) [96,260,9,144,34] 13 := by
  apply FastRouting.sound _ _ [96,260,9,144,34] 13 (by decide) (choices 1) [1,2,64,128] r40267 c40267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28849
  · exact u28850
  · exact u28851
  · exact u28852

def b40268 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 13 152 112 163 195 131 387), lower := (rows 97 262 13 152 112 32 64 128 256), losses := [] }

theorem u40268 : Upper (D 7) (R 7) [96,260,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40269 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 97 262 13 152 145 98 98 226 354), lower := (rows 97 262 13 152 145 32 64 128 256), losses := [] }

theorem u40269 : Upper (D 7) (R 7) [96,260,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40270 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 262 13 152 146 99 99 227 355), lower := (rows 97 262 13 152 146 32 64 128 256), losses := [] }

theorem u40270 : Upper (D 7) (R 7) [96,260,9,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40271 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 262 13 152 176 99 67 195 323), lower := (rows 97 262 13 152 176 32 64 128 256), losses := [] }

theorem u40271 : Upper (D 7) (R 7) [96,260,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40272 : Route 9 := (fun mask => (mask,id))

def c40272 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40272 : Upper (D 7) (R 7) [96,260,9,160,3] 13 := by
  apply FastRouting.sound _ _ [96,260,9,160,3] 13 (by decide) (choices 1) [2,16,64,128] r40272 c40272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28853
  · exact u28854
  · exact u28855
  · exact u28856

def b40273 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 13 168 81 178 210 146 402), lower := (rows 97 262 13 168 81 32 64 128 256), losses := [] }

theorem u40273 : Upper (D 7) (R 7) [96,260,9,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40274 : Route 9 := (fun mask => (mask,id))

def c40274 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40274 : Upper (D 7) (R 7) [96,260,9,160,66] 13 := by
  apply FastRouting.sound _ _ [96,260,9,160,66] 13 (by decide) (choices 1) [1,2,16,128] r40274 c40274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28857
  · exact u28858
  · exact u28859
  · exact u28860

def r40275 : Route 9 := (fun mask => (mask,id))

def c40275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40275 : Upper (D 7) (R 7) [96,260,9,160,129] 13 := by
  apply FastRouting.sound _ _ [96,260,9,160,129] 13 (by decide) (choices 1) [2,16,64] r40275 c40275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28861
  · exact u28862
  · exact u28863

def r40276 : Route 9 := (fun mask => (mask,id))

def c40276 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40276 : Upper (D 7) (R 7) [96,260,9,160,130] 13 := by
  apply FastRouting.sound _ _ [96,260,9,160,130] 13 (by decide) (choices 1) [1,2,16,64] r40276 c40276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28864
  · exact u28865
  · exact u28866
  · exact u28867

def r40277 : Route 9 := (fun mask => (mask,id))

def c40277 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40277 : Upper (D 7) (R 7) [96,260,9,160,192] 13 := by
  apply FastRouting.sound _ _ [96,260,9,160,192] 13 (by decide) (choices 1) [1,2,16] r40277 c40277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28868
  · exact u28869
  · exact u28870

def b40278 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 97 262 14 25 19 224 224 224 480), lower := (rows 97 262 14 25 19 32 64 128 256), losses := [] }

theorem u40278 : Upper (D 7) (R 7) [96,260,10,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40279 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 97 262 14 25 49 226 194 194 450), lower := (rows 97 262 14 25 49 32 64 128 256), losses := [] }

theorem u40279 : Upper (D 7) (R 7) [96,260,10,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40280 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 4, region := 201, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(3,1)], upper := (rows 97 262 14 25 50 225 193 193 449), lower := (rows 97 262 14 25 50 32 64 128 256), losses := [] }

theorem u40280 : Upper (D 7) (R 7) [96,260,10,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40281 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 14 25 112 163 195 131 387), lower := (rows 97 262 14 25 112 32 64 128 256), losses := [] }

theorem u40281 : Upper (D 7) (R 7) [96,260,10,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40282 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 262 14 25 145 226 226 226 482), lower := (rows 97 262 14 25 145 32 64 128 256), losses := [] }

theorem u40282 : Upper (D 7) (R 7) [96,260,10,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40283 : Route 9 := (fun mask => (mask,id))

def c40283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40283 : Upper (D 7) (R 7) [96,260,10,17,130] 13 := by
  apply FastRouting.sound _ _ [96,260,10,17,130] 13 (by decide) (choices 1) [1,64,128] r40283 c40283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28871
  · exact u28872
  · exact u28873

def r40284 : Route 9 := (fun mask => (mask,id))

def c40284 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40284 : Upper (D 7) (R 7) [96,260,10,17,160] 13 := by
  apply FastRouting.sound _ _ [96,260,10,17,160] 13 (by decide) (choices 1) [1,2,64,128] r40284 c40284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28874
  · exact u28875
  · exact u28876
  · exact u28877

def b40285 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 233, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(3,1)], upper := (rows 97 262 14 56 19 225 193 193 449), lower := (rows 97 262 14 56 19 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 16 0 81 145 273), good := (rows 449 262 14 478 467 0 64 128 256) }] }

theorem u40285 : Upper (D 7) (R 7) [96,260,10,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40286 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 14 56 81 163 195 131 387), lower := (rows 97 262 14 56 81 32 64 128 256), losses := [] }

theorem u40286 : Upper (D 7) (R 7) [96,260,10,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40287 : Route 9 := (fun mask => (mask,id))

def c40287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40287 : Upper (D 7) (R 7) [96,260,10,48,66] 13 := by
  apply FastRouting.sound _ _ [96,260,10,48,66] 13 (by decide) (choices 1) [1,128] r40287 c40287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u28878
  · exact u28879

def r40288 : Route 9 := (fun mask => (mask,id))

def c40288 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40288 : Upper (D 7) (R 7) [96,260,10,48,129] 13 := by
  apply FastRouting.sound _ _ [96,260,10,48,129] 13 (by decide) (choices 1) [1,2,64,128] r40288 c40288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28880
  · exact u28881
  · exact u28882
  · exact u28883

def r40289 : Route 9 := (fun mask => (mask,id))

def c40289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40289 : Upper (D 7) (R 7) [96,260,10,48,130] 13 := by
  apply FastRouting.sound _ _ [96,260,10,48,130] 13 (by decide) (choices 1) [1,64,128] r40289 c40289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28884
  · exact u28885
  · exact u28886

def r40290 : Route 9 := (fun mask => (mask,id))

def c40290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40290 : Upper (D 7) (R 7) [96,260,10,48,192] 13 := by
  apply FastRouting.sound _ _ [96,260,10,48,192] 13 (by decide) (choices 1) [1,2,128] r40290 c40290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28887
  · exact u28888
  · exact u28889

def r40291 : Route 9 := (fun mask => (mask,id))

def c40291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40291 : Upper (D 7) (R 7) [96,260,10,129,3] 13 := by
  apply FastRouting.sound _ _ [96,260,10,129,3] 13 (by decide) (choices 1) [16,64,128] r40291 c40291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28890
  · exact u28891
  · exact u28892

def b40292 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 262 14 137 49 242 210 210 466), lower := (rows 97 262 14 137 49 32 64 128 256), losses := [] }

theorem u40292 : Upper (D 7) (R 7) [96,260,10,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40293 : Route 9 := (fun mask => (mask,id))

def c40293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40293 : Upper (D 7) (R 7) [96,260,10,129,34] 13 := by
  apply FastRouting.sound _ _ [96,260,10,129,34] 13 (by decide) (choices 1) [1,16,64,128] r40293 c40293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28893
  · exact u28894
  · exact u28895
  · exact u28896

def b40294 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 14 137 112 179 211 147 403), lower := (rows 97 262 14 137 112 32 64 128 256), losses := [] }

theorem u40294 : Upper (D 7) (R 7) [96,260,10,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40295 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 97 262 14 137 145 114 114 242 370), lower := (rows 97 262 14 137 145 32 64 128 256), losses := [] }

theorem u40295 : Upper (D 7) (R 7) [96,260,10,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40296 : Route 9 := (fun mask => (mask,id))

def c40296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40296 : Upper (D 7) (R 7) [96,260,10,129,130] 13 := by
  apply FastRouting.sound _ _ [96,260,10,129,130] 13 (by decide) (choices 1) [1,16,64] r40296 c40296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28897
  · exact u28898
  · exact u28899

def r40297 : Route 9 := (fun mask => (mask,id))

def c40297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40297 : Upper (D 7) (R 7) [96,260,10,129,160] 13 := by
  apply FastRouting.sound _ _ [96,260,10,129,160] 13 (by decide) (choices 1) [1,2,16,64] r40297 c40297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28900
  · exact u28901
  · exact u28902
  · exact u28903

def r40298 : Route 9 := (fun mask => (mask,id))

def c40298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40298 : Upper (D 7) (R 7) [96,260,10,144,3] 13 := by
  apply FastRouting.sound _ _ [96,260,10,144,3] 13 (by decide) (choices 1) [1,64,128] r40298 c40298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28904
  · exact u28905
  · exact u28906

def b40299 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 262 14 152 49 227 195 195 451), lower := (rows 97 262 14 152 49 32 64 128 256), losses := [] }

theorem u40299 : Upper (D 7) (R 7) [96,260,10,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40300 : Route 9 := (fun mask => (mask,id))

def c40300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40300 : Upper (D 7) (R 7) [96,260,10,144,34] 13 := by
  apply FastRouting.sound _ _ [96,260,10,144,34] 13 (by decide) (choices 1) [1,64,128] r40300 c40300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28907
  · exact u28908
  · exact u28909

def b40301 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 14 152 112 163 195 131 387), lower := (rows 97 262 14 152 112 32 64 128 256), losses := [] }

theorem u40301 : Upper (D 7) (R 7) [96,260,10,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40302 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 262 14 152 145 99 99 227 355), lower := (rows 97 262 14 152 145 32 64 128 256), losses := [] }

theorem u40302 : Upper (D 7) (R 7) [96,260,10,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40303 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 97 262 14 152 146 97 97 225 353), lower := (rows 97 262 14 152 146 32 64 128 256), losses := [] }

theorem u40303 : Upper (D 7) (R 7) [96,260,10,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40304 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 262 14 152 176 99 67 195 323), lower := (rows 97 262 14 152 176 32 64 128 256), losses := [] }

theorem u40304 : Upper (D 7) (R 7) [96,260,10,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40305 : Route 9 := (fun mask => (mask,id))

def c40305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40305 : Upper (D 7) (R 7) [96,260,10,160,3] 13 := by
  apply FastRouting.sound _ _ [96,260,10,160,3] 13 (by decide) (choices 1) [1,16,64,128] r40305 c40305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28910
  · exact u28911
  · exact u28912
  · exact u28913

def b40306 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 14 168 81 179 211 147 403), lower := (rows 97 262 14 168 81 32 64 128 256), losses := [] }

theorem u40306 : Upper (D 7) (R 7) [96,260,10,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40307 : Route 9 := (fun mask => (mask,id))

def c40307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40307 : Upper (D 7) (R 7) [96,260,10,160,66] 13 := by
  apply FastRouting.sound _ _ [96,260,10,160,66] 13 (by decide) (choices 1) [1,16,128] r40307 c40307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28914
  · exact u28915
  · exact u28916

def r40308 : Route 9 := (fun mask => (mask,id))

def c40308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40308 : Upper (D 7) (R 7) [96,260,10,160,129] 13 := by
  apply FastRouting.sound _ _ [96,260,10,160,129] 13 (by decide) (choices 1) [1,2,16,64] r40308 c40308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28917
  · exact u28918
  · exact u28919
  · exact u28920

def r40309 : Route 9 := (fun mask => (mask,id))

def c40309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40309 : Upper (D 7) (R 7) [96,260,10,160,130] 13 := by
  apply FastRouting.sound _ _ [96,260,10,160,130] 13 (by decide) (choices 1) [1,16,64] r40309 c40309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28921
  · exact u28922
  · exact u28923

def r40310 : Route 9 := (fun mask => (mask,id))

def c40310 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40310 : Upper (D 7) (R 7) [96,260,10,160,192] 13 := by
  apply FastRouting.sound _ _ [96,260,10,160,192] 13 (by decide) (choices 1) [1,2,16] r40310 c40310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28924
  · exact u28925
  · exact u28926

def b40311 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 20, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(4,5)], upper := (rows 97 262 28 11 19 224 224 224 480), lower := (rows 97 262 28 11 19 32 64 128 256), losses := [] }

theorem u40311 : Upper (D 7) (R 7) [96,260,24,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40312 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 262 28 11 49 226 194 194 450), lower := (rows 97 262 28 11 49 32 64 128 256), losses := [] }

theorem u40312 : Upper (D 7) (R 7) [96,260,24,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40313 : Route 9 := (fun mask => (mask,id))

def c40313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40313 : Upper (D 7) (R 7) [96,260,24,3,34] 13 := by
  apply FastRouting.sound _ _ [96,260,24,3,34] 13 (by decide) (choices 1) [1,64,128] r40313 c40313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28927
  · exact u28928
  · exact u28929

def b40314 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 28 11 112 163 195 131 387), lower := (rows 97 262 28 11 112 32 64 128 256), losses := [] }

theorem u40314 : Upper (D 7) (R 7) [96,260,24,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40315 : Route 9 := (fun mask => (mask,id))

def c40315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40315 : Upper (D 7) (R 7) [96,260,24,3,129] 13 := by
  apply FastRouting.sound _ _ [96,260,24,3,129] 13 (by decide) (choices 1) [2,64,128] r40315 c40315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28930
  · exact u28931
  · exact u28932

def r40316 : Route 9 := (fun mask => (mask,id))

def c40316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40316 : Upper (D 7) (R 7) [96,260,24,3,130] 13 := by
  apply FastRouting.sound _ _ [96,260,24,3,130] 13 (by decide) (choices 1) [1,64,128] r40316 c40316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28933
  · exact u28934
  · exact u28935

def r40317 : Route 9 := (fun mask => (mask,id))

def c40317 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40317 : Upper (D 7) (R 7) [96,260,24,3,160] 13 := by
  apply FastRouting.sound _ _ [96,260,24,3,160] 13 (by decide) (choices 1) [1,2,64,128] r40317 c40317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28936
  · exact u28937
  · exact u28938
  · exact u28939

def b40318 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 28 41 82 163 195 131 387), lower := (rows 97 262 28 41 82 32 64 128 256), losses := [] }

theorem u40318 : Upper (D 7) (R 7) [96,260,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40319 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 28 41 145 226 194 194 450), lower := (rows 97 262 28 41 145 32 64 128 256), losses := [] }

theorem u40319 : Upper (D 7) (R 7) [96,260,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u40319
end Delivery.IrregularNine14.P07
