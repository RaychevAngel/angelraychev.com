import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0185
import IrregularNine14P07C0186

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29280 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 81, targets := 128 },{ cop := 4, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(3,0),(4,7)], upper := (rows 97 262 140 42 82 160 81 145 273), lower := (rows 97 262 140 42 82 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 164 64 128 256), good := (rows 96 302 172 42 90 160 64 160 256) }] }

theorem u29280 : Upper (D 7) (R 7) [96,260,136,34,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29281 : Route 9 := (fun mask => (mask,id))

def c29281 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29281 : Upper (D 7) (R 7) [96,260,136,34,129,1] 13 := by
  apply FastRouting.sound _ _ [96,260,136,34,129,1] 13 (by decide) (choices 1) [2,16] r29281 c29281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11159
  · exact u11160

def b29282 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 262 140 42 145 34 81 209 337), lower := (rows 97 262 140 42 145 34 64 128 256), losses := [] }

theorem u29282 : Upper (D 7) (R 7) [96,260,136,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29283 : Route 9 := (fun mask => (mask,id))

def c29283 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29283 : Upper (D 7) (R 7) [96,260,136,34,129,16] 13 := by
  apply FastRouting.sound _ _ [96,260,136,34,129,16] 13 (by decide) (choices 1) [1,2] r29283 c29283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11161
  · exact u11162

def b29284 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 42 145 96 83 147 275), lower := (rows 97 262 140 42 145 96 64 128 256), losses := [] }

theorem u29284 : Upper (D 7) (R 7) [96,260,136,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29285 : Route 9 := (fun mask => (mask,id))

def c29285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29285 : Upper (D 7) (R 7) [96,260,136,34,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,136,34,130,1] 13 (by decide) (choices 1) [1,16] r29285 c29285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11163
  · exact u11164

def b29286 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 262 140 42 146 48 65 193 321), lower := (rows 97 262 140 42 146 48 64 128 256), losses := [] }

theorem u29286 : Upper (D 7) (R 7) [96,260,136,34,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29286 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29287 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 42 146 96 81 145 273), lower := (rows 97 262 140 42 146 96 64 128 256), losses := [] }

theorem u29287 : Upper (D 7) (R 7) [96,260,136,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29288 : Route 9 := (fun mask => (mask,id))

def c29288 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29288 : Upper (D 7) (R 7) [96,260,136,34,192,1] 13 := by
  apply FastRouting.sound _ _ [96,260,136,34,192,1] 13 (by decide) (choices 1) [1,2,16] r29288 c29288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11165
  · exact u11166
  · exact u11167

def b29289 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 262 140 42 208 34 81 145 273), lower := (rows 97 262 140 42 208 34 64 128 256), losses := [] }

theorem u29289 : Upper (D 7) (R 7) [96,260,136,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29290 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 140 42 208 48 67 131 259), lower := (rows 97 262 140 42 208 48 64 128 256), losses := [] }

theorem u29290 : Upper (D 7) (R 7) [96,260,136,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29290 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29291 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 97 262 140 56 19 33 194 194 450), lower := (rows 97 262 140 56 19 33 64 128 256), losses := [] }

theorem u29291 : Upper (D 7) (R 7) [96,260,136,48,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29292 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 3, region := 193, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 262 140 56 19 34 193 193 449), lower := (rows 97 262 140 56 19 34 64 128 256), losses := [] }

theorem u29292 : Upper (D 7) (R 7) [96,260,136,48,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29293 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 56 19 96 195 131 387), lower := (rows 97 262 140 56 19 96 64 128 256), losses := [] }

theorem u29293 : Upper (D 7) (R 7) [96,260,136,48,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29294 : PairBound 9 := { available := 67, camps := [], pairs := [(0,7),(1,5),(1,7),(2,5)], upper := (rows 97 262 140 56 19 160 67 195 323), lower := (rows 97 262 140 56 19 160 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 16 0 80 144 272), good := (rows 65 262 142 478 467 128 64 128 256) },{ target := 7, region := (rows 9 6 4 8 20 32 84 0 276), good := (rows 97 342 351 377 339 32 64 0 256) }] }

theorem u29294 : Upper (D 7) (R 7) [96,260,136,48,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29295 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 140 56 82 33 195 131 387), lower := (rows 97 262 140 56 82 33 64 128 256), losses := [] }

theorem u29295 : Upper (D 7) (R 7) [96,260,136,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29296 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 197, targets := 2 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,1),(2,1),(3,0),(3,6)], upper := (rows 97 262 140 56 82 34 193 129 385), lower := (rows 97 262 140 56 82 34 64 128 256), losses := [] }

theorem u29296 : Upper (D 7) (R 7) [96,260,136,48,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29297 : Route 9 := (fun mask => (mask,id))

def c29297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29297 : Upper (D 7) (R 7) [96,260,136,48,66,128] 13 := by
  apply FastRouting.sound _ _ [96,260,136,48,66,128] 13 (by decide) (choices 1) [1,2] r29297 c29297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11168
  · exact u11169

def b29298 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 97 262 140 56 145 33 66 194 322), lower := (rows 97 262 140 56 145 33 64 128 256), losses := [] }

theorem u29298 : Upper (D 7) (R 7) [96,260,136,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29299 : Route 9 := (fun mask => (mask,id))

def c29299 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29299 : Upper (D 7) (R 7) [96,260,136,48,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,136,48,129,2] 13 (by decide) (choices 1) [1,2] r29299 c29299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11170
  · exact u11171

def b29300 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 56 145 96 67 131 259), lower := (rows 97 262 140 56 145 96 64 128 256), losses := [] }

theorem u29300 : Upper (D 7) (R 7) [96,260,136,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29301 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 105, targets := 128 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(3,7)], upper := (rows 97 262 140 56 146 33 67 195 323), lower := (rows 97 262 140 56 146 33 64 128 256), losses := [] }

theorem u29301 : Upper (D 7) (R 7) [96,260,136,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29302 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 262 140 56 146 34 65 193 321), lower := (rows 97 262 140 56 146 34 64 128 256), losses := [] }

theorem u29302 : Upper (D 7) (R 7) [96,260,136,48,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29303 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 56 146 96 67 131 259), lower := (rows 97 262 140 56 146 96 64 128 256), losses := [] }

theorem u29303 : Upper (D 7) (R 7) [96,260,136,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29304 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 262 140 56 208 33 67 131 259), lower := (rows 97 262 140 56 208 33 64 128 256), losses := [] }

theorem u29304 : Upper (D 7) (R 7) [96,260,136,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29305 : Route 9 := (fun mask => (mask,id))

def c29305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29305 : Upper (D 7) (R 7) [96,260,136,48,192,2] 13 := by
  apply FastRouting.sound _ _ [96,260,136,48,192,2] 13 (by decide) (choices 1) [1,2] r29305 c29305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11172
  · exact u11173

def b29306 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 4, region := 41, targets := 128 }], pairs := [(0,7),(3,7),(4,0),(4,5)], upper := (rows 97 262 164 11 82 33 216 152 408), lower := (rows 97 262 164 11 82 33 64 128 256), losses := [] }

theorem u29306 : Upper (D 7) (R 7) [96,260,160,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29307 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 41, targets := 128 },{ cop := 3, region := 208, targets := 32 }], pairs := [(0,7),(3,7),(4,5)], upper := (rows 97 262 164 11 82 40 209 145 401), lower := (rows 97 262 164 11 82 40 64 128 256), losses := [] }

theorem u29307 : Upper (D 7) (R 7) [96,260,160,3,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29307 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29308 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 164 11 82 48 201 137 393), lower := (rows 97 262 164 11 82 48 64 128 256), losses := [] }

theorem u29308 : Upper (D 7) (R 7) [96,260,160,3,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29308 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29309 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 97 262 164 11 82 160 89 153 281), lower := (rows 97 262 164 11 82 160 64 128 256), losses := [] }

theorem u29309 : Upper (D 7) (R 7) [96,260,160,3,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29310 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 262 164 11 88 33 210 146 402), lower := (rows 97 262 164 11 88 33 64 128 256), losses := [] }

theorem u29310 : Upper (D 7) (R 7) [96,260,160,3,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29311 : Route 9 := (fun mask => (mask,id))

def c29311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29311 : Upper (D 7) (R 7) [96,260,160,3,72,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,3,72,2] 13 (by decide) (choices 1) [1,16,128] r29311 c29311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11174
  · exact u11175
  · exact u11176

def b29312 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 164 11 88 48 195 131 387), lower := (rows 97 262 164 11 88 48 64 128 256), losses := [] }

theorem u29312 : Upper (D 7) (R 7) [96,260,160,3,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29312 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29313 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 97 262 164 11 88 160 83 147 275), lower := (rows 97 262 164 11 88 160 64 128 256), losses := [] }

theorem u29313 : Upper (D 7) (R 7) [96,260,160,3,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29314 : Route 9 := (fun mask => (mask,id))

def c29314 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29314 : Upper (D 7) (R 7) [96,260,160,3,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,3,129,2] 13 (by decide) (choices 1) [8,16] r29314 c29314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11177
  · exact u11178

def r29315 : Route 9 := (fun mask => (mask,id))

def c29315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29315 : Upper (D 7) (R 7) [96,260,160,3,129,8] 13 := by
  apply FastRouting.sound _ _ [96,260,160,3,129,8] 13 (by decide) (choices 1) [2,16] r29315 c29315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11179
  · exact u11180

def b29316 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 97 262 164 11 145 48 74 202 330), lower := (rows 97 262 164 11 145 48 64 128 256), losses := [] }

theorem u29316 : Upper (D 7) (R 7) [96,260,160,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29316 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29317 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 164 11 145 96 90 154 282), lower := (rows 97 262 164 11 145 96 64 128 256), losses := [] }

theorem u29317 : Upper (D 7) (R 7) [96,260,160,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29318 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(3,7),(4,0),(4,5)], upper := (rows 97 262 164 11 146 33 88 216 344), lower := (rows 97 262 164 11 146 33 64 128 256), losses := [] }

theorem u29318 : Upper (D 7) (R 7) [96,260,160,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29319 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 105, targets := 128 },{ cop := 3, region := 208, targets := 32 }], pairs := [(0,7),(3,7),(4,5)], upper := (rows 97 262 164 11 146 40 81 209 337), lower := (rows 97 262 164 11 146 40 64 128 256), losses := [] }

theorem u29319 : Upper (D 7) (R 7) [96,260,160,3,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29319 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29320 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 97 262 164 11 146 48 73 201 329), lower := (rows 97 262 164 11 146 48 64 128 256), losses := [] }

theorem u29320 : Upper (D 7) (R 7) [96,260,160,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29320 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29321 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 164 11 146 96 89 153 281), lower := (rows 97 262 164 11 146 96 64 128 256), losses := [] }

theorem u29321 : Upper (D 7) (R 7) [96,260,160,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29322 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 262 164 11 152 33 82 210 338), lower := (rows 97 262 164 11 152 33 64 128 256), losses := [] }

theorem u29322 : Upper (D 7) (R 7) [96,260,160,3,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29323 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 208, targets := 34 }], pairs := [(2,0),(2,6),(4,1),(4,5)], upper := (rows 97 262 164 11 152 34 81 209 337), lower := (rows 97 262 164 11 152 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 42 64 128 256), good := (rows 96 294 164 42 188 34 64 128 256) },{ target := 6, region := (rows 1 2 20 8 16 42 0 128 256), good := (rows 33 294 164 43 188 34 0 128 256) }] }

theorem u29323 : Upper (D 7) (R 7) [96,260,160,3,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29324 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 97 262 164 11 152 48 67 195 323), lower := (rows 97 262 164 11 152 48 64 128 256), losses := [] }

theorem u29324 : Upper (D 7) (R 7) [96,260,160,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29324 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29325 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 164 11 152 96 83 147 275), lower := (rows 97 262 164 11 152 96 64 128 256), losses := [] }

theorem u29325 : Upper (D 7) (R 7) [96,260,160,3,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29326 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,5)], upper := (rows 97 262 164 11 208 33 90 154 282), lower := (rows 97 262 164 11 208 33 64 128 256), losses := [] }

theorem u29326 : Upper (D 7) (R 7) [96,260,160,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29327 : Route 9 := (fun mask => (mask,id))

def c29327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29327 : Upper (D 7) (R 7) [96,260,160,3,192,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,3,192,2] 13 (by decide) (choices 1) [1,8,16] r29327 c29327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11181
  · exact u11182
  · exact u11183

def r29328 : Route 9 := (fun mask => (mask,id))

def c29328 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29328 : Upper (D 7) (R 7) [96,260,160,3,192,8] 13 := by
  apply FastRouting.sound _ _ [96,260,160,3,192,8] 13 (by decide) (choices 1) [1,2,16] r29328 c29328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11184
  · exact u11185
  · exact u11186

def b29329 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 164 11 208 48 75 139 267), lower := (rows 97 262 164 11 208 48 64 128 256), losses := [] }

theorem u29329 : Upper (D 7) (R 7) [96,260,160,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29329 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29330 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(2,0)], upper := (rows 97 262 164 25 26 33 194 194 450), lower := (rows 97 262 164 25 26 33 64 128 256), losses := [] }

theorem u29330 : Upper (D 7) (R 7) [96,260,160,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29331 : Route 9 := (fun mask => (mask,id))

def c29331 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29331 : Upper (D 7) (R 7) [96,260,160,17,10,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,17,10,2] 13 (by decide) (choices 1) [1,128] r29331 c29331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11187
  · exact u11188

def b29332 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 164 25 26 96 195 131 387), lower := (rows 97 262 164 25 26 96 64 128 256), losses := [] }

theorem u29332 : Upper (D 7) (R 7) [96,260,160,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29333 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 97 262 164 25 26 160 67 195 323), lower := (rows 97 262 164 25 26 160 64 128 256), losses := [] }

theorem u29333 : Upper (D 7) (R 7) [96,260,160,17,10,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29334 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 164 25 82 33 202 138 394), lower := (rows 97 262 164 25 82 33 64 128 256), losses := [] }

theorem u29334 : Upper (D 7) (R 7) [96,260,160,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29335 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 422, targets := 64 },{ cop := 4, region := 41, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,7)], upper := (rows 97 262 164 25 82 34 201 137 393), lower := (rows 97 262 164 25 82 34 64 128 256), losses := [] }

theorem u29335 : Upper (D 7) (R 7) [96,260,160,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29336 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 262 164 25 82 40 195 131 387), lower := (rows 97 262 164 25 82 40 64 128 256), losses := [] }

theorem u29336 : Upper (D 7) (R 7) [96,260,160,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29336 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29337 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 97 262 164 25 82 160 75 139 267), lower := (rows 97 262 164 25 82 160 64 128 256), losses := [] }

theorem u29337 : Upper (D 7) (R 7) [96,260,160,17,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29338 : Route 9 := (fun mask => (mask,id))

def c29338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29338 : Upper (D 7) (R 7) [96,260,160,17,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,160,17,130,1] 13 (by decide) (choices 1) [2,8] r29338 c29338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11189
  · exact u11190

def b29339 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 36, targets := 65 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(3,7)], upper := (rows 97 262 164 25 146 34 73 201 329), lower := (rows 97 262 164 25 146 34 64 128 256), losses := [] }

theorem u29339 : Upper (D 7) (R 7) [96,260,160,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u29339
end Delivery.IrregularNine14.P07
