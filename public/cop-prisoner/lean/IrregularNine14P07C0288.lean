import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0069
import IrregularNine14P07C0070

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17280 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 13 98 164 328 145 48 67 131 259), lower := (rows 13 98 164 328 145 48 64 128 256), losses := [] }

theorem u17280 : Upper (D 7) (R 7) [12,96,160,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17280 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17281 : Route 9 := (fun mask => (mask,id))

def c17281 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17281 : Upper (D 7) (R 7) [12,96,160,320,130,1] 13 := by
  apply FastRouting.sound _ _ [12,96,160,320,130,1] 13 (by decide) (choices 1) [1,2,16] r17281 c17281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4191
  · exact u4192
  · exact u4193

def b17282 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 4, region := 36, targets := 65 }], pairs := [(1,0),(1,7),(2,0),(2,6)], upper := (rows 13 98 164 328 146 34 81 145 273), lower := (rows 13 98 164 328 146 34 64 128 256), losses := [] }

theorem u17282 : Upper (D 7) (R 7) [12,96,160,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17283 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 13 98 164 328 146 48 67 131 259), lower := (rows 13 98 164 328 146 48 64 128 256), losses := [] }

theorem u17283 : Upper (D 7) (R 7) [12,96,160,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17283 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17284 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 164 392 19 33 82 210 338), lower := (rows 13 98 164 392 19 33 64 128 256), losses := [] }

theorem u17284 : Upper (D 7) (R 7) [12,96,160,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17285 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 4, region := 456, targets := 34 }], pairs := [(1,7),(3,1),(3,5),(4,7)], upper := (rows 13 98 164 392 19 34 81 209 337), lower := (rows 13 98 164 392 19 34 64 128 256), losses := [] }

theorem u17285 : Upper (D 7) (R 7) [12,96,160,384,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17286 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 4, region := 456, targets := 32 }], pairs := [(1,7),(3,5),(4,7)], upper := (rows 13 98 164 392 19 48 67 195 323), lower := (rows 13 98 164 392 19 48 64 128 256), losses := [] }

theorem u17286 : Upper (D 7) (R 7) [12,96,160,384,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17286 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17287 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 164 392 19 96 83 147 275), lower := (rows 13 98 164 392 19 96 64 128 256), losses := [] }

theorem u17287 : Upper (D 7) (R 7) [12,96,160,384,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17288 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 164 392 81 33 82 146 274), lower := (rows 13 98 164 392 81 33 64 128 256), losses := [] }

theorem u17288 : Upper (D 7) (R 7) [12,96,160,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17289 : Route 9 := (fun mask => (mask,id))

def c17289 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17289 : Upper (D 7) (R 7) [12,96,160,384,65,2] 13 := by
  apply FastRouting.sound _ _ [12,96,160,384,65,2] 13 (by decide) (choices 1) [1,2,16] r17289 c17289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4194
  · exact u4195
  · exact u4196

def b17290 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 164 392 81 48 67 131 259), lower := (rows 13 98 164 392 81 48 64 128 256), losses := [] }

theorem u17290 : Upper (D 7) (R 7) [12,96,160,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17290 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17291 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 1, region := 232, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 13 259 21 42 82 96 224 160 416), lower := (rows 13 259 21 42 82 96 64 128 256), losses := [] }

theorem u17291 : Upper (D 7) (R 7) [12,257,17,34,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17292 : Route 9 := (fun mask => (mask,id))

def c17292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17292 : Upper (D 7) (R 7) [12,257,17,34,66,128] 13 := by
  apply FastRouting.sound _ _ [12,257,17,34,66,128] 13 (by decide) (choices 1) [32,128] r17292 c17292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4197
  · exact u4198

def b17293 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 213, targets := 2 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 13 259 21 42 112 34 192 192 448), lower := (rows 13 259 21 42 112 34 64 128 256), losses := [] }

theorem u17293 : Upper (D 7) (R 7) [12,257,17,34,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17294 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 13 259 21 42 112 96 194 130 386), lower := (rows 13 259 21 42 112 96 64 128 256), losses := [] }

theorem u17294 : Upper (D 7) (R 7) [12,257,17,34,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17295 : Route 9 := (fun mask => (mask,id))

def c17295 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17295 : Upper (D 7) (R 7) [12,257,17,34,96,128] 13 := by
  apply FastRouting.sound _ _ [12,257,17,34,96,128] 13 (by decide) (choices 1) [2,128] r17295 c17295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4199
  · exact u4200

def b17296 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 213, targets := 2 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 13 259 21 42 208 34 224 224 480), lower := (rows 13 259 21 42 208 34 64 128 256), losses := [] }

theorem u17296 : Upper (D 7) (R 7) [12,257,17,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17297 : Route 9 := (fun mask => (mask,id))

def c17297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17297 : Upper (D 7) (R 7) [12,257,17,34,192,64] 13 := by
  apply FastRouting.sound _ _ [12,257,17,34,192,64] 13 (by decide) (choices 1) [2,32,128] r17297 c17297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4201
  · exact u4202
  · exact u4203

def b17298 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 52, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 259 21 104 50 34 192 192 448), lower := (rows 13 259 21 104 50 34 64 128 256), losses := [] }

theorem u17298 : Upper (D 7) (R 7) [12,257,17,96,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17299 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 259 21 104 50 96 194 130 386), lower := (rows 13 259 21 104 50 96 64 128 256), losses := [] }

theorem u17299 : Upper (D 7) (R 7) [12,257,17,96,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17300 : Route 9 := (fun mask => (mask,id))

def c17300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17300 : Upper (D 7) (R 7) [12,257,17,96,34,128] 13 := by
  apply FastRouting.sound _ _ [12,257,17,96,34,128] 13 (by decide) (choices 1) [2,128] r17300 c17300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4204
  · exact u4205

def r17301 : Route 9 := (fun mask => (mask,id))

def c17301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17301 : Upper (D 7) (R 7) [12,257,17,96,130,2] 13 := by
  apply FastRouting.sound _ _ [12,257,17,96,130,2] 13 (by decide) (choices 1) [32,128] r17301 c17301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4206
  · exact u4207

def b17302 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 259 21 104 146 96 226 162 418), lower := (rows 13 259 21 104 146 96 64 128 256), losses := [] }

theorem u17302 : Upper (D 7) (R 7) [12,257,17,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17303_2 : Upper (D 7) (R 7) [12,257,17,96,130,128,2] 13 :=
  permutation_upper _ _ _ [12,257,17,96,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4207

theorem m17303_32 : Upper (D 7) (R 7) [12,257,17,96,130,128,32] 13 :=
  permutation_upper _ _ _ [12,257,17,96,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4208

def r17303 : Route 9 := (fun mask => (mask,id))

def c17303 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17303 : Upper (D 7) (R 7) [12,257,17,96,130,128] 13 := by
  apply FastRouting.sound _ _ [12,257,17,96,130,128] 13 (by decide) (choices 1) [2,32] r17303 c17303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17303_2
  · exact m17303_32

def r17304 : Route 9 := (fun mask => (mask,id))

def c17304 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17304 : Upper (D 7) (R 7) [12,257,17,96,160,2] 13 := by
  apply FastRouting.sound _ _ [12,257,17,96,160,2] 13 (by decide) (choices 1) [2,128] r17304 c17304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4209
  · exact u4210

def b17305 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 259 21 104 176 96 194 130 386), lower := (rows 13 259 21 104 176 96 64 128 256), losses := [] }

theorem u17305 : Upper (D 7) (R 7) [12,257,17,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17306 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 21 104 176 160 66 194 322), lower := (rows 13 259 21 104 176 160 64 128 256), losses := [] }

theorem u17306 : Upper (D 7) (R 7) [12,257,17,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17307 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 259 22 41 112 34 192 192 448), lower := (rows 13 259 22 41 112 34 64 128 256), losses := [] }

theorem u17307 : Upper (D 7) (R 7) [12,257,18,33,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17308 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 13 259 22 41 112 96 194 130 386), lower := (rows 13 259 22 41 112 96 64 128 256), losses := [] }

theorem u17308 : Upper (D 7) (R 7) [12,257,18,33,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17309 : Route 9 := (fun mask => (mask,id))

def c17309 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17309 : Upper (D 7) (R 7) [12,257,18,33,96,128] 13 := by
  apply FastRouting.sound _ _ [12,257,18,33,96,128] 13 (by decide) (choices 1) [2,128] r17309 c17309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4211
  · exact u4212

def b17310 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 259 22 41 208 34 224 224 480), lower := (rows 13 259 22 41 208 34 64 128 256), losses := [] }

theorem u17310 : Upper (D 7) (R 7) [12,257,18,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17311 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 244, targets := 1 },{ cop := 3, region := 386, targets := 64 }], pairs := [(0,1),(1,6),(2,0),(4,0)], upper := (rows 13 259 22 41 208 96 226 162 418), lower := (rows 13 259 22 41 208 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 16 112 64 128 256), good := (rows 13 257 61 41 240 96 96 128 256) }] }

theorem u17311 : Upper (D 7) (R 7) [12,257,18,33,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17312 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 1, region := 232, targets := 1 }], pairs := [(1,6),(2,6),(3,0),(4,1)], upper := (rows 13 259 22 42 81 96 224 160 416), lower := (rows 13 259 22 42 81 96 64 128 256), losses := [{ target := 6, region := (rows 1 3 20 8 16 32 0 168 296), good := (rows 399 259 22 426 23 416 0 128 256) }] }

theorem u17312 : Upper (D 7) (R 7) [12,257,18,34,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17313 : Route 9 := (fun mask => (mask,id))

def c17313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17313 : Upper (D 7) (R 7) [12,257,18,34,65,128] 13 := by
  apply FastRouting.sound _ _ [12,257,18,34,65,128] 13 (by decide) (choices 1) [32,128] r17313 c17313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4213
  · exact u4214

def b17314 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 259 22 42 112 33 192 192 448), lower := (rows 13 259 22 42 112 33 64 128 256), losses := [] }

theorem u17314 : Upper (D 7) (R 7) [12,257,18,34,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17315 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 13 259 22 42 112 96 193 129 385), lower := (rows 13 259 22 42 112 96 64 128 256), losses := [] }

theorem u17315 : Upper (D 7) (R 7) [12,257,18,34,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17316 : Route 9 := (fun mask => (mask,id))

def c17316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17316 : Upper (D 7) (R 7) [12,257,18,34,96,128] 13 := by
  apply FastRouting.sound _ _ [12,257,18,34,96,128] 13 (by decide) (choices 1) [1,128] r17316 c17316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4215
  · exact u4216

def b17317 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 259 22 42 208 33 224 224 480), lower := (rows 13 259 22 42 208 33 64 128 256), losses := [] }

theorem u17317 : Upper (D 7) (R 7) [12,257,18,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17318 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 240, targets := 2 }], pairs := [(0,7),(3,0),(3,7),(4,1)], upper := (rows 13 259 22 42 208 96 225 161 417), lower := (rows 13 259 22 42 208 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 112 64 128 256), good := (rows 12 258 62 42 240 96 96 128 256) },{ target := 7, region := (rows 5 2 4 12 16 112 64 0 256), good := (rows 13 259 63 42 112 96 96 0 256) }] }

theorem u17318 : Upper (D 7) (R 7) [12,257,18,34,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17319 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 52, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 259 22 104 49 34 192 192 448), lower := (rows 13 259 22 104 49 34 64 128 256), losses := [] }

theorem u17319 : Upper (D 7) (R 7) [12,257,18,96,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17320 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 259 22 104 49 96 194 130 386), lower := (rows 13 259 22 104 49 96 64 128 256), losses := [] }

theorem u17320 : Upper (D 7) (R 7) [12,257,18,96,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17321 : Route 9 := (fun mask => (mask,id))

def c17321 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17321 : Upper (D 7) (R 7) [12,257,18,96,33,128] 13 := by
  apply FastRouting.sound _ _ [12,257,18,96,33,128] 13 (by decide) (choices 1) [2,128] r17321 c17321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4217
  · exact u4218

def r17322 : Route 9 := (fun mask => (mask,id))

def c17322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17322 : Upper (D 7) (R 7) [12,257,18,96,129,2] 13 := by
  apply FastRouting.sound _ _ [12,257,18,96,129,2] 13 (by decide) (choices 1) [32,128] r17322 c17322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4219
  · exact u4220

def b17323 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 259 22 104 145 96 226 162 418), lower := (rows 13 259 22 104 145 96 64 128 256), losses := [] }

theorem u17323 : Upper (D 7) (R 7) [12,257,18,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17324_2 : Upper (D 7) (R 7) [12,257,18,96,129,128,2] 13 :=
  permutation_upper _ _ _ [12,257,18,96,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4220

theorem m17324_32 : Upper (D 7) (R 7) [12,257,18,96,129,128,32] 13 :=
  permutation_upper _ _ _ [12,257,18,96,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4221

def r17324 : Route 9 := (fun mask => (mask,id))

def c17324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17324 : Upper (D 7) (R 7) [12,257,18,96,129,128] 13 := by
  apply FastRouting.sound _ _ [12,257,18,96,129,128] 13 (by decide) (choices 1) [2,32] r17324 c17324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17324_2
  · exact m17324_32

def r17325 : Route 9 := (fun mask => (mask,id))

def c17325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17325 : Upper (D 7) (R 7) [12,257,18,96,160,1] 13 := by
  apply FastRouting.sound _ _ [12,257,18,96,160,1] 13 (by decide) (choices 1) [2,128] r17325 c17325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4222
  · exact u4223

def r17326 : Route 9 := (fun mask => (mask,id))

def c17326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17326 : Upper (D 7) (R 7) [12,257,18,96,160,2] 13 := by
  apply FastRouting.sound _ _ [12,257,18,96,160,2] 13 (by decide) (choices 1) [1,128] r17326 c17326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4224
  · exact u4225

def b17327 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 259 22 104 176 96 195 131 387), lower := (rows 13 259 22 104 176 96 64 128 256), losses := [] }

theorem u17327 : Upper (D 7) (R 7) [12,257,18,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17328 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 22 104 176 160 67 195 323), lower := (rows 13 259 22 104 176 160 64 128 256), losses := [] }

theorem u17328 : Upper (D 7) (R 7) [12,257,18,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17329 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 13 259 37 74 50 48 192 192 448), lower := (rows 13 259 37 74 50 48 64 128 256), losses := [] }

theorem u17329 : Upper (D 7) (R 7) [12,257,33,66,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17329 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17330 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 13 259 37 74 50 96 208 144 400), lower := (rows 13 259 37 74 50 96 64 128 256), losses := [] }

theorem u17330 : Upper (D 7) (R 7) [12,257,33,66,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17331 : Route 9 := (fun mask => (mask,id))

def c17331 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17331 : Upper (D 7) (R 7) [12,257,33,66,34,128] 13 := by
  apply FastRouting.sound _ _ [12,257,33,66,34,128] 13 (by decide) (choices 1) [16,128] r17331 c17331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4226
  · exact u4227

def b17332 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 13 259 37 74 112 34 208 144 400), lower := (rows 13 259 37 74 112 34 64 128 256), losses := [] }

theorem u17332 : Upper (D 7) (R 7) [12,257,33,66,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17333 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 53, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 13 259 37 74 112 48 194 130 386), lower := (rows 13 259 37 74 112 48 64 128 256), losses := [] }

theorem u17333 : Upper (D 7) (R 7) [12,257,33,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17333 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17334 : Route 9 := (fun mask => (mask,id))

def c17334 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17334 : Upper (D 7) (R 7) [12,257,33,66,96,128] 13 := by
  apply FastRouting.sound _ _ [12,257,33,66,96,128] 13 (by decide) (choices 1) [2,16,128] r17334 c17334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4228
  · exact u4229
  · exact u4230

def r17335 : Route 9 := (fun mask => (mask,id))

def c17335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17335 : Upper (D 7) (R 7) [12,257,33,66,130,16] 13 := by
  apply FastRouting.sound _ _ [12,257,33,66,130,16] 13 (by decide) (choices 1) [32,128] r17335 c17335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4231
  · exact u4232

def b17336 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 259 37 74 146 96 240 176 432), lower := (rows 13 259 37 74 146 96 64 128 256), losses := [] }

theorem u17336 : Upper (D 7) (R 7) [12,257,33,66,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17337 : Route 9 := (fun mask => (mask,id))

def c17337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17337 : Upper (D 7) (R 7) [12,257,33,66,130,128] 13 := by
  apply FastRouting.sound _ _ [12,257,33,66,130,128] 13 (by decide) (choices 1) [16,32] r17337 c17337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4233
  · exact u4234

def b17338 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 259 37 74 176 34 208 208 464), lower := (rows 13 259 37 74 176 34 64 128 256), losses := [] }

theorem u17338 : Upper (D 7) (R 7) [12,257,33,66,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17339 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 13 259 37 74 176 48 194 194 450), lower := (rows 13 259 37 74 176 48 64 128 256), losses := [] }

theorem u17339 : Upper (D 7) (R 7) [12,257,33,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17339 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17339
end Delivery.IrregularNine14.P07
