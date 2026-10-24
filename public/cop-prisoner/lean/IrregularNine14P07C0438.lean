import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0156
import IrregularNine14P07C0157

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26280 : PairBound 9 := { available := 131, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 26 176 96 195 131 387), lower := (rows 37 266 69 26 176 96 64 128 256), losses := [] }

theorem u26280 : Upper (D 7) (R 7) [36,264,65,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26281 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 69 26 176 160 67 195 323), lower := (rows 37 266 69 26 176 160 64 128 256), losses := [] }

theorem u26281 : Upper (D 7) (R 7) [36,264,65,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26282 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 26 208 33 226 162 418), lower := (rows 37 266 69 26 208 33 64 128 256), losses := [] }

theorem u26282 : Upper (D 7) (R 7) [36,264,65,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26283 : Route 9 := (fun mask => (mask,id))

def c26283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26283 : Upper (D 7) (R 7) [36,264,65,18,192,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,18,192,2] 13 (by decide) (choices 1) [1,32,128] r26283 c26283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9403
  · exact u9404
  · exact u9405

def r26284 : Route 9 := (fun mask => (mask,id))

def c26284 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26284 : Upper (D 7) (R 7) [36,264,65,18,192,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,18,192,128] 13 (by decide) (choices 1) [1,2,32] r26284 c26284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9406
  · exact u9407
  · exact u9408

def b26285 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 266 69 42 82 33 208 144 400), lower := (rows 37 266 69 42 82 33 64 128 256), losses := [] }

theorem u26285 : Upper (D 7) (R 7) [36,264,65,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26286 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 266 69 42 82 48 193 129 385), lower := (rows 37 266 69 42 82 48 64 128 256), losses := [] }

theorem u26286 : Upper (D 7) (R 7) [36,264,65,34,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26286 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26287 : Route 9 := (fun mask => (mask,id))

def c26287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26287 : Upper (D 7) (R 7) [36,264,65,34,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,34,66,128] 13 (by decide) (choices 1) [1,16,128] r26287 c26287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9409
  · exact u9410
  · exact u9411

def b26288 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 42, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 266 69 42 145 34 208 208 464), lower := (rows 37 266 69 42 145 34 64 128 256), losses := [] }

theorem u26288 : Upper (D 7) (R 7) [36,264,65,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26289 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 266 69 42 145 48 194 194 450), lower := (rows 37 266 69 42 145 48 64 128 256), losses := [] }

theorem u26289 : Upper (D 7) (R 7) [36,264,65,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26289 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26290 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 42 145 96 210 146 402), lower := (rows 37 266 69 42 145 96 64 128 256), losses := [] }

theorem u26290 : Upper (D 7) (R 7) [36,264,65,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26291 : Route 9 := (fun mask => (mask,id))

def c26291 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26291 : Upper (D 7) (R 7) [36,264,65,34,129,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,34,129,128] 13 (by decide) (choices 1) [2,16] r26291 c26291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9412
  · exact u9413

def b26292 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 266 69 42 146 33 208 208 464), lower := (rows 37 266 69 42 146 33 64 128 256), losses := [] }

theorem u26292 : Upper (D 7) (R 7) [36,264,65,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26293 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 37 266 69 42 146 48 193 193 449), lower := (rows 37 266 69 42 146 48 64 128 256), losses := [] }

theorem u26293 : Upper (D 7) (R 7) [36,264,65,34,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26293 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26294 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 42 146 96 209 145 401), lower := (rows 37 266 69 42 146 96 64 128 256), losses := [] }

theorem u26294 : Upper (D 7) (R 7) [36,264,65,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26295 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 40, targets := 65 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(3,6)], upper := (rows 37 266 69 42 146 160 81 209 337), lower := (rows 37 266 69 42 146 160 64 128 256), losses := [] }

theorem u26295 : Upper (D 7) (R 7) [36,264,65,34,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26296 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 266 69 42 208 33 210 146 402), lower := (rows 37 266 69 42 208 33 64 128 256), losses := [] }

theorem u26296 : Upper (D 7) (R 7) [36,264,65,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26297 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 42, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 266 69 42 208 34 209 145 401), lower := (rows 37 266 69 42 208 34 64 128 256), losses := [] }

theorem u26297 : Upper (D 7) (R 7) [36,264,65,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26298 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 266 69 42 208 48 195 131 387), lower := (rows 37 266 69 42 208 48 64 128 256), losses := [] }

theorem u26298 : Upper (D 7) (R 7) [36,264,65,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26298 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26299 : Route 9 := (fun mask => (mask,id))

def c26299 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26299 : Upper (D 7) (R 7) [36,264,65,34,192,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,34,192,128] 13 (by decide) (choices 1) [1,2,16] r26299 c26299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9414
  · exact u9415
  · exact u9416

def b26300 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 56 82 33 194 130 386), lower := (rows 37 266 69 56 82 33 64 128 256), losses := [] }

theorem u26300 : Upper (D 7) (R 7) [36,264,65,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26301 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,7),(2,1),(2,7),(3,7)], upper := (rows 37 266 69 56 82 34 193 129 385), lower := (rows 37 266 69 56 82 34 64 128 256), losses := [] }

theorem u26301 : Upper (D 7) (R 7) [36,264,65,48,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26302 : Route 9 := (fun mask => (mask,id))

def c26302 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26302 : Upper (D 7) (R 7) [36,264,65,48,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,48,66,128] 13 (by decide) (choices 1) [1,2,128] r26302 c26302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9417
  · exact u9418
  · exact u9419

def b26303 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(3,0)], upper := (rows 37 266 69 56 145 34 194 194 450), lower := (rows 37 266 69 56 145 34 64 128 256), losses := [{ target := 5, region := (rows 1 10 5 8 17 0 106 170 298), good := (rows 469 458 85 474 149 450 64 128 256) }] }

theorem u26303 : Upper (D 7) (R 7) [36,264,65,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26304 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 56 145 96 194 130 386), lower := (rows 37 266 69 56 145 96 64 128 256), losses := [] }

theorem u26304 : Upper (D 7) (R 7) [36,264,65,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26305 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 266 69 56 145 160 66 194 322), lower := (rows 37 266 69 56 145 160 64 128 256), losses := [] }

theorem u26305 : Upper (D 7) (R 7) [36,264,65,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26306 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 266 69 56 146 33 194 194 450), lower := (rows 37 266 69 56 146 33 64 128 256), losses := [] }

theorem u26306 : Upper (D 7) (R 7) [36,264,65,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26307 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(3,0),(3,6),(3,7)], upper := (rows 37 266 69 56 146 34 193 193 449), lower := (rows 37 266 69 56 146 34 64 128 256), losses := [] }

theorem u26307 : Upper (D 7) (R 7) [36,264,65,48,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26308 : PairBound 9 := { available := 131, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 56 146 96 195 131 387), lower := (rows 37 266 69 56 146 96 64 128 256), losses := [] }

theorem u26308 : Upper (D 7) (R 7) [36,264,65,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26309 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 266 69 56 146 160 67 195 323), lower := (rows 37 266 69 56 146 160 64 128 256), losses := [] }

theorem u26309 : Upper (D 7) (R 7) [36,264,65,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26310 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 56 208 33 194 130 386), lower := (rows 37 266 69 56 208 33 64 128 256), losses := [] }

theorem u26310 : Upper (D 7) (R 7) [36,264,65,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26311 : Route 9 := (fun mask => (mask,id))

def c26311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26311 : Upper (D 7) (R 7) [36,264,65,48,192,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,48,192,2] 13 (by decide) (choices 1) [1,2,128] r26311 c26311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9420
  · exact u9421
  · exact u9422

def b26312 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 266 69 56 208 160 67 131 259), lower := (rows 37 266 69 56 208 160 64 128 256), losses := [] }

theorem u26312 : Upper (D 7) (R 7) [36,264,65,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26313 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 266 69 74 50 33 208 144 400), lower := (rows 37 266 69 74 50 33 64 128 256), losses := [] }

theorem u26313 : Upper (D 7) (R 7) [36,264,65,66,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26314 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 69 74 50 48 193 129 385), lower := (rows 37 266 69 74 50 48 64 128 256), losses := [] }

theorem u26314 : Upper (D 7) (R 7) [36,264,65,66,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26314 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26315 : Route 9 := (fun mask => (mask,id))

def c26315 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26315 : Upper (D 7) (R 7) [36,264,65,66,34,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,66,34,128] 13 (by decide) (choices 1) [1,16,128] r26315 c26315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9423
  · exact u9424
  · exact u9425

def b26316 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 266 69 74 145 34 240 176 432), lower := (rows 37 266 69 74 145 34 64 128 256), losses := [] }

theorem u26316 : Upper (D 7) (R 7) [36,264,65,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26317 : Route 9 := (fun mask => (mask,id))

def c26317 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26317 : Upper (D 7) (R 7) [36,264,65,66,129,16] 13 := by
  apply FastRouting.sound _ _ [36,264,65,66,129,16] 13 (by decide) (choices 1) [2,32,128] r26317 c26317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9426
  · exact u9427
  · exact u9428

def r26318 : Route 9 := (fun mask => (mask,id))

def c26318 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26318 : Upper (D 7) (R 7) [36,264,65,66,129,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,66,129,128] 13 (by decide) (choices 1) [2,16,32] r26318 c26318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9429
  · exact u9430
  · exact u9431

def b26319 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 74 146 33 240 176 432), lower := (rows 37 266 69 74 146 33 64 128 256), losses := [] }

theorem u26319 : Upper (D 7) (R 7) [36,264,65,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26320 : Route 9 := (fun mask => (mask,id))

def c26320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26320 : Upper (D 7) (R 7) [36,264,65,66,130,16] 13 := by
  apply FastRouting.sound _ _ [36,264,65,66,130,16] 13 (by decide) (choices 1) [1,32,128] r26320 c26320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9432
  · exact u9433
  · exact u9434

def r26321 : Route 9 := (fun mask => (mask,id))

def c26321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26321 : Upper (D 7) (R 7) [36,264,65,66,130,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,66,130,128] 13 (by decide) (choices 1) [1,16,32] r26321 c26321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9435
  · exact u9436
  · exact u9437

def b26322 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 74 176 33 210 146 402), lower := (rows 37 266 69 74 176 33 64 128 256), losses := [] }

theorem u26322 : Upper (D 7) (R 7) [36,264,65,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26323 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 266 69 74 176 34 209 145 401), lower := (rows 37 266 69 74 176 34 64 128 256), losses := [] }

theorem u26323 : Upper (D 7) (R 7) [36,264,65,66,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26324 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 69 74 176 48 195 131 387), lower := (rows 37 266 69 74 176 48 64 128 256), losses := [] }

theorem u26324 : Upper (D 7) (R 7) [36,264,65,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26324 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26325 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 69 74 176 160 83 147 275), lower := (rows 37 266 69 74 176 160 64 128 256), losses := [] }

theorem u26325 : Upper (D 7) (R 7) [36,264,65,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26326 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 266 69 88 19 34 224 160 416), lower := (rows 37 266 69 88 19 34 64 128 256), losses := [] }

theorem u26326 : Upper (D 7) (R 7) [36,264,65,80,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26327 : Route 9 := (fun mask => (mask,id))

def c26327 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26327 : Upper (D 7) (R 7) [36,264,65,80,3,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,80,3,128] 13 (by decide) (choices 1) [2,32,128] r26327 c26327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9438
  · exact u9439
  · exact u9440

def b26328 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 88 50 33 194 130 386), lower := (rows 37 266 69 88 50 33 64 128 256), losses := [] }

theorem u26328 : Upper (D 7) (R 7) [36,264,65,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26329 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 266 69 88 50 34 193 129 385), lower := (rows 37 266 69 88 50 34 64 128 256), losses := [] }

theorem u26329 : Upper (D 7) (R 7) [36,264,65,80,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26330 : Route 9 := (fun mask => (mask,id))

def c26330 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26330 : Upper (D 7) (R 7) [36,264,65,80,34,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,80,34,128] 13 (by decide) (choices 1) [1,2,128] r26330 c26330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9441
  · exact u9442
  · exact u9443

def b26331 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,6)], upper := (rows 37 266 69 88 145 34 226 162 418), lower := (rows 37 266 69 88 145 34 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 17 42 0 170 298), good := (rows 437 426 21 442 145 418 0 128 256) }] }

theorem u26331 : Upper (D 7) (R 7) [36,264,65,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26332 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,1),(1,0),(1,6),(3,0)], upper := (rows 37 266 69 88 145 160 98 162 290), lower := (rows 37 266 69 88 145 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 269 69 125 177 160 64 160 256) }] }

theorem u26332 : Upper (D 7) (R 7) [36,264,65,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26333 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 88 146 33 226 162 418), lower := (rows 37 266 69 88 146 33 64 128 256), losses := [] }

theorem u26333 : Upper (D 7) (R 7) [36,264,65,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26334 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 88 146 34 225 161 417), lower := (rows 37 266 69 88 146 34 64 128 256), losses := [{ target := 7, region := (rows 11 2 12 8 16 50 64 0 256), good := (rows 37 303 69 125 51 35 64 0 256) }] }

theorem u26334 : Upper (D 7) (R 7) [36,264,65,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26335 : Route 9 := (fun mask => (mask,id))

def c26335 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26335 : Upper (D 7) (R 7) [36,264,65,80,130,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,80,130,128] 13 (by decide) (choices 1) [1,2,32] r26335 c26335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9444
  · exact u9445
  · exact u9446

def b26336 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 88 176 33 194 130 386), lower := (rows 37 266 69 88 176 33 64 128 256), losses := [] }

theorem u26336 : Upper (D 7) (R 7) [36,264,65,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26337 : Route 9 := (fun mask => (mask,id))

def c26337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26337 : Upper (D 7) (R 7) [36,264,65,80,160,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,80,160,2] 13 (by decide) (choices 1) [1,2,128] r26337 c26337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9447
  · exact u9448
  · exact u9449

def b26338 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 69 88 176 160 67 131 259), lower := (rows 37 266 69 88 176 160 64 128 256), losses := [] }

theorem u26338 : Upper (D 7) (R 7) [36,264,65,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26339 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 205, targets := 2 },{ cop := 1, region := 48, targets := 64 }], pairs := [(0,1),(2,1),(3,1),(4,6)], upper := (rows 37 266 69 137 50 34 208 208 464), lower := (rows 37 266 69 137 50 34 64 128 256), losses := [] }

theorem u26339 : Upper (D 7) (R 7) [36,264,65,129,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26339
end Delivery.IrregularNine14.P07
