import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0060
import IrregularNine14P07C0061

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16320 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 46, targets := 1 },{ cop := 0, region := 464, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 13 50 70 168 208 34 321 385 257), lower := (rows 13 50 70 168 208 34 64 128 256), losses := [] }

theorem u16320 : Upper (D 7) (R 7) [12,48,66,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16321 : Route 9 := (fun mask => (mask,id))

def c16321 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16321 : Upper (D 7) (R 7) [12,48,66,160,192,256] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,192,256] 13 (by decide) (choices 1) [1,2] r16321 c16321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3651
  · exact u3652

def b16322 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(3,0)], upper := (rows 13 50 70 168 273 33 194 194 450), lower := (rows 13 50 70 168 273 33 64 128 256), losses := [] }

theorem u16322 : Upper (D 7) (R 7) [12,48,66,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16323 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 34, targets := 193 },{ cop := 0, region := 464, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 50 70 168 273 34 193 193 449), lower := (rows 13 50 70 168 273 34 64 128 256), losses := [] }

theorem u16323 : Upper (D 7) (R 7) [12,48,66,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16324 : Route 9 := (fun mask => (mask,id))

def c16324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16324 : Upper (D 7) (R 7) [12,48,66,160,257,64] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,257,64] 13 (by decide) (choices 1) [1,2,128] r16324 c16324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3653
  · exact u3654
  · exact u3655

def b16325 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 70 168 273 160 67 195 323), lower := (rows 13 50 70 168 273 160 64 128 256), losses := [] }

theorem u16325 : Upper (D 7) (R 7) [12,48,66,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16326 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 169, targets := 2 }], pairs := [(0,1),(2,5),(3,1),(4,5)], upper := (rows 13 50 70 168 274 33 193 193 449), lower := (rows 13 50 70 168 274 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 8 18 0 97 161 289), good := (rows 461 470 86 456 278 449 64 128 256) }] }

theorem u16326 : Upper (D 7) (R 7) [12,48,66,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16327 : Route 9 := (fun mask => (mask,id))

def c16327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16327 : Upper (D 7) (R 7) [12,48,66,160,258,64] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,258,64] 13 (by decide) (choices 1) [1,128] r16327 c16327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3656
  · exact u3657

def b16328 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 70 168 274 160 65 193 321), lower := (rows 13 50 70 168 274 160 64 128 256), losses := [] }

theorem u16328 : Upper (D 7) (R 7) [12,48,66,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16329 : Route 9 := (fun mask => (mask,id))

def c16329 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16329 : Upper (D 7) (R 7) [12,48,66,160,320,1] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,320,1] 13 (by decide) (choices 1) [1,2,128] r16329 c16329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3658
  · exact u3659
  · exact u3660

def b16330 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 168 336 34 193 129 385), lower := (rows 13 50 70 168 336 34 64 128 256), losses := [] }

theorem u16330 : Upper (D 7) (R 7) [12,48,66,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16331 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 70 168 336 160 67 131 259), lower := (rows 13 50 70 168 336 160 64 128 256), losses := [] }

theorem u16331 : Upper (D 7) (R 7) [12,48,66,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16332 : Route 9 := (fun mask => (mask,id))

def c16332 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16332 : Upper (D 7) (R 7) [12,48,66,160,384,1] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,384,1] 13 (by decide) (choices 1) [1,2] r16332 c16332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3661
  · exact u3662

def b16333 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 70 168 400 34 65 193 321), lower := (rows 13 50 70 168 400 34 64 128 256), losses := [] }

theorem u16333 : Upper (D 7) (R 7) [12,48,66,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16334 : Route 9 := (fun mask => (mask,id))

def c16334 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16334 : Upper (D 7) (R 7) [12,48,66,160,384,64] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,384,64] 13 (by decide) (choices 1) [1,2] r16334 c16334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3663
  · exact u3664

def b16335 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 204, targets := 1 }], pairs := [(1,6),(2,0),(3,0),(4,6)], upper := (rows 13 50 70 200 273 33 226 162 418), lower := (rows 13 50 70 200 273 33 64 128 256), losses := [] }

theorem u16335 : Upper (D 7) (R 7) [12,48,66,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16336 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 50 70 200 273 34 225 161 417), lower := (rows 13 50 70 200 273 34 64 128 256), losses := [] }

theorem u16336 : Upper (D 7) (R 7) [12,48,66,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16337 : Route 9 := (fun mask => (mask,id))

def c16337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16337 : Upper (D 7) (R 7) [12,48,66,192,257,128] 13 := by
  apply FastRouting.sound _ _ [12,48,66,192,257,128] 13 (by decide) (choices 1) [1,2,32] r16337 c16337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3665
  · exact u3666
  · exact u3667

def r16338 : Route 9 := (fun mask => (mask,id))

def c16338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16338 : Upper (D 7) (R 7) [12,48,66,192,384,1] 13 := by
  apply FastRouting.sound _ _ [12,48,66,192,384,1] 13 (by decide) (choices 1) [1,2,32] r16338 c16338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3668
  · exact u3669
  · exact u3670

def b16339 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 34, targets := 193 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 50 70 200 400 34 97 161 289), lower := (rows 13 50 70 200 400 34 64 128 256), losses := [] }

theorem u16339 : Upper (D 7) (R 7) [12,48,66,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16340 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 13 50 70 265 145 34 224 224 480), lower := (rows 13 50 70 265 145 34 64 128 256), losses := [] }

theorem u16340 : Upper (D 7) (R 7) [12,48,66,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16341 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 102, targets := 1 }], pairs := [(0,6),(1,0),(2,0),(3,6)], upper := (rows 13 50 70 265 145 96 226 162 418), lower := (rows 13 50 70 265 145 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 12 20 32 0 130 258), good := (rows 29 434 415 265 145 32 0 128 256) }] }

theorem u16341 : Upper (D 7) (R 7) [12,48,66,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16342 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 70 265 145 160 98 226 354), lower := (rows 13 50 70 265 145 160 64 128 256), losses := [] }

theorem u16342 : Upper (D 7) (R 7) [12,48,66,257,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16343 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 214, targets := 1 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(1,0),(2,0),(4,0)], upper := (rows 13 50 70 265 146 33 224 224 480), lower := (rows 13 50 70 265 146 33 64 128 256), losses := [] }

theorem u16343 : Upper (D 7) (R 7) [12,48,66,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16344 : Route 9 := (fun mask => (mask,id))

def c16344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16344 : Upper (D 7) (R 7) [12,48,66,257,130,64] 13 := by
  apply FastRouting.sound _ _ [12,48,66,257,130,64] 13 (by decide) (choices 1) [1,32,128] r16344 c16344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3671
  · exact u3672
  · exact u3673

def b16345 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 70 265 146 160 97 225 353), lower := (rows 13 50 70 265 146 160 64 128 256), losses := [] }

theorem u16345 : Upper (D 7) (R 7) [12,48,66,257,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16346 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 214, targets := 1 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(4,0)], upper := (rows 13 50 70 265 208 33 226 162 418), lower := (rows 13 50 70 265 208 33 64 128 256), losses := [] }

theorem u16346 : Upper (D 7) (R 7) [12,48,66,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16347 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 265 208 34 225 161 417), lower := (rows 13 50 70 265 208 34 64 128 256), losses := [] }

theorem u16347 : Upper (D 7) (R 7) [12,48,66,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16348 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 13 50 70 265 208 160 99 163 291), lower := (rows 13 50 70 265 208 160 64 128 256), losses := [] }

theorem u16348 : Upper (D 7) (R 7) [12,48,66,257,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16349 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(3,0)], upper := (rows 13 50 70 266 145 33 224 224 480), lower := (rows 13 50 70 266 145 33 64 128 256), losses := [] }

theorem u16349 : Upper (D 7) (R 7) [12,48,66,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16350 : Route 9 := (fun mask => (mask,id))

def c16350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16350 : Upper (D 7) (R 7) [12,48,66,258,129,64] 13 := by
  apply FastRouting.sound _ _ [12,48,66,258,129,64] 13 (by decide) (choices 1) [1,32,128] r16350 c16350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3674
  · exact u3675
  · exact u3676

def b16351 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 70 266 145 160 97 225 353), lower := (rows 13 50 70 266 145 160 64 128 256), losses := [] }

theorem u16351 : Upper (D 7) (R 7) [12,48,66,258,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16352 : Route 9 := (fun mask => (mask,id))

def c16352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16352 : Upper (D 7) (R 7) [12,48,66,258,192,1] 13 := by
  apply FastRouting.sound _ _ [12,48,66,258,192,1] 13 (by decide) (choices 1) [1,32,128] r16352 c16352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3677
  · exact u3678
  · exact u3679

def b16353 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 13 50 70 266 208 160 97 161 289), lower := (rows 13 50 70 266 208 160 64 128 256), losses := [] }

theorem u16353 : Upper (D 7) (R 7) [12,48,66,258,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16354 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 70 296 19 33 192 192 448), lower := (rows 13 50 70 296 19 33 64 128 256), losses := [] }

theorem u16354 : Upper (D 7) (R 7) [12,48,66,288,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16355 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 2 },{ cop := 4, region := 196, targets := 32 }], pairs := [(0,1),(0,6),(2,5),(3,1)], upper := (rows 13 50 70 296 19 96 193 129 385), lower := (rows 13 50 70 296 19 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 10 20 32 0 149 277), good := (rows 413 442 415 296 411 32 0 128 256) }] }

theorem u16355 : Upper (D 7) (R 7) [12,48,66,288,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16356 : Route 9 := (fun mask => (mask,id))

def c16356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16356 : Upper (D 7) (R 7) [12,48,66,288,3,128] 13 := by
  apply FastRouting.sound _ _ [12,48,66,288,3,128] 13 (by decide) (choices 1) [1,128] r16356 c16356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3680
  · exact u3681

def b16357 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(3,6)], upper := (rows 13 50 70 296 81 33 194 130 386), lower := (rows 13 50 70 296 81 33 64 128 256), losses := [] }

theorem u16357 : Upper (D 7) (R 7) [12,48,66,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16358 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 296 81 34 193 129 385), lower := (rows 13 50 70 296 81 34 64 128 256), losses := [] }

theorem u16358 : Upper (D 7) (R 7) [12,48,66,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16359 : Route 9 := (fun mask => (mask,id))

def c16359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16359 : Upper (D 7) (R 7) [12,48,66,288,65,128] 13 := by
  apply FastRouting.sound _ _ [12,48,66,288,65,128] 13 (by decide) (choices 1) [1,2,128] r16359 c16359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3682
  · exact u3683
  · exact u3684

def b16360 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(3,0)], upper := (rows 13 50 70 296 145 33 194 194 450), lower := (rows 13 50 70 296 145 33 64 128 256), losses := [] }

theorem u16360 : Upper (D 7) (R 7) [12,48,66,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16361 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 50 70 296 145 34 193 193 449), lower := (rows 13 50 70 296 145 34 64 128 256), losses := [] }

theorem u16361 : Upper (D 7) (R 7) [12,48,66,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16362 : Route 9 := (fun mask => (mask,id))

def c16362 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16362 : Upper (D 7) (R 7) [12,48,66,288,129,64] 13 := by
  apply FastRouting.sound _ _ [12,48,66,288,129,64] 13 (by decide) (choices 1) [1,2,128] r16362 c16362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3685
  · exact u3686
  · exact u3687

def b16363 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 70 296 145 160 67 195 323), lower := (rows 13 50 70 296 145 160 64 128 256), losses := [] }

theorem u16363 : Upper (D 7) (R 7) [12,48,66,288,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16364 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(2,5),(3,1),(4,5)], upper := (rows 13 50 70 296 146 33 193 193 449), lower := (rows 13 50 70 296 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 8 18 0 97 161 289), good := (rows 461 470 86 456 150 449 64 128 256) }] }

theorem u16364 : Upper (D 7) (R 7) [12,48,66,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16365 : Route 9 := (fun mask => (mask,id))

def c16365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16365 : Upper (D 7) (R 7) [12,48,66,288,130,64] 13 := by
  apply FastRouting.sound _ _ [12,48,66,288,130,64] 13 (by decide) (choices 1) [1,128] r16365 c16365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3688
  · exact u3689

def b16366 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 70 296 146 160 65 193 321), lower := (rows 13 50 70 296 146 160 64 128 256), losses := [] }

theorem u16366 : Upper (D 7) (R 7) [12,48,66,288,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16367 : Route 9 := (fun mask => (mask,id))

def c16367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16367 : Upper (D 7) (R 7) [12,48,66,288,192,1] 13 := by
  apply FastRouting.sound _ _ [12,48,66,288,192,1] 13 (by decide) (choices 1) [1,2,128] r16367 c16367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3690
  · exact u3691
  · exact u3692

def b16368 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 296 208 34 193 129 385), lower := (rows 13 50 70 296 208 34 64 128 256), losses := [] }

theorem u16368 : Upper (D 7) (R 7) [12,48,66,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16369 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 13 50 70 296 208 160 67 131 259), lower := (rows 13 50 70 296 208 160 64 128 256), losses := [] }

theorem u16369 : Upper (D 7) (R 7) [12,48,66,288,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16370 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 460, targets := 1 }], pairs := [(1,6),(2,0),(3,0),(4,6)], upper := (rows 13 50 70 328 145 33 226 162 418), lower := (rows 13 50 70 328 145 33 64 128 256), losses := [] }

theorem u16370 : Upper (D 7) (R 7) [12,48,66,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16371 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 50 70 328 145 34 225 161 417), lower := (rows 13 50 70 328 145 34 64 128 256), losses := [] }

theorem u16371 : Upper (D 7) (R 7) [12,48,66,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16372 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 0, region := 178, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 13 50 70 328 145 160 99 163 291), lower := (rows 13 50 70 328 145 160 64 128 256), losses := [] }

theorem u16372 : Upper (D 7) (R 7) [12,48,66,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16373 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 70 392 19 33 224 224 480), lower := (rows 13 50 70 392 19 33 64 128 256), losses := [] }

theorem u16373 : Upper (D 7) (R 7) [12,48,66,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16374 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(1,7),(3,1),(4,7)], upper := (rows 13 50 70 392 19 96 225 161 417), lower := (rows 13 50 70 392 19 96 64 128 256), losses := [{ target := 7, region := (rows 1 3 4 8 17 100 64 0 256), good := (rows 63 50 102 264 19 96 96 0 256) }] }

theorem u16374 : Upper (D 7) (R 7) [12,48,66,384,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16375 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(1,6),(3,1),(4,6)], upper := (rows 13 50 70 392 19 160 97 225 353), lower := (rows 13 50 70 392 19 160 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 17 168 0 128 256), good := (rows 63 50 6 424 19 160 0 160 256) }] }

theorem u16375 : Upper (D 7) (R 7) [12,48,66,384,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16376 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(3,6)], upper := (rows 13 50 70 392 81 33 226 162 418), lower := (rows 13 50 70 392 81 33 64 128 256), losses := [] }

theorem u16376 : Upper (D 7) (R 7) [12,48,66,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16377 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 392 81 34 225 161 417), lower := (rows 13 50 70 392 81 34 64 128 256), losses := [] }

theorem u16377 : Upper (D 7) (R 7) [12,48,66,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16378 : Route 9 := (fun mask => (mask,id))

def c16378 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16378 : Upper (D 7) (R 7) [12,48,66,384,65,128] 13 := by
  apply FastRouting.sound _ _ [12,48,66,384,65,128] 13 (by decide) (choices 1) [1,2,32] r16378 c16378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3693
  · exact u3694
  · exact u3695

def b16379 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,7),(2,0),(2,7),(3,0)], upper := (rows 13 50 70 392 145 33 98 226 354), lower := (rows 13 50 70 392 145 33 64 128 256), losses := [] }

theorem u16379 : Upper (D 7) (R 7) [12,48,66,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16379
end Delivery.IrregularNine14.P07
