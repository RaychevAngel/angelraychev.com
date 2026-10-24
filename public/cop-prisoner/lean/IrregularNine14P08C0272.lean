import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0097
import IrregularNine14P08C0098

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16320 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 76 152 208 37 101 165 293), lower := (rows 259 35 76 152 208 32 64 128 256), losses := [] }

theorem u16320 : Upper (D 8) (R 8) [258,33,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16320 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16321 : Route 9 := (fun mask => (mask,id))

def c16321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16321 : Upper (D 8) (R 8) [258,33,72,160,96] 13 := by
  apply FastRouting.sound _ _ [258,33,72,160,96] 13 (by decide) (choices 1) [1,4,16,128] r16321 c16321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5861
  · exact u5862
  · exact u5863
  · exact u5864

def b16322 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 35 76 168 176 117 85 213 341), lower := (rows 259 35 76 168 176 32 64 128 256), losses := [] }

theorem u16322 : Upper (D 8) (R 8) [258,33,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16323 : Route 9 := (fun mask => (mask,id))

def c16323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16323 : Upper (D 8) (R 8) [258,33,72,160,192] 13 := by
  apply FastRouting.sound _ _ [258,33,72,160,192] 13 (by decide) (choices 1) [1,4,16] r16323 c16323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5865
  · exact u5866
  · exact u5867

def b16324 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 200 176 53 117 181 309), lower := (rows 259 35 76 200 176 32 64 128 256), losses := [] }

theorem u16324 : Upper (D 8) (R 8) [258,33,72,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m16325_8 : Upper (D 8) (R 8) [258,33,96,160,192,8] 13 :=
  permutation_upper _ _ _ [258,33,96,160,192,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5869

def r16325 : Route 9 := (fun mask => (mask,id))

def c16325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16325 : Upper (D 8) (R 8) [258,33,96,160,192] 13 := by
  apply FastRouting.sound _ _ [258,33,96,160,192] 13 (by decide) (choices 1) [1,4,8,16] r16325 c16325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5868
  · exact u5869
  · exact m16325_8
  · exact u5870

def b16326 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 13 56 49 224 192 192 448), lower := (rows 259 38 13 56 49 32 64 128 256), losses := [] }

theorem u16326 : Upper (D 8) (R 8) [258,36,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16327 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 13 56 81 224 224 224 480), lower := (rows 259 38 13 56 81 32 64 128 256), losses := [] }

theorem u16327 : Upper (D 8) (R 8) [258,36,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16328 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 13 56 112 225 193 193 449), lower := (rows 259 38 13 56 112 32 64 128 256), losses := [] }

theorem u16328 : Upper (D 8) (R 8) [258,36,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16328 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16329 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c16329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16329 : Upper (D 8) (R 8) [258,36,9,48,192] 13 := by
  apply FastRouting.sound _ _ [258,36,9,48,192] 13 (by decide) (choices 1) [1,64] r16329 c16329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5871
  · exact u5872

def b16330 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 13 88 49 224 224 224 480), lower := (rows 259 38 13 88 49 32 64 128 256), losses := [] }

theorem u16330 : Upper (D 8) (R 8) [258,36,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16331 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 13 88 81 160 224 160 416), lower := (rows 259 38 13 88 81 32 64 128 256), losses := [] }

theorem u16331 : Upper (D 8) (R 8) [258,36,9,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16332 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 13 88 112 161 225 161 417), lower := (rows 259 38 13 88 112 32 64 128 256), losses := [] }

theorem u16332 : Upper (D 8) (R 8) [258,36,9,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16333 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 13 88 145 224 224 224 480), lower := (rows 259 38 13 88 145 32 64 128 256), losses := [] }

theorem u16333 : Upper (D 8) (R 8) [258,36,9,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16334 : Route 9 := (fun mask => (mask,id))

def c16334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16334 : Upper (D 8) (R 8) [258,36,9,80,160] 13 := by
  apply FastRouting.sound _ _ [258,36,9,80,160] 13 (by decide) (choices 1) [1,64,128] r16334 c16334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5873
  · exact u5874
  · exact u5875

def b16335 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 13 88 208 161 225 161 417), lower := (rows 259 38 13 88 208 32 64 128 256), losses := [] }

theorem u16335 : Upper (D 8) (R 8) [258,36,9,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16336 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 13 104 49 240 208 208 464), lower := (rows 259 38 13 104 49 32 64 128 256), losses := [] }

theorem u16336 : Upper (D 8) (R 8) [258,36,9,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16337 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 13 104 81 176 240 176 432), lower := (rows 259 38 13 104 81 32 64 128 256), losses := [] }

theorem u16337 : Upper (D 8) (R 8) [258,36,9,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16338 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 13 104 112 177 209 145 401), lower := (rows 259 38 13 104 112 32 64 128 256), losses := [] }

theorem u16338 : Upper (D 8) (R 8) [258,36,9,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16339 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 13 104 145 240 240 240 496), lower := (rows 259 38 13 104 145 32 64 128 256), losses := [] }

theorem u16339 : Upper (D 8) (R 8) [258,36,9,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16340 : Route 9 := (fun mask => (mask,id))

def c16340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u16340 : Upper (D 8) (R 8) [258,36,9,96,160] 13 := by
  apply FastRouting.sound _ _ [258,36,9,96,160] 13 (by decide) (choices 1) [1,16,64,128] r16340 c16340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5876
  · exact u5877
  · exact u5878
  · exact u5879

def r16341 : Route 9 := (fun mask => (mask,id))

def c16341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16341 : Upper (D 8) (R 8) [258,36,9,96,192] 13 := by
  apply FastRouting.sound _ _ [258,36,9,96,192] 13 (by decide) (choices 1) [1,16,128] r16341 c16341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5880
  · exact u5881
  · exact u5882

def b16342 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 13 200 49 240 240 240 496), lower := (rows 259 38 13 200 49 32 64 128 256), losses := [] }

theorem u16342 : Upper (D 8) (R 8) [258,36,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16343 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 13 200 81 176 240 176 432), lower := (rows 259 38 13 200 81 32 64 128 256), losses := [] }

theorem u16343 : Upper (D 8) (R 8) [258,36,9,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16344 : Route 9 := (fun mask => (mask,id))

def c16344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16344 : Upper (D 8) (R 8) [258,36,9,192,96] 13 := by
  apply FastRouting.sound _ _ [258,36,9,192,96] 13 (by decide) (choices 1) [1,16,128] r16344 c16344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5883
  · exact u5884
  · exact u5885

def b16345 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 13 200 208 49 113 177 305), lower := (rows 259 38 13 200 208 32 64 128 256), losses := [] }

theorem u16345 : Upper (D 8) (R 8) [258,36,9,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16346 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 22, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 28 41 49 224 192 192 448), lower := (rows 259 38 28 41 49 32 64 128 256), losses := [] }

theorem u16346 : Upper (D 8) (R 8) [258,36,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16347 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 28 41 81 224 224 224 480), lower := (rows 259 38 28 41 81 32 64 128 256), losses := [] }

theorem u16347 : Upper (D 8) (R 8) [258,36,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16348 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 28 41 112 225 193 193 449), lower := (rows 259 38 28 41 112 32 64 128 256), losses := [] }

theorem u16348 : Upper (D 8) (R 8) [258,36,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16349 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c16349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16349 : Upper (D 8) (R 8) [258,36,24,33,192] 13 := by
  apply FastRouting.sound _ _ [258,36,24,33,192] 13 (by decide) (choices 1) [1,64] r16349 c16349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5886
  · exact u5887

def b16350 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 28 73 81 160 224 160 416), lower := (rows 259 38 28 73 81 32 64 128 256), losses := [] }

theorem u16350 : Upper (D 8) (R 8) [258,36,24,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16351 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 28 73 112 161 225 161 417), lower := (rows 259 38 28 73 112 32 64 128 256), losses := [] }

theorem u16351 : Upper (D 8) (R 8) [258,36,24,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16352 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 28 73 145 224 224 224 480), lower := (rows 259 38 28 73 145 32 64 128 256), losses := [] }

theorem u16352 : Upper (D 8) (R 8) [258,36,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16353 : Route 9 := (fun mask => (mask,id))

def c16353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16353 : Upper (D 8) (R 8) [258,36,24,65,160] 13 := by
  apply FastRouting.sound _ _ [258,36,24,65,160] 13 (by decide) (choices 1) [1,64,128] r16353 c16353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5888
  · exact u5889
  · exact u5890

def b16354 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 28 73 208 161 225 161 417), lower := (rows 259 38 28 73 208 32 64 128 256), losses := [] }

theorem u16354 : Upper (D 8) (R 8) [258,36,24,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16355 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 28 104 112 161 193 129 385), lower := (rows 259 38 28 104 112 32 64 128 256), losses := [] }

theorem u16355 : Upper (D 8) (R 8) [258,36,24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16356 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 28 104 176 225 193 193 449), lower := (rows 259 38 28 104 176 32 64 128 256), losses := [] }

theorem u16356 : Upper (D 8) (R 8) [258,36,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16357 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 28 104 208 161 225 161 417), lower := (rows 259 38 28 104 208 32 64 128 256), losses := [] }

theorem u16357 : Upper (D 8) (R 8) [258,36,24,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16358 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 38 28 200 208 33 97 161 289), lower := (rows 259 38 28 200 208 32 64 128 256), losses := [] }

theorem u16358 : Upper (D 8) (R 8) [258,36,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16359 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 69 25 56 224 224 224 480), lower := (rows 259 38 69 25 56 32 64 128 256), losses := [] }

theorem u16359 : Upper (D 8) (R 8) [258,36,65,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16360 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 25 88 160 224 160 416), lower := (rows 259 38 69 25 88 32 64 128 256), losses := [] }

theorem u16360 : Upper (D 8) (R 8) [258,36,65,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16361 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 25 112 168 232 168 424), lower := (rows 259 38 69 25 112 32 64 128 256), losses := [] }

theorem u16361 : Upper (D 8) (R 8) [258,36,65,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16362 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 69 25 152 224 224 224 480), lower := (rows 259 38 69 25 152 32 64 128 256), losses := [] }

theorem u16362 : Upper (D 8) (R 8) [258,36,65,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16363 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 25 176 232 232 232 488), lower := (rows 259 38 69 25 176 32 64 128 256), losses := [] }

theorem u16363 : Upper (D 8) (R 8) [258,36,65,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16364 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 25 208 168 232 168 424), lower := (rows 259 38 69 25 208 32 64 128 256), losses := [] }

theorem u16364 : Upper (D 8) (R 8) [258,36,65,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16365 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 38 69 41 56 240 208 208 464), lower := (rows 259 38 69 41 56 32 64 128 256), losses := [] }

theorem u16365 : Upper (D 8) (R 8) [258,36,65,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16366 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 41 88 176 240 176 432), lower := (rows 259 38 69 41 88 32 64 128 256), losses := [] }

theorem u16366 : Upper (D 8) (R 8) [258,36,65,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16367 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 41 112 184 216 152 408), lower := (rows 259 38 69 41 112 32 64 128 256), losses := [] }

theorem u16367 : Upper (D 8) (R 8) [258,36,65,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16368 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 41 152 240 240 240 496), lower := (rows 259 38 69 41 152 32 64 128 256), losses := [] }

theorem u16368 : Upper (D 8) (R 8) [258,36,65,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16368 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16369 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 41 176 248 216 216 472), lower := (rows 259 38 69 41 176 32 64 128 256), losses := [] }

theorem u16369 : Upper (D 8) (R 8) [258,36,65,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16370 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 41 208 184 248 184 440), lower := (rows 259 38 69 41 208 32 64 128 256), losses := [] }

theorem u16370 : Upper (D 8) (R 8) [258,36,65,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16371 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 56 56 225 193 193 449), lower := (rows 259 38 69 56 56 32 64 128 256), losses := [] }

theorem u16371 : Upper (D 8) (R 8) [258,36,65,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16371 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16372 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 38 69 56 81 168 232 168 424), lower := (rows 259 38 69 56 81 32 64 128 256), losses := [] }

theorem u16372 : Upper (D 8) (R 8) [258,36,65,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16373 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 69 56 88 161 225 161 417), lower := (rows 259 38 69 56 88 32 64 128 256), losses := [] }

theorem u16373 : Upper (D 8) (R 8) [258,36,65,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16374 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 56 112 169 201 137 393), lower := (rows 259 38 69 56 112 32 64 128 256), losses := [] }

theorem u16374 : Upper (D 8) (R 8) [258,36,65,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16375 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 56 145 232 232 232 488), lower := (rows 259 38 69 56 145 32 64 128 256), losses := [] }

theorem u16375 : Upper (D 8) (R 8) [258,36,65,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16376 : Route 9 := (fun mask => (mask,id))

def c16376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16376 : Upper (D 8) (R 8) [258,36,65,48,136] 13 := by
  apply FastRouting.sound _ _ [258,36,65,48,136] 13 (by decide) (choices 1) [1,64,128] r16376 c16376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5891
  · exact u5892
  · exact u5893

def b16377 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 56 176 233 201 201 457), lower := (rows 259 38 69 56 176 32 64 128 256), losses := [] }

theorem u16377 : Upper (D 8) (R 8) [258,36,65,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16378 : Route 9 := (fun mask => (mask,id))

def c16378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16378 : Upper (D 8) (R 8) [258,36,65,48,192] 13 := by
  apply FastRouting.sound _ _ [258,36,65,48,192] 13 (by decide) (choices 1) [1,8,128] r16378 c16378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5894
  · exact u5895
  · exact u5896

def b16379 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 73 152 176 240 176 432), lower := (rows 259 38 69 73 152 32 64 128 256), losses := [] }

theorem u16379 : Upper (D 8) (R 8) [258,36,65,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16379
end Delivery.IrregularNine14.P08
