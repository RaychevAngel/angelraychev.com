import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0098
import IrregularNine14P08C0099

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16380 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 73 176 184 248 184 440), lower := (rows 259 38 69 73 176 32 64 128 256), losses := [] }

theorem u16380 : Upper (D 8) (R 8) [258,36,65,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16381 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 88 145 168 232 168 424), lower := (rows 259 38 69 88 145 32 64 128 256), losses := [] }

theorem u16381 : Upper (D 8) (R 8) [258,36,65,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16382 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 69 88 152 161 225 161 417), lower := (rows 259 38 69 88 152 32 64 128 256), losses := [] }

theorem u16382 : Upper (D 8) (R 8) [258,36,65,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16383 : Route 9 := (fun mask => (mask,id))

def c16383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16383 : Upper (D 8) (R 8) [258,36,65,80,160] 13 := by
  apply FastRouting.sound _ _ [258,36,65,80,160] 13 (by decide) (choices 1) [1,8,128] r16383 c16383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5897
  · exact u5898
  · exact u5899

def b16384 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 104 145 184 248 184 440), lower := (rows 259 38 69 104 145 32 64 128 256), losses := [] }

theorem u16384 : Upper (D 8) (R 8) [258,36,65,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16385 : Route 9 := (fun mask => (mask,id))

def c16385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16385 : Upper (D 8) (R 8) [258,36,65,96,136] 13 := by
  apply FastRouting.sound _ _ [258,36,65,96,136] 13 (by decide) (choices 1) [1,16,128] r16385 c16385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5900
  · exact u5901
  · exact u5902

def r16386 : Route 9 := (fun mask => (mask,id))

def c16386 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16386 : Upper (D 8) (R 8) [258,36,65,96,160] 13 := by
  apply FastRouting.sound _ _ [258,36,65,96,160] 13 (by decide) (choices 1) [1,8,16,128] r16386 c16386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5903
  · exact u5904
  · exact u5905
  · exact u5906

def b16387 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 69 137 152 112 112 240 368), lower := (rows 259 38 69 137 152 32 64 128 256), losses := [] }

theorem u16387 : Upper (D 8) (R 8) [258,36,65,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16388 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 137 176 120 120 248 376), lower := (rows 259 38 69 137 176 32 64 128 256), losses := [] }

theorem u16388 : Upper (D 8) (R 8) [258,36,65,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16389 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 137 208 56 120 184 312), lower := (rows 259 38 69 137 208 32 64 128 256), losses := [] }

theorem u16389 : Upper (D 8) (R 8) [258,36,65,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16390 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 152 152 97 97 225 353), lower := (rows 259 38 69 152 152 32 64 128 256), losses := [] }

theorem u16390 : Upper (D 8) (R 8) [258,36,65,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16391 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 69 152 176 105 105 233 361), lower := (rows 259 38 69 152 176 32 64 128 256), losses := [] }

theorem u16391 : Upper (D 8) (R 8) [258,36,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16392 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 69 152 208 41 105 169 297), lower := (rows 259 38 69 152 208 32 64 128 256), losses := [] }

theorem u16392 : Upper (D 8) (R 8) [258,36,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16393 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 168 176 121 89 217 345), lower := (rows 259 38 69 168 176 32 64 128 256), losses := [] }

theorem u16393 : Upper (D 8) (R 8) [258,36,65,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16394 : Route 9 := (fun mask => (mask,id))

def c16394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16394 : Upper (D 8) (R 8) [258,36,65,160,192] 13 := by
  apply FastRouting.sound _ _ [258,36,65,160,192] 13 (by decide) (choices 1) [1,8,16] r16394 c16394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5907
  · exact u5908
  · exact u5909

def b16395 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 76 25 49 224 224 224 480), lower := (rows 259 38 76 25 49 32 64 128 256), losses := [] }

theorem u16395 : Upper (D 8) (R 8) [258,36,72,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16396 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 76 25 81 160 224 160 416), lower := (rows 259 38 76 25 81 32 64 128 256), losses := [] }

theorem u16396 : Upper (D 8) (R 8) [258,36,72,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16397 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 25 112 161 225 161 417), lower := (rows 259 38 76 25 112 32 64 128 256), losses := [] }

theorem u16397 : Upper (D 8) (R 8) [258,36,72,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16398 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 76 25 145 224 224 224 480), lower := (rows 259 38 76 25 145 32 64 128 256), losses := [] }

theorem u16398 : Upper (D 8) (R 8) [258,36,72,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16399 : Route 9 := (fun mask => (mask,id))

def c16399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16399 : Upper (D 8) (R 8) [258,36,72,17,160] 13 := by
  apply FastRouting.sound _ _ [258,36,72,17,160] 13 (by decide) (choices 1) [1,64,128] r16399 c16399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5910
  · exact u5911
  · exact u5912

def b16400 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 25 208 161 225 161 417), lower := (rows 259 38 76 25 208 32 64 128 256), losses := [] }

theorem u16400 : Upper (D 8) (R 8) [258,36,72,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16401 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 38 76 41 49 240 208 208 464), lower := (rows 259 38 76 41 49 32 64 128 256), losses := [] }

theorem u16401 : Upper (D 8) (R 8) [258,36,72,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16402 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 259 38 76 41 81 176 240 176 432), lower := (rows 259 38 76 41 81 32 64 128 256), losses := [] }

theorem u16402 : Upper (D 8) (R 8) [258,36,72,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16402 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16403 : Route 9 := (fun mask => (mask,id))

def c16403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16403 : Upper (D 8) (R 8) [258,36,72,33,96] 13 := by
  apply FastRouting.sound _ _ [258,36,72,33,96] 13 (by decide) (choices 1) [1,16,128] r16403 c16403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5913
  · exact u5914
  · exact u5915

def r16404 : Route 9 := (fun mask => (mask,id))

def c16404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u16404 : Upper (D 8) (R 8) [258,36,72,33,129] 13 := by
  apply FastRouting.sound _ _ [258,36,72,33,129] 13 (by decide) (choices 1) [16,64,128] r16404 c16404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5916
  · exact u5917
  · exact u5918

def r16405 : Route 9 := (fun mask => (mask,id))

def c16405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u16405 : Upper (D 8) (R 8) [258,36,72,33,160] 13 := by
  apply FastRouting.sound _ _ [258,36,72,33,160] 13 (by decide) (choices 1) [1,16,64,128] r16405 c16405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5919
  · exact u5920
  · exact u5921
  · exact u5922

def r16406 : Route 9 := (fun mask => (mask,id))

def c16406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16406 : Upper (D 8) (R 8) [258,36,72,33,192] 13 := by
  apply FastRouting.sound _ _ [258,36,72,33,192] 13 (by decide) (choices 1) [1,16,128] r16406 c16406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5923
  · exact u5924
  · exact u5925

def b16407 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 76 56 49 225 193 193 449), lower := (rows 259 38 76 56 49 32 64 128 256), losses := [] }

theorem u16407 : Upper (D 8) (R 8) [258,36,72,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16408 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 56 81 161 225 161 417), lower := (rows 259 38 76 56 81 32 64 128 256), losses := [] }

theorem u16408 : Upper (D 8) (R 8) [258,36,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16409 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 56 112 161 193 129 385), lower := (rows 259 38 76 56 112 32 64 128 256), losses := [] }

theorem u16409 : Upper (D 8) (R 8) [258,36,72,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16409 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16410 : Route 9 := (fun mask => (mask,id))

def c16410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16410 : Upper (D 8) (R 8) [258,36,72,48,129] 13 := by
  apply FastRouting.sound _ _ [258,36,72,48,129] 13 (by decide) (choices 1) [1,64,128] r16410 c16410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5926
  · exact u5927
  · exact u5928

def b16411 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 76 56 176 225 193 193 449), lower := (rows 259 38 76 56 176 32 64 128 256), losses := [] }

theorem u16411 : Upper (D 8) (R 8) [258,36,72,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16412 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 56 208 161 225 161 417), lower := (rows 259 38 76 56 208 32 64 128 256), losses := [] }

theorem u16412 : Upper (D 8) (R 8) [258,36,72,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16412 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16413 : Route 9 := (fun mask => (mask,id))

def c16413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u16413 : Upper (D 8) (R 8) [258,36,72,129,33] 13 := by
  apply FastRouting.sound _ _ [258,36,72,129,33] 13 (by decide) (choices 1) [16,64,128] r16413 c16413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5929
  · exact u5930
  · exact u5931

def b16414 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 259 38 76 137 81 176 240 176 432), lower := (rows 259 38 76 137 81 32 64 128 256), losses := [] }

theorem u16414 : Upper (D 8) (R 8) [258,36,72,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16415 : Route 9 := (fun mask => (mask,id))

def c16415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16415 : Upper (D 8) (R 8) [258,36,72,129,96] 13 := by
  apply FastRouting.sound _ _ [258,36,72,129,96] 13 (by decide) (choices 1) [1,16,128] r16415 c16415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5932
  · exact u5933
  · exact u5934

def b16416 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 38 76 137 145 112 112 240 368), lower := (rows 259 38 76 137 145 32 64 128 256), losses := [] }

theorem u16416 : Upper (D 8) (R 8) [258,36,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16417 : Route 9 := (fun mask => (mask,id))

def c16417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16417 : Upper (D 8) (R 8) [258,36,72,129,160] 13 := by
  apply FastRouting.sound _ _ [258,36,72,129,160] 13 (by decide) (choices 1) [1,16,64] r16417 c16417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5935
  · exact u5936
  · exact u5937

def r16418 : Route 9 := (fun mask => (mask,id))

def c16418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16418 : Upper (D 8) (R 8) [258,36,72,129,192] 13 := by
  apply FastRouting.sound _ _ [258,36,72,129,192] 13 (by decide) (choices 1) [1,16] r16418 c16418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5938
  · exact u5939

def r16419 : Route 9 := (fun mask => (mask,id))

def c16419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16419 : Upper (D 8) (R 8) [258,36,72,144,33] 13 := by
  apply FastRouting.sound _ _ [258,36,72,144,33] 13 (by decide) (choices 1) [1,64,128] r16419 c16419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5940
  · exact u5941
  · exact u5942

def b16420 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 152 81 161 225 161 417), lower := (rows 259 38 76 152 81 32 64 128 256), losses := [] }

theorem u16420 : Upper (D 8) (R 8) [258,36,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16421 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 152 112 161 225 161 417), lower := (rows 259 38 76 152 112 32 64 128 256), losses := [] }

theorem u16421 : Upper (D 8) (R 8) [258,36,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16422 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 152 145 97 97 225 353), lower := (rows 259 38 76 152 145 32 64 128 256), losses := [] }

theorem u16422 : Upper (D 8) (R 8) [258,36,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16423 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 152 176 97 97 225 353), lower := (rows 259 38 76 152 176 32 64 128 256), losses := [] }

theorem u16423 : Upper (D 8) (R 8) [258,36,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16424 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 38 76 152 208 33 97 161 289), lower := (rows 259 38 76 152 208 32 64 128 256), losses := [] }

theorem u16424 : Upper (D 8) (R 8) [258,36,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16425 : Route 9 := (fun mask => (mask,id))

def c16425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u16425 : Upper (D 8) (R 8) [258,36,72,160,33] 13 := by
  apply FastRouting.sound _ _ [258,36,72,160,33] 13 (by decide) (choices 1) [1,16,64,128] r16425 c16425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5943
  · exact u5944
  · exact u5945
  · exact u5946

def b16426 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 259 38 76 168 81 177 241 177 433), lower := (rows 259 38 76 168 81 32 64 128 256), losses := [] }

theorem u16426 : Upper (D 8) (R 8) [258,36,72,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16427 : Route 9 := (fun mask => (mask,id))

def c16427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16427 : Upper (D 8) (R 8) [258,36,72,160,96] 13 := by
  apply FastRouting.sound _ _ [258,36,72,160,96] 13 (by decide) (choices 1) [1,16,128] r16427 c16427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5947
  · exact u5948
  · exact u5949

def r16428 : Route 9 := (fun mask => (mask,id))

def c16428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16428 : Upper (D 8) (R 8) [258,36,72,160,129] 13 := by
  apply FastRouting.sound _ _ [258,36,72,160,129] 13 (by decide) (choices 1) [1,16,64] r16428 c16428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5950
  · exact u5951
  · exact u5952

def b16429 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 76 168 176 113 81 209 337), lower := (rows 259 38 76 168 176 32 64 128 256), losses := [] }

theorem u16429 : Upper (D 8) (R 8) [258,36,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16430 : Route 9 := (fun mask => (mask,id))

def c16430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16430 : Upper (D 8) (R 8) [258,36,72,160,192] 13 := by
  apply FastRouting.sound _ _ [258,36,72,160,192] 13 (by decide) (choices 1) [1,16] r16430 c16430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5953
  · exact u5954

def b16431 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 196 25 25 224 224 224 480), lower := (rows 259 38 196 25 25 32 64 128 256), losses := [] }

theorem u16431 : Upper (D 8) (R 8) [258,36,192,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16432 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 196 25 49 232 232 232 488), lower := (rows 259 38 196 25 49 32 64 128 256), losses := [] }

theorem u16432 : Upper (D 8) (R 8) [258,36,192,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16433 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c16433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16433 : Upper (D 8) (R 8) [258,36,192,17,40] 13 := by
  apply FastRouting.sound _ _ [258,36,192,17,40] 13 (by decide) (choices 1) [1,64] r16433 c16433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5955
  · exact u5956

def b16434 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 230, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 196 25 81 168 232 168 424), lower := (rows 259 38 196 25 81 32 64 128 256), losses := [] }

theorem u16434 : Upper (D 8) (R 8) [258,36,192,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16435 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 196 25 88 161 225 161 417), lower := (rows 259 38 196 25 88 32 64 128 256), losses := [] }

theorem u16435 : Upper (D 8) (R 8) [258,36,192,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16436 : Route 9 := (fun mask => (mask,id))

def c16436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16436 : Upper (D 8) (R 8) [258,36,192,17,96] 13 := by
  apply FastRouting.sound _ _ [258,36,192,17,96] 13 (by decide) (choices 1) [1,8,128] r16436 c16436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5957
  · exact u5958
  · exact u5959

def b16437 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 196 25 208 41 105 169 297), lower := (rows 259 38 196 25 208 32 64 128 256), losses := [] }

theorem u16437 : Upper (D 8) (R 8) [258,36,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16438 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 38 196 41 49 248 216 216 472), lower := (rows 259 38 196 41 49 32 64 128 256), losses := [] }

theorem u16438 : Upper (D 8) (R 8) [258,36,192,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16439 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 196 41 56 241 209 209 465), lower := (rows 259 38 196 41 56 32 64 128 256), losses := [] }

theorem u16439 : Upper (D 8) (R 8) [258,36,192,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16439
end Delivery.IrregularNine14.P08
