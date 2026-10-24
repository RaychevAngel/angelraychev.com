import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0024
import IrregularNine14P08C0025

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7920 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 388 41 145 112 112 240 368), lower := (rows 7 74 388 41 145 32 64 128 256), losses := [] }

theorem u7920 : Upper (D 8) (R 8) [6,72,384,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7920 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7921 : Route 9 := (fun mask => (mask,id))

def c7921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7921 : Upper (D 8) (R 8) [6,72,384,33,160] 13 := by
  apply FastRouting.sound _ _ [6,72,384,33,160] 13 (by decide) (choices 1) [1,16,64] r7921 c7921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1461
  · exact u1462
  · exact u1463

def r7922 : Route 9 := (fun mask => (mask,id))

def c7922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7922 : Upper (D 8) (R 8) [6,72,384,33,192] 13 := by
  apply FastRouting.sound _ _ [6,72,384,33,192] 13 (by decide) (choices 1) [1,16] r7922 c7922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1464
  · exact u1465

def b7923 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 74 388 56 49 225 225 225 481), lower := (rows 7 74 388 56 49 32 64 128 256), losses := [] }

theorem u7923 : Upper (D 8) (R 8) [6,72,384,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7924 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 388 56 81 161 225 161 417), lower := (rows 7 74 388 56 81 32 64 128 256), losses := [] }

theorem u7924 : Upper (D 8) (R 8) [6,72,384,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7924 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7925 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 388 56 112 161 225 161 417), lower := (rows 7 74 388 56 112 32 64 128 256), losses := [] }

theorem u7925 : Upper (D 8) (R 8) [6,72,384,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7926 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 388 56 145 97 97 225 353), lower := (rows 7 74 388 56 145 32 64 128 256), losses := [] }

theorem u7926 : Upper (D 8) (R 8) [6,72,384,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7927 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 74 388 56 176 97 97 225 353), lower := (rows 7 74 388 56 176 32 64 128 256), losses := [] }

theorem u7927 : Upper (D 8) (R 8) [6,72,384,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7928 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 388 56 208 33 97 161 289), lower := (rows 7 74 388 56 208 32 64 128 256), losses := [] }

theorem u7928 : Upper (D 8) (R 8) [6,72,384,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7929 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 164 25 25 480 480 480 480), lower := (rows 7 98 164 25 25 32 64 128 256), losses := [] }

theorem u7929 : Upper (D 8) (R 8) [6,96,160,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7930 : PairBound 9 := { available := 456, camps := [{ cop := 3, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 164 25 49 488 456 456 456), lower := (rows 7 98 164 25 49 32 64 128 256), losses := [] }

theorem u7930 : Upper (D 8) (R 8) [6,96,160,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m7931_128 : Upper (D 8) (R 8) [6,96,160,17,40,128] 13 :=
  permutation_upper _ _ _ [6,96,160,17,40,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1467

def r7931 : Route 9 := (fun mask => (mask,id))

def c7931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7931 : Upper (D 8) (R 8) [6,96,160,17,40] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,40] 13 (by decide) (choices 1) [1,64,128,256] r7931 c7931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1466
  · exact u1467
  · exact m7931_128
  · exact u1468

def b7932 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 164 25 81 424 488 424 424), lower := (rows 7 98 164 25 81 32 64 128 256), losses := [] }

theorem u7932 : Upper (D 8) (R 8) [6,96,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7933 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 25 88 417 481 417 417), lower := (rows 7 98 164 25 88 32 64 128 256), losses := [] }

theorem u7933 : Upper (D 8) (R 8) [6,96,160,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7934 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 164 25 112 425 457 393 393), lower := (rows 7 98 164 25 112 32 64 128 256), losses := [] }

theorem u7934 : Upper (D 8) (R 8) [6,96,160,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7935 : PairBound 9 := { available := 297, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 164 25 208 297 361 425 297), lower := (rows 7 98 164 25 208 32 64 128 256), losses := [] }

theorem u7935 : Upper (D 8) (R 8) [6,96,160,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7936 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 164 25 273 232 232 232 488), lower := (rows 7 98 164 25 273 32 64 128 256), losses := [] }

theorem u7936 : Upper (D 8) (R 8) [6,96,160,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m7937_128 : Upper (D 8) (R 8) [6,96,160,17,264,128] 13 :=
  permutation_upper _ _ _ [6,96,160,17,264,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1470

def r7937 : Route 9 := (fun mask => (mask,id))

def c7937 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7937 : Upper (D 8) (R 8) [6,96,160,17,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,264] 13 (by decide) (choices 1) [1,64,128] r7937 c7937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1469
  · exact u1470
  · exact m7937_128

theorem m7938_128 : Upper (D 8) (R 8) [6,96,160,17,288,128] 13 :=
  permutation_upper _ _ _ [6,96,160,17,288,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1473

def r7938 : Route 9 := (fun mask => (mask,id))

def c7938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7938 : Upper (D 8) (R 8) [6,96,160,17,288] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,288] 13 (by decide) (choices 1) [1,8,64,128] r7938 c7938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1471
  · exact u1472
  · exact u1473
  · exact m7938_128

def b7939 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 164 25 336 169 233 169 425), lower := (rows 7 98 164 25 336 32 64 128 256), losses := [] }

theorem u7939 : Upper (D 8) (R 8) [6,96,160,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7940 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 164 41 88 433 465 401 401), lower := (rows 7 98 164 41 88 32 64 128 256), losses := [] }

theorem u7940 : Upper (D 8) (R 8) [6,96,160,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7940 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7941 : PairBound 9 := { available := 281, camps := [{ cop := 3, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 164 41 208 313 345 409 281), lower := (rows 7 98 164 41 208 32 64 128 256), losses := [] }

theorem u7941 : Upper (D 8) (R 8) [6,96,160,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7942 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 164 41 273 248 216 216 472), lower := (rows 7 98 164 41 273 32 64 128 256), losses := [] }

theorem u7942 : Upper (D 8) (R 8) [6,96,160,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7943 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 164 41 280 241 209 209 465), lower := (rows 7 98 164 41 280 32 64 128 256), losses := [] }

theorem u7943 : Upper (D 8) (R 8) [6,96,160,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7944 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 164 41 336 185 217 153 409), lower := (rows 7 98 164 41 336 32 64 128 256), losses := [] }

theorem u7944 : Upper (D 8) (R 8) [6,96,160,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7945 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 164 56 81 425 457 393 393), lower := (rows 7 98 164 56 81 32 64 128 256), losses := [] }

theorem u7945 : Upper (D 8) (R 8) [6,96,160,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7946 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 164 56 88 417 449 385 385), lower := (rows 7 98 164 56 88 32 64 128 256), losses := [] }

theorem u7946 : Upper (D 8) (R 8) [6,96,160,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7947 : Route 9 := (fun mask => (mask,id))

def c7947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7947 : Upper (D 8) (R 8) [6,96,160,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48,192] 13 (by decide) (choices 1) [1,8,256] r7947 c7947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1474
  · exact u1475
  · exact u1476

theorem m7948_128 : Upper (D 8) (R 8) [6,96,160,48,257,128] 13 :=
  permutation_upper _ _ _ [6,96,160,48,257,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1479

def r7948 : Route 9 := (fun mask => (mask,id))

def c7948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7948 : Upper (D 8) (R 8) [6,96,160,48,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48,257] 13 (by decide) (choices 1) [1,8,64,128] r7948 c7948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1477
  · exact u1478
  · exact u1479
  · exact m7948_128

theorem m7949_128 : Upper (D 8) (R 8) [6,96,160,48,264,128] 13 :=
  permutation_upper _ _ _ [6,96,160,48,264,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1481

def r7949 : Route 9 := (fun mask => (mask,id))

def c7949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7949 : Upper (D 8) (R 8) [6,96,160,48,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48,264] 13 (by decide) (choices 1) [1,64,128] r7949 c7949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1480
  · exact u1481
  · exact m7949_128

def r7950 : Route 9 := (fun mask => (mask,id))

def c7950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7950 : Upper (D 8) (R 8) [6,96,160,48,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48,320] 13 (by decide) (choices 1) [1,8,128] r7950 c7950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1482
  · exact u1483
  · exact u1484

def b7951 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 164 73 152 305 369 433 305), lower := (rows 7 98 164 73 152 32 64 128 256), losses := [] }

theorem u7951 : Upper (D 8) (R 8) [6,96,160,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7952 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 164 73 273 184 248 184 440), lower := (rows 7 98 164 73 273 32 64 128 256), losses := [] }

theorem u7952 : Upper (D 8) (R 8) [6,96,160,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7953 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 164 73 280 177 241 177 433), lower := (rows 7 98 164 73 280 32 64 128 256), losses := [] }

theorem u7953 : Upper (D 8) (R 8) [6,96,160,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7954 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 164 73 304 185 217 153 409), lower := (rows 7 98 164 73 304 32 64 128 256), losses := [] }

theorem u7954 : Upper (D 8) (R 8) [6,96,160,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7955 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 164 73 400 57 121 185 313), lower := (rows 7 98 164 73 400 32 64 128 256), losses := [] }

theorem u7955 : Upper (D 8) (R 8) [6,96,160,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7956 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 88 152 289 353 417 289), lower := (rows 7 98 164 88 152 32 64 128 256), losses := [] }

theorem u7956 : Upper (D 8) (R 8) [6,96,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7957 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 164 88 176 297 329 393 265), lower := (rows 7 98 164 88 176 32 64 128 256), losses := [] }

theorem u7957 : Upper (D 8) (R 8) [6,96,160,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7958 : Route 9 := (fun mask => (mask,id))

def c7958 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7958 : Upper (D 8) (R 8) [6,96,160,80,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,257] 13 (by decide) (choices 1) [1,8,128] r7958 c7958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1485
  · exact u1486
  · exact u1487

def b7959 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 88 280 161 225 161 417), lower := (rows 7 98 164 88 280 32 64 128 256), losses := [] }

theorem u7959 : Upper (D 8) (R 8) [6,96,160,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7960 : Route 9 := (fun mask => (mask,id))

def c7960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7960 : Upper (D 8) (R 8) [6,96,160,80,288] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,288] 13 (by decide) (choices 1) [1,8,128] r7960 c7960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1488
  · exact u1489
  · exact u1490

def r7961 : Route 9 := (fun mask => (mask,id))

def c7961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7961 : Upper (D 8) (R 8) [6,96,160,80,384] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,384] 13 (by decide) (choices 1) [1,8] r7961 c7961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1491
  · exact u1492

def b7962 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 164 104 273 185 217 153 409), lower := (rows 7 98 164 104 273 32 64 128 256), losses := [] }

theorem u7962 : Upper (D 8) (R 8) [6,96,160,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7963 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 164 104 280 177 209 145 401), lower := (rows 7 98 164 104 280 32 64 128 256), losses := [] }

theorem u7963 : Upper (D 8) (R 8) [6,96,160,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7964 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 164 104 400 57 89 153 281), lower := (rows 7 98 164 104 400 32 64 128 256), losses := [] }

theorem u7964 : Upper (D 8) (R 8) [6,96,160,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7965 : Route 9 := (fun mask => (mask,id))

def c7965 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7965 : Upper (D 8) (R 8) [6,96,160,192,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,257] 13 (by decide) (choices 1) [1,8,16] r7965 c7965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1493
  · exact u1494
  · exact u1495

def r7966 : Route 9 := (fun mask => (mask,id))

def c7966 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7966 : Upper (D 8) (R 8) [6,96,160,192,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,264] 13 (by decide) (choices 1) [1,16] r7966 c7966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1496
  · exact u1497

def r7967 : Route 9 := (fun mask => (mask,id))

def c7967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7967 : Upper (D 8) (R 8) [6,96,160,192,288] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,288] 13 (by decide) (choices 1) [1,8,16] r7967 c7967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1498
  · exact u1499
  · exact u1500

def b7968 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 25 56 224 224 224 480), lower := (rows 7 98 261 25 56 32 64 128 256), losses := [] }

theorem u7968 : Upper (D 8) (R 8) [6,96,257,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7969 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 261 25 88 160 224 160 416), lower := (rows 7 98 261 25 88 32 64 128 256), losses := [] }

theorem u7969 : Upper (D 8) (R 8) [6,96,257,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7970 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 25 152 224 224 224 480), lower := (rows 7 98 261 25 152 32 64 128 256), losses := [] }

theorem u7970 : Upper (D 8) (R 8) [6,96,257,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7971 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 25 176 232 232 232 488), lower := (rows 7 98 261 25 176 32 64 128 256), losses := [] }

theorem u7971 : Upper (D 8) (R 8) [6,96,257,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7972 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 25 208 168 232 168 424), lower := (rows 7 98 261 25 208 32 64 128 256), losses := [] }

theorem u7972 : Upper (D 8) (R 8) [6,96,257,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7973 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 41 56 240 208 208 464), lower := (rows 7 98 261 41 56 32 64 128 256), losses := [] }

theorem u7973 : Upper (D 8) (R 8) [6,96,257,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7974 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 41 88 176 240 176 432), lower := (rows 7 98 261 41 88 32 64 128 256), losses := [] }

theorem u7974 : Upper (D 8) (R 8) [6,96,257,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7975 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 41 152 240 240 240 496), lower := (rows 7 98 261 41 152 32 64 128 256), losses := [] }

theorem u7975 : Upper (D 8) (R 8) [6,96,257,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7976 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 41 176 248 216 216 472), lower := (rows 7 98 261 41 176 32 64 128 256), losses := [] }

theorem u7976 : Upper (D 8) (R 8) [6,96,257,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7977 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 41 208 184 248 184 440), lower := (rows 7 98 261 41 208 32 64 128 256), losses := [] }

theorem u7977 : Upper (D 8) (R 8) [6,96,257,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7978 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 56 56 225 193 193 449), lower := (rows 7 98 261 56 56 32 64 128 256), losses := [] }

theorem u7978 : Upper (D 8) (R 8) [6,96,257,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7979 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 170, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 56 81 168 232 168 424), lower := (rows 7 98 261 56 81 32 64 128 256), losses := [] }

theorem u7979 : Upper (D 8) (R 8) [6,96,257,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u7979
end Delivery.IrregularNine14.P08
