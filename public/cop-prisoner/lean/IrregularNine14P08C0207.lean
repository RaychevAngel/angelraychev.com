import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0068
import IrregularNine14P08C0069

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12420 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 108, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 28 44 145 97 97 225 353), lower := (rows 67 386 28 44 145 32 64 128 256), losses := [] }

theorem u12420 : Upper (D 8) (R 8) [66,384,24,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12421 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 28 44 176 97 97 225 353), lower := (rows 67 386 28 44 176 32 64 128 256), losses := [] }

theorem u12421 : Upper (D 8) (R 8) [66,384,24,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12422 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 28 44 208 33 97 161 289), lower := (rows 67 386 28 44 208 32 64 128 256), losses := [] }

theorem u12422 : Upper (D 8) (R 8) [66,384,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12423 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 28 73 176 37 101 165 293), lower := (rows 67 386 28 73 176 32 64 128 256), losses := [] }

theorem u12423 : Upper (D 8) (R 8) [66,384,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12424 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 28 76 176 33 97 161 289), lower := (rows 67 386 28 76 176 32 64 128 256), losses := [] }

theorem u12424 : Upper (D 8) (R 8) [66,384,24,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12425 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 108, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 28 104 145 37 101 165 293), lower := (rows 67 386 28 104 145 32 64 128 256), losses := [] }

theorem u12425 : Upper (D 8) (R 8) [66,384,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12426 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 386 28 104 148 33 97 161 289), lower := (rows 67 386 28 104 148 32 64 128 256), losses := [] }

theorem u12426 : Upper (D 8) (R 8) [66,384,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12427 : Route 9 := (fun mask => (mask,id))

def c12427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12427 : Upper (D 8) (R 8) [66,384,24,96,160] 13 := by
  apply FastRouting.sound _ _ [66,384,24,96,160] 13 (by decide) (choices 1) [1,4] r12427 c12427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4110
  · exact u4111

def b12428 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 386 37 41 52 248 216 216 472), lower := (rows 67 386 37 41 52 32 64 128 256), losses := [] }

theorem u12428 : Upper (D 8) (R 8) [66,384,33,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12429 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 386 37 41 84 184 248 184 440), lower := (rows 67 386 37 41 84 32 64 128 256), losses := [] }

theorem u12429 : Upper (D 8) (R 8) [66,384,33,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12430 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 386 37 41 112 188 220 156 412), lower := (rows 67 386 37 41 112 32 64 128 256), losses := [] }

theorem u12430 : Upper (D 8) (R 8) [66,384,33,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12431 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 386 37 41 148 120 120 248 376), lower := (rows 67 386 37 41 148 32 64 128 256), losses := [] }

theorem u12431 : Upper (D 8) (R 8) [66,384,33,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12432 : PairBound 9 := { available := 92, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 386 37 41 176 124 92 220 348), lower := (rows 67 386 37 41 176 32 64 128 256), losses := [] }

theorem u12432 : Upper (D 8) (R 8) [66,384,33,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12433 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 386 37 41 208 60 124 188 316), lower := (rows 67 386 37 41 208 32 64 128 256), losses := [] }

theorem u12433 : Upper (D 8) (R 8) [66,384,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12433 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12434 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 386 37 44 56 241 209 209 465), lower := (rows 67 386 37 44 56 32 64 128 256), losses := [] }

theorem u12434 : Upper (D 8) (R 8) [66,384,33,36,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12435 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 386 37 44 88 177 241 177 433), lower := (rows 67 386 37 44 88 32 64 128 256), losses := [] }

theorem u12435 : Upper (D 8) (R 8) [66,384,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12436 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 386 37 44 112 185 217 153 409), lower := (rows 67 386 37 44 112 32 64 128 256), losses := [] }

theorem u12436 : Upper (D 8) (R 8) [66,384,33,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12437 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 386 37 44 152 113 113 241 369), lower := (rows 67 386 37 44 152 32 64 128 256), losses := [] }

theorem u12437 : Upper (D 8) (R 8) [66,384,33,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12438 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 386 37 44 176 121 89 217 345), lower := (rows 67 386 37 44 176 32 64 128 256), losses := [] }

theorem u12438 : Upper (D 8) (R 8) [66,384,33,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12439 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 386 37 44 208 57 121 185 313), lower := (rows 67 386 37 44 208 32 64 128 256), losses := [] }

theorem u12439 : Upper (D 8) (R 8) [66,384,33,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12440 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 386 37 56 56 229 197 197 453), lower := (rows 67 386 37 56 56 32 64 128 256), losses := [] }

theorem u12440 : Upper (D 8) (R 8) [66,384,33,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12441 : PairBound 9 := { available := 172, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 37 56 81 172 236 172 428), lower := (rows 67 386 37 56 81 32 64 128 256), losses := [] }

theorem u12441 : Upper (D 8) (R 8) [66,384,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12442 : Route 9 := (fun mask => (mask,id))

def c12442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12442 : Upper (D 8) (R 8) [66,384,33,48,68] 13 := by
  apply FastRouting.sound _ _ [66,384,33,48,68] 13 (by decide) (choices 1) [1,8,128] r12442 c12442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4112
  · exact u4113
  · exact u4114

def b12443 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 37 56 88 165 229 165 421), lower := (rows 67 386 37 56 88 32 64 128 256), losses := [] }

theorem u12443 : Upper (D 8) (R 8) [66,384,33,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12444 : PairBound 9 := { available := 141, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 386 37 56 112 173 205 141 397), lower := (rows 67 386 37 56 112 32 64 128 256), losses := [] }

theorem u12444 : Upper (D 8) (R 8) [66,384,33,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12445 : PairBound 9 := { available := 108, camps := [{ cop := 4, region := 108, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 37 56 145 108 108 236 364), lower := (rows 67 386 37 56 145 32 64 128 256), losses := [] }

theorem u12445 : Upper (D 8) (R 8) [66,384,33,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12446 : Route 9 := (fun mask => (mask,id))

def c12446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12446 : Upper (D 8) (R 8) [66,384,33,48,132] 13 := by
  apply FastRouting.sound _ _ [66,384,33,48,132] 13 (by decide) (choices 1) [1,8,64] r12446 c12446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4115
  · exact u4116
  · exact u4117

def b12447 : PairBound 9 := { available := 101, camps := [{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7)], upper := (rows 67 386 37 56 152 101 101 229 357), lower := (rows 67 386 37 56 152 32 64 128 256), losses := [] }

theorem u12447 : Upper (D 8) (R 8) [66,384,33,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12448 : PairBound 9 := { available := 77, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 386 37 56 176 109 77 205 333), lower := (rows 67 386 37 56 176 32 64 128 256), losses := [] }

theorem u12448 : Upper (D 8) (R 8) [66,384,33,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12449 : Route 9 := (fun mask => (mask,id))

def c12449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12449 : Upper (D 8) (R 8) [66,384,33,48,192] 13 := by
  apply FastRouting.sound _ _ [66,384,33,48,192] 13 (by decide) (choices 1) [1,4,8] r12449 c12449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4118
  · exact u4119
  · exact u4120

def b12450 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 37 73 148 56 120 184 312), lower := (rows 67 386 37 73 148 32 64 128 256), losses := [] }

theorem u12450 : Upper (D 8) (R 8) [66,384,33,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12451 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 37 73 152 52 116 180 308), lower := (rows 67 386 37 73 152 32 64 128 256), losses := [] }

theorem u12451 : Upper (D 8) (R 8) [66,384,33,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12452 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 37 73 176 60 124 188 316), lower := (rows 67 386 37 73 176 32 64 128 256), losses := [] }

theorem u12452 : Upper (D 8) (R 8) [66,384,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12452 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12453 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 108, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 37 76 145 56 120 184 312), lower := (rows 67 386 37 76 145 32 64 128 256), losses := [] }

theorem u12453 : Upper (D 8) (R 8) [66,384,33,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12454 : Route 9 := (fun mask => (mask,id))

def c12454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12454 : Upper (D 8) (R 8) [66,384,33,68,136] 13 := by
  apply FastRouting.sound _ _ [66,384,33,68,136] 13 (by decide) (choices 1) [1,16] r12454 c12454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4121
  · exact u4122

def r12455 : Route 9 := (fun mask => (mask,id))

def c12455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12455 : Upper (D 8) (R 8) [66,384,33,68,160] 13 := by
  apply FastRouting.sound _ _ [66,384,33,68,160] 13 (by decide) (choices 1) [1,8,16] r12455 c12455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4123
  · exact u4124
  · exact u4125

def b12456 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 108, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 37 88 145 44 108 172 300), lower := (rows 67 386 37 88 145 32 64 128 256), losses := [] }

theorem u12456 : Upper (D 8) (R 8) [66,384,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12457 : Route 9 := (fun mask => (mask,id))

def c12457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12457 : Upper (D 8) (R 8) [66,384,33,80,132] 13 := by
  apply FastRouting.sound _ _ [66,384,33,80,132] 13 (by decide) (choices 1) [1,8] r12457 c12457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4126
  · exact u4127

def b12458 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 37 88 152 37 101 165 293), lower := (rows 67 386 37 88 152 32 64 128 256), losses := [] }

theorem u12458 : Upper (D 8) (R 8) [66,384,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12459 : Route 9 := (fun mask => (mask,id))

def c12459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12459 : Upper (D 8) (R 8) [66,384,33,80,160] 13 := by
  apply FastRouting.sound _ _ [66,384,33,80,160] 13 (by decide) (choices 1) [1,4,8] r12459 c12459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4128
  · exact u4129
  · exact u4130

def b12460 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 108, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 37 104 145 60 124 188 316), lower := (rows 67 386 37 104 145 32 64 128 256), losses := [] }

theorem u12460 : Upper (D 8) (R 8) [66,384,33,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12461 : Route 9 := (fun mask => (mask,id))

def c12461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12461 : Upper (D 8) (R 8) [66,384,33,96,132] 13 := by
  apply FastRouting.sound _ _ [66,384,33,96,132] 13 (by decide) (choices 1) [1,8,16] r12461 c12461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4131
  · exact u4132
  · exact u4133

def r12462 : Route 9 := (fun mask => (mask,id))

def c12462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12462 : Upper (D 8) (R 8) [66,384,33,96,136] 13 := by
  apply FastRouting.sound _ _ [66,384,33,96,136] 13 (by decide) (choices 1) [1,4,16] r12462 c12462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4134
  · exact u4135
  · exact u4136

def r12463 : Route 9 := (fun mask => (mask,id))

def c12463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12463 : Upper (D 8) (R 8) [66,384,33,96,160] 13 := by
  apply FastRouting.sound _ _ [66,384,33,96,160] 13 (by decide) (choices 1) [1,4,8,16] r12463 c12463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4137
  · exact u4138
  · exact u4139
  · exact u4140

def b12464 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 44 112 177 209 145 401), lower := (rows 67 386 44 44 112 32 64 128 256), losses := [] }

theorem u12464 : Upper (D 8) (R 8) [66,384,40,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12465 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 44 176 113 81 209 337), lower := (rows 67 386 44 44 176 32 64 128 256), losses := [] }

theorem u12465 : Upper (D 8) (R 8) [66,384,40,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12466 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 44 208 49 113 177 305), lower := (rows 67 386 44 44 208 32 64 128 256), losses := [] }

theorem u12466 : Upper (D 8) (R 8) [66,384,40,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12467 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 56 84 161 225 161 417), lower := (rows 67 386 44 56 84 32 64 128 256), losses := [] }

theorem u12467 : Upper (D 8) (R 8) [66,384,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12468 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 56 112 165 197 133 389), lower := (rows 67 386 44 56 112 32 64 128 256), losses := [] }

theorem u12468 : Upper (D 8) (R 8) [66,384,40,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12469 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 56 148 97 97 225 353), lower := (rows 67 386 44 56 148 32 64 128 256), losses := [] }

theorem u12469 : Upper (D 8) (R 8) [66,384,40,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12470 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 56 176 101 69 197 325), lower := (rows 67 386 44 56 176 32 64 128 256), losses := [] }

theorem u12470 : Upper (D 8) (R 8) [66,384,40,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12471 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 56 208 37 101 165 293), lower := (rows 67 386 44 56 208 32 64 128 256), losses := [] }

theorem u12471 : Upper (D 8) (R 8) [66,384,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12472 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 44 73 148 49 113 177 305), lower := (rows 67 386 44 73 148 32 64 128 256), losses := [] }

theorem u12472 : Upper (D 8) (R 8) [66,384,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12473 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 44 73 176 53 117 181 309), lower := (rows 67 386 44 73 176 32 64 128 256), losses := [] }

theorem u12473 : Upper (D 8) (R 8) [66,384,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12474 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 44 76 176 49 113 177 305), lower := (rows 67 386 44 76 176 32 64 128 256), losses := [] }

theorem u12474 : Upper (D 8) (R 8) [66,384,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12475 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 108, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 44 88 145 37 101 165 293), lower := (rows 67 386 44 88 145 32 64 128 256), losses := [] }

theorem u12475 : Upper (D 8) (R 8) [66,384,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12476 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 44 88 148 33 97 161 289), lower := (rows 67 386 44 88 148 32 64 128 256), losses := [] }

theorem u12476 : Upper (D 8) (R 8) [66,384,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12477 : Route 9 := (fun mask => (mask,id))

def c12477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12477 : Upper (D 8) (R 8) [66,384,40,80,160] 13 := by
  apply FastRouting.sound _ _ [66,384,40,80,160] 13 (by decide) (choices 1) [1,4] r12477 c12477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4141
  · exact u4142

def b12478 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 104 148 49 113 177 305), lower := (rows 67 386 44 104 148 32 64 128 256), losses := [] }

theorem u12478 : Upper (D 8) (R 8) [66,384,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12479 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 104 176 53 85 149 277), lower := (rows 67 386 44 104 176 32 64 128 256), losses := [] }

theorem u12479 : Upper (D 8) (R 8) [66,384,40,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12479
end Delivery.IrregularNine14.P08
