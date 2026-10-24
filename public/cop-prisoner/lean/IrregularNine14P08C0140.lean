import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0029
import IrregularNine14P08C0030

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8400 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 280 208 161 225 161 417), lower := (rows 35 14 69 280 208 32 64 128 256), losses := [] }

theorem u8400 : Upper (D 8) (R 8) [34,12,65,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8401 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 69 296 49 240 208 208 464), lower := (rows 35 14 69 296 49 32 64 128 256), losses := [] }

theorem u8401 : Upper (D 8) (R 8) [34,12,65,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8402 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 69 296 81 176 240 176 432), lower := (rows 35 14 69 296 81 32 64 128 256), losses := [] }

theorem u8402 : Upper (D 8) (R 8) [34,12,65,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8402 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8403 : Route 9 := (fun mask => (mask,id))

def c8403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8403 : Upper (D 8) (R 8) [34,12,65,288,96] 13 := by
  apply FastRouting.sound _ _ [34,12,65,288,96] 13 (by decide) (choices 1) [1,16,128] r8403 c8403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1786
  · exact u1787
  · exact u1788

def b8404 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 296 145 240 240 240 496), lower := (rows 35 14 69 296 145 32 64 128 256), losses := [] }

theorem u8404 : Upper (D 8) (R 8) [34,12,65,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8405 : Route 9 := (fun mask => (mask,id))

def c8405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8405 : Upper (D 8) (R 8) [34,12,65,288,160] 13 := by
  apply FastRouting.sound _ _ [34,12,65,288,160] 13 (by decide) (choices 1) [1,16,64,128] r8405 c8405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1789
  · exact u1790
  · exact u1791
  · exact u1792

def r8406 : Route 9 := (fun mask => (mask,id))

def c8406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8406 : Upper (D 8) (R 8) [34,12,65,288,192] 13 := by
  apply FastRouting.sound _ _ [34,12,65,288,192] 13 (by decide) (choices 1) [1,16,128] r8406 c8406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1793
  · exact u1794
  · exact u1795

def b8407 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 69 392 49 240 240 240 496), lower := (rows 35 14 69 392 49 32 64 128 256), losses := [] }

theorem u8407 : Upper (D 8) (R 8) [34,12,65,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8408 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 69 392 81 176 240 176 432), lower := (rows 35 14 69 392 81 32 64 128 256), losses := [] }

theorem u8408 : Upper (D 8) (R 8) [34,12,65,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8409 : Route 9 := (fun mask => (mask,id))

def c8409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8409 : Upper (D 8) (R 8) [34,12,65,384,96] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,96] 13 (by decide) (choices 1) [1,16,128] r8409 c8409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1796
  · exact u1797
  · exact u1798

def b8410 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 392 145 112 112 240 368), lower := (rows 35 14 69 392 145 32 64 128 256), losses := [] }

theorem u8410 : Upper (D 8) (R 8) [34,12,65,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8411 : Route 9 := (fun mask => (mask,id))

def c8411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8411 : Upper (D 8) (R 8) [34,12,65,384,160] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,160] 13 (by decide) (choices 1) [1,16,64] r8411 c8411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1799
  · exact u1800
  · exact u1801

def r8412 : Route 9 := (fun mask => (mask,id))

def c8412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8412 : Upper (D 8) (R 8) [34,12,65,384,192] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,192] 13 (by decide) (choices 1) [1,16] r8412 c8412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1802
  · exact u1803

def b8413 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 84 168 49 481 449 449 449), lower := (rows 35 14 84 168 49 32 64 128 256), losses := [] }

theorem u8413 : Upper (D 8) (R 8) [34,12,80,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8414 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 168 81 417 481 417 417), lower := (rows 35 14 84 168 81 32 64 128 256), losses := [] }

theorem u8414 : Upper (D 8) (R 8) [34,12,80,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8415 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 168 112 417 449 385 385), lower := (rows 35 14 84 168 112 32 64 128 256), losses := [] }

theorem u8415 : Upper (D 8) (R 8) [34,12,80,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8416 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 84 168 145 353 353 481 353), lower := (rows 35 14 84 168 145 32 64 128 256), losses := [] }

theorem u8416 : Upper (D 8) (R 8) [34,12,80,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8417 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 84 168 176 353 321 449 321), lower := (rows 35 14 84 168 176 32 64 128 256), losses := [] }

theorem u8417 : Upper (D 8) (R 8) [34,12,80,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8418 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 168 208 289 353 417 289), lower := (rows 35 14 84 168 208 32 64 128 256), losses := [] }

theorem u8418 : Upper (D 8) (R 8) [34,12,80,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8419 : Route 9 := (fun mask => (mask,id))

def c8419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8419 : Upper (D 8) (R 8) [34,12,80,160,257] 13 := by
  apply FastRouting.sound _ _ [34,12,80,160,257] 13 (by decide) (choices 1) [1,64,128] r8419 c8419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1804
  · exact u1805
  · exact u1806

def r8420 : Route 9 := (fun mask => (mask,id))

def c8420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8420 : Upper (D 8) (R 8) [34,12,80,160,288] 13 := by
  apply FastRouting.sound _ _ [34,12,80,160,288] 13 (by decide) (choices 1) [1,64,128] r8420 c8420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1807
  · exact u1808
  · exact u1809

def b8421 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 168 336 161 225 161 417), lower := (rows 35 14 84 168 336 32 64 128 256), losses := [] }

theorem u8421 : Upper (D 8) (R 8) [34,12,80,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8422 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 84 168 400 97 97 225 353), lower := (rows 35 14 84 168 400 32 64 128 256), losses := [] }

theorem u8422 : Upper (D 8) (R 8) [34,12,80,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8423 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 84 265 49 224 224 224 480), lower := (rows 35 14 84 265 49 32 64 128 256), losses := [] }

theorem u8423 : Upper (D 8) (R 8) [34,12,80,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8424 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 265 81 160 224 160 416), lower := (rows 35 14 84 265 81 32 64 128 256), losses := [] }

theorem u8424 : Upper (D 8) (R 8) [34,12,80,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8425 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 265 112 161 225 161 417), lower := (rows 35 14 84 265 112 32 64 128 256), losses := [] }

theorem u8425 : Upper (D 8) (R 8) [34,12,80,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8426 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 84 265 145 224 224 224 480), lower := (rows 35 14 84 265 145 32 64 128 256), losses := [] }

theorem u8426 : Upper (D 8) (R 8) [34,12,80,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8427 : Route 9 := (fun mask => (mask,id))

def c8427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8427 : Upper (D 8) (R 8) [34,12,80,257,160] 13 := by
  apply FastRouting.sound _ _ [34,12,80,257,160] 13 (by decide) (choices 1) [1,64,128] r8427 c8427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1810
  · exact u1811
  · exact u1812

def b8428 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 265 208 161 225 161 417), lower := (rows 35 14 84 265 208 32 64 128 256), losses := [] }

theorem u8428 : Upper (D 8) (R 8) [34,12,80,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8429 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 84 296 49 225 193 193 449), lower := (rows 35 14 84 296 49 32 64 128 256), losses := [] }

theorem u8429 : Upper (D 8) (R 8) [34,12,80,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8430 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 296 81 161 225 161 417), lower := (rows 35 14 84 296 81 32 64 128 256), losses := [] }

theorem u8430 : Upper (D 8) (R 8) [34,12,80,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8431 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 296 112 161 193 129 385), lower := (rows 35 14 84 296 112 32 64 128 256), losses := [] }

theorem u8431 : Upper (D 8) (R 8) [34,12,80,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8432 : Route 9 := (fun mask => (mask,id))

def c8432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8432 : Upper (D 8) (R 8) [34,12,80,288,129] 13 := by
  apply FastRouting.sound _ _ [34,12,80,288,129] 13 (by decide) (choices 1) [1,64,128] r8432 c8432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1813
  · exact u1814
  · exact u1815

def r8433 : Route 9 := (fun mask => (mask,id))

def c8433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8433 : Upper (D 8) (R 8) [34,12,80,288,160] 13 := by
  apply FastRouting.sound _ _ [34,12,80,288,160] 13 (by decide) (choices 1) [1,64,128] r8433 c8433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1816
  · exact u1817
  · exact u1818

def b8434 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 296 208 161 225 161 417), lower := (rows 35 14 84 296 208 32 64 128 256), losses := [] }

theorem u8434 : Upper (D 8) (R 8) [34,12,80,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8435 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 84 392 49 225 225 225 481), lower := (rows 35 14 84 392 49 32 64 128 256), losses := [] }

theorem u8435 : Upper (D 8) (R 8) [34,12,80,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8436 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 392 81 161 225 161 417), lower := (rows 35 14 84 392 81 32 64 128 256), losses := [] }

theorem u8436 : Upper (D 8) (R 8) [34,12,80,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8437 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 392 112 161 225 161 417), lower := (rows 35 14 84 392 112 32 64 128 256), losses := [] }

theorem u8437 : Upper (D 8) (R 8) [34,12,80,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8438 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 84 392 145 97 97 225 353), lower := (rows 35 14 84 392 145 32 64 128 256), losses := [] }

theorem u8438 : Upper (D 8) (R 8) [34,12,80,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8439 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 84 392 176 97 97 225 353), lower := (rows 35 14 84 392 176 32 64 128 256), losses := [] }

theorem u8439 : Upper (D 8) (R 8) [34,12,80,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8440 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 392 208 33 97 161 289), lower := (rows 35 14 84 392 208 32 64 128 256), losses := [] }

theorem u8440 : Upper (D 8) (R 8) [34,12,80,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8441 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 100 265 49 240 208 208 464), lower := (rows 35 14 100 265 49 32 64 128 256), losses := [] }

theorem u8441 : Upper (D 8) (R 8) [34,12,96,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8442 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 100 265 81 176 240 176 432), lower := (rows 35 14 100 265 81 32 64 128 256), losses := [] }

theorem u8442 : Upper (D 8) (R 8) [34,12,96,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8443 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 100 265 112 177 209 145 401), lower := (rows 35 14 100 265 112 32 64 128 256), losses := [] }

theorem u8443 : Upper (D 8) (R 8) [34,12,96,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8444 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 100 265 145 240 240 240 496), lower := (rows 35 14 100 265 145 32 64 128 256), losses := [] }

theorem u8444 : Upper (D 8) (R 8) [34,12,96,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8445 : Route 9 := (fun mask => (mask,id))

def c8445 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8445 : Upper (D 8) (R 8) [34,12,96,257,160] 13 := by
  apply FastRouting.sound _ _ [34,12,96,257,160] 13 (by decide) (choices 1) [1,16,64,128] r8445 c8445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1819
  · exact u1820
  · exact u1821
  · exact u1822

def r8446 : Route 9 := (fun mask => (mask,id))

def c8446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8446 : Upper (D 8) (R 8) [34,12,96,257,192] 13 := by
  apply FastRouting.sound _ _ [34,12,96,257,192] 13 (by decide) (choices 1) [1,16,128] r8446 c8446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1823
  · exact u1824
  · exact u1825

def b8447 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 100 280 49 225 193 193 449), lower := (rows 35 14 100 280 49 32 64 128 256), losses := [] }

theorem u8447 : Upper (D 8) (R 8) [34,12,96,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8448 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 100 280 81 161 225 161 417), lower := (rows 35 14 100 280 81 32 64 128 256), losses := [] }

theorem u8448 : Upper (D 8) (R 8) [34,12,96,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8449 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 100 280 112 161 193 129 385), lower := (rows 35 14 100 280 112 32 64 128 256), losses := [] }

theorem u8449 : Upper (D 8) (R 8) [34,12,96,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8450 : Route 9 := (fun mask => (mask,id))

def c8450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8450 : Upper (D 8) (R 8) [34,12,96,272,129] 13 := by
  apply FastRouting.sound _ _ [34,12,96,272,129] 13 (by decide) (choices 1) [1,64,128] r8450 c8450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1826
  · exact u1827
  · exact u1828

def r8451 : Route 9 := (fun mask => (mask,id))

def c8451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8451 : Upper (D 8) (R 8) [34,12,96,272,160] 13 := by
  apply FastRouting.sound _ _ [34,12,96,272,160] 13 (by decide) (choices 1) [1,64,128] r8451 c8451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1829
  · exact u1830
  · exact u1831

def b8452 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 100 280 208 161 225 161 417), lower := (rows 35 14 100 280 208 32 64 128 256), losses := [] }

theorem u8452 : Upper (D 8) (R 8) [34,12,96,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8452 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8453 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 100 392 49 241 209 209 465), lower := (rows 35 14 100 392 49 32 64 128 256), losses := [] }

theorem u8453 : Upper (D 8) (R 8) [34,12,96,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8454 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 100 392 81 177 241 177 433), lower := (rows 35 14 100 392 81 32 64 128 256), losses := [] }

theorem u8454 : Upper (D 8) (R 8) [34,12,96,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8455 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 100 392 112 177 209 145 401), lower := (rows 35 14 100 392 112 32 64 128 256), losses := [] }

theorem u8455 : Upper (D 8) (R 8) [34,12,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8456 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 35 14 100 392 145 113 113 241 369), lower := (rows 35 14 100 392 145 32 64 128 256), losses := [] }

theorem u8456 : Upper (D 8) (R 8) [34,12,96,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8457 : Route 9 := (fun mask => (mask,id))

def c8457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8457 : Upper (D 8) (R 8) [34,12,96,384,160] 13 := by
  apply FastRouting.sound _ _ [34,12,96,384,160] 13 (by decide) (choices 1) [1,16,64] r8457 c8457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1832
  · exact u1833
  · exact u1834

def r8458 : Route 9 := (fun mask => (mask,id))

def c8458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8458 : Upper (D 8) (R 8) [34,12,96,384,192] 13 := by
  apply FastRouting.sound _ _ [34,12,96,384,192] 13 (by decide) (choices 1) [1,16] r8458 c8458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1835
  · exact u1836

def b8459 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 196 265 49 240 240 240 496), lower := (rows 35 14 196 265 49 32 64 128 256), losses := [] }

theorem u8459 : Upper (D 8) (R 8) [34,12,192,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u8459
end Delivery.IrregularNine14.P08
