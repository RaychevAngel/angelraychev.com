import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0030
import IrregularNine14P08C0031

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8580 : Route 9 := (fun mask => (mask,id))

def c8580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8580 : Upper (D 8) (R 8) [34,65,24,132,288] 13 := by
  apply FastRouting.sound _ _ [34,65,24,132,288] 13 (by decide) (choices 1) [1,64,128] r8580 c8580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1846
  · exact u1847
  · exact u1848

def b8581 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 140 336 161 225 161 417), lower := (rows 35 67 28 140 336 32 64 128 256), losses := [] }

theorem u8581 : Upper (D 8) (R 8) [34,65,24,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8581 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8582 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 140 400 97 97 225 353), lower := (rows 35 67 28 140 400 32 64 128 256), losses := [] }

theorem u8582 : Upper (D 8) (R 8) [34,65,24,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8583 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 168 176 357 325 453 325), lower := (rows 35 67 28 168 176 32 64 128 256), losses := [] }

theorem u8583 : Upper (D 8) (R 8) [34,65,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8584 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 168 208 293 357 421 293), lower := (rows 35 67 28 168 208 32 64 128 256), losses := [] }

theorem u8584 : Upper (D 8) (R 8) [34,65,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8585 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 168 273 228 228 228 484), lower := (rows 35 67 28 168 273 32 64 128 256), losses := [] }

theorem u8585 : Upper (D 8) (R 8) [34,65,24,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8586 : Route 9 := (fun mask => (mask,id))

def c8586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8586 : Upper (D 8) (R 8) [34,65,24,160,260] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,260] 13 (by decide) (choices 1) [1,64,128] r8586 c8586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1849
  · exact u1850
  · exact u1851

def r8587 : Route 9 := (fun mask => (mask,id))

def c8587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8587 : Upper (D 8) (R 8) [34,65,24,160,288] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,288] 13 (by decide) (choices 1) [1,4,64,128] r8587 c8587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1852
  · exact u1853
  · exact u1854
  · exact u1855

def r8588 : Route 9 := (fun mask => (mask,id))

def c8588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8588 : Upper (D 8) (R 8) [34,65,24,160,320] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,320] 13 (by decide) (choices 1) [1,4,128] r8588 c8588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1856
  · exact u1857
  · exact u1858

def b8589 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 168 400 101 101 229 357), lower := (rows 35 67 28 168 400 32 64 128 256), losses := [] }

theorem u8589 : Upper (D 8) (R 8) [34,65,24,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8590 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 200 273 164 228 164 420), lower := (rows 35 67 28 200 273 32 64 128 256), losses := [] }

theorem u8590 : Upper (D 8) (R 8) [34,65,24,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8591 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 200 276 161 225 161 417), lower := (rows 35 67 28 200 276 32 64 128 256), losses := [] }

theorem u8591 : Upper (D 8) (R 8) [34,65,24,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8591 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8592 : Route 9 := (fun mask => (mask,id))

def c8592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8592 : Upper (D 8) (R 8) [34,65,24,192,288] 13 := by
  apply FastRouting.sound _ _ [34,65,24,192,288] 13 (by decide) (choices 1) [1,4,128] r8592 c8592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1859
  · exact u1860
  · exact u1861

def b8593 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 200 400 37 101 165 293), lower := (rows 35 67 28 200 400 32 64 128 256), losses := [] }

theorem u8593 : Upper (D 8) (R 8) [34,65,24,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8594 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 44 88 432 464 400 400), lower := (rows 35 67 37 44 88 32 64 128 256), losses := [] }

theorem u8594 : Upper (D 8) (R 8) [34,65,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8594 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8595 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 44 152 496 464 464 464), lower := (rows 35 67 37 44 152 32 64 128 256), losses := [] }

theorem u8595 : Upper (D 8) (R 8) [34,65,33,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8595 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8596 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 44 208 440 472 408 408), lower := (rows 35 67 37 44 208 32 64 128 256), losses := [] }

theorem u8596 : Upper (D 8) (R 8) [34,65,33,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8597 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 44 280 240 208 208 464), lower := (rows 35 67 37 44 280 32 64 128 256), losses := [] }

theorem u8597 : Upper (D 8) (R 8) [34,65,33,36,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8598 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 44 336 184 216 152 408), lower := (rows 35 67 37 44 336 32 64 128 256), losses := [] }

theorem u8598 : Upper (D 8) (R 8) [34,65,33,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8599 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 44 400 248 216 216 472), lower := (rows 35 67 37 44 400 32 64 128 256), losses := [] }

theorem u8599 : Upper (D 8) (R 8) [34,65,33,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8600 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 56 84 424 456 392 392), lower := (rows 35 67 37 56 84 32 64 128 256), losses := [] }

theorem u8600 : Upper (D 8) (R 8) [34,65,33,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8601 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 56 148 488 456 456 456), lower := (rows 35 67 37 56 148 32 64 128 256), losses := [] }

theorem u8601 : Upper (D 8) (R 8) [34,65,33,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8602 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 56 152 484 452 452 452), lower := (rows 35 67 37 56 152 32 64 128 256), losses := [] }

theorem u8602 : Upper (D 8) (R 8) [34,65,33,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8603 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 56 208 428 460 396 396), lower := (rows 35 67 37 56 208 32 64 128 256), losses := [] }

theorem u8603 : Upper (D 8) (R 8) [34,65,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8604 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 56 276 232 200 200 456), lower := (rows 35 67 37 56 276 32 64 128 256), losses := [] }

theorem u8604 : Upper (D 8) (R 8) [34,65,33,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8605 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 56 280 228 196 196 452), lower := (rows 35 67 37 56 280 32 64 128 256), losses := [] }

theorem u8605 : Upper (D 8) (R 8) [34,65,33,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8606 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 56 336 172 204 140 396), lower := (rows 35 67 37 56 336 32 64 128 256), losses := [] }

theorem u8606 : Upper (D 8) (R 8) [34,65,33,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8607 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 56 400 236 204 204 460), lower := (rows 35 67 37 56 400 32 64 128 256), losses := [] }

theorem u8607 : Upper (D 8) (R 8) [34,65,33,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8607 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8608 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 76 152 432 496 432 432), lower := (rows 35 67 37 76 152 32 64 128 256), losses := [] }

theorem u8608 : Upper (D 8) (R 8) [34,65,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8609 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 76 176 440 472 408 408), lower := (rows 35 67 37 76 176 32 64 128 256), losses := [] }

theorem u8609 : Upper (D 8) (R 8) [34,65,33,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8610 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 76 280 176 240 176 432), lower := (rows 35 67 37 76 280 32 64 128 256), losses := [] }

theorem u8610 : Upper (D 8) (R 8) [34,65,33,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8611 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 76 304 184 216 152 408), lower := (rows 35 67 37 76 304 32 64 128 256), losses := [] }

theorem u8611 : Upper (D 8) (R 8) [34,65,33,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8612 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 76 400 184 248 184 440), lower := (rows 35 67 37 76 400 32 64 128 256), losses := [] }

theorem u8612 : Upper (D 8) (R 8) [34,65,33,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8613 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 88 148 424 488 424 424), lower := (rows 35 67 37 88 148 32 64 128 256), losses := [] }

theorem u8613 : Upper (D 8) (R 8) [34,65,33,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8614 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 88 176 428 460 396 396), lower := (rows 35 67 37 88 176 32 64 128 256), losses := [] }

theorem u8614 : Upper (D 8) (R 8) [34,65,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8615 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 88 276 168 232 168 424), lower := (rows 35 67 37 88 276 32 64 128 256), losses := [] }

theorem u8615 : Upper (D 8) (R 8) [34,65,33,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8615 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8616 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 88 304 172 204 140 396), lower := (rows 35 67 37 88 304 32 64 128 256), losses := [] }

theorem u8616 : Upper (D 8) (R 8) [34,65,33,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8617 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 88 400 172 236 172 428), lower := (rows 35 67 37 88 400 32 64 128 256), losses := [] }

theorem u8617 : Upper (D 8) (R 8) [34,65,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8618 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 140 176 376 344 472 344), lower := (rows 35 67 37 140 176 32 64 128 256), losses := [] }

theorem u8618 : Upper (D 8) (R 8) [34,65,33,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8619 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 140 208 312 376 440 312), lower := (rows 35 67 37 140 208 32 64 128 256), losses := [] }

theorem u8619 : Upper (D 8) (R 8) [34,65,33,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8620 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 140 280 240 240 240 496), lower := (rows 35 67 37 140 280 32 64 128 256), losses := [] }

theorem u8620 : Upper (D 8) (R 8) [34,65,33,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8621 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 140 304 248 216 216 472), lower := (rows 35 67 37 140 304 32 64 128 256), losses := [] }

theorem u8621 : Upper (D 8) (R 8) [34,65,33,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8622 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 140 336 184 248 184 440), lower := (rows 35 67 37 140 336 32 64 128 256), losses := [] }

theorem u8622 : Upper (D 8) (R 8) [34,65,33,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8623 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 140 400 120 120 248 376), lower := (rows 35 67 37 140 400 32 64 128 256), losses := [] }

theorem u8623 : Upper (D 8) (R 8) [34,65,33,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8624 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 152 276 232 232 232 488), lower := (rows 35 67 37 152 276 32 64 128 256), losses := [] }

theorem u8624 : Upper (D 8) (R 8) [34,65,33,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8625 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 152 280 228 228 228 484), lower := (rows 35 67 37 152 280 32 64 128 256), losses := [] }

theorem u8625 : Upper (D 8) (R 8) [34,65,33,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8626 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 152 304 236 204 204 460), lower := (rows 35 67 37 152 304 32 64 128 256), losses := [] }

theorem u8626 : Upper (D 8) (R 8) [34,65,33,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8627 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 152 336 172 236 172 428), lower := (rows 35 67 37 152 336 32 64 128 256), losses := [] }

theorem u8627 : Upper (D 8) (R 8) [34,65,33,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8628 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 168 208 316 348 412 284), lower := (rows 35 67 37 168 208 32 64 128 256), losses := [] }

theorem u8628 : Upper (D 8) (R 8) [34,65,33,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8629 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 168 276 248 216 216 472), lower := (rows 35 67 37 168 276 32 64 128 256), losses := [] }

theorem u8629 : Upper (D 8) (R 8) [34,65,33,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8630 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 168 280 244 212 212 468), lower := (rows 35 67 37 168 280 32 64 128 256), losses := [] }

theorem u8630 : Upper (D 8) (R 8) [34,65,33,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8631 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 168 336 188 220 156 412), lower := (rows 35 67 37 168 336 32 64 128 256), losses := [] }

theorem u8631 : Upper (D 8) (R 8) [34,65,33,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8632 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 168 400 124 92 220 348), lower := (rows 35 67 37 168 400 32 64 128 256), losses := [] }

theorem u8632 : Upper (D 8) (R 8) [34,65,33,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8633 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 200 276 184 248 184 440), lower := (rows 35 67 37 200 276 32 64 128 256), losses := [] }

theorem u8633 : Upper (D 8) (R 8) [34,65,33,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8634 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 200 280 180 244 180 436), lower := (rows 35 67 37 200 280 32 64 128 256), losses := [] }

theorem u8634 : Upper (D 8) (R 8) [34,65,33,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8635 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 200 304 188 220 156 412), lower := (rows 35 67 37 200 304 32 64 128 256), losses := [] }

theorem u8635 : Upper (D 8) (R 8) [34,65,33,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8636 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 200 400 60 124 188 316), lower := (rows 35 67 37 200 400 32 64 128 256), losses := [] }

theorem u8636 : Upper (D 8) (R 8) [34,65,33,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8637 : PairBound 9 := { available := 401, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 44 208 433 465 401 401), lower := (rows 35 67 44 44 208 32 64 128 256), losses := [] }

theorem u8637 : Upper (D 8) (R 8) [34,65,40,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8638 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 44 336 177 209 145 401), lower := (rows 35 67 44 44 336 32 64 128 256), losses := [] }

theorem u8638 : Upper (D 8) (R 8) [34,65,40,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8639 : PairBound 9 := { available := 209, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 44 400 241 209 209 465), lower := (rows 35 67 44 44 400 32 64 128 256), losses := [] }

theorem u8639 : Upper (D 8) (R 8) [34,65,40,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u8639
end Delivery.IrregularNine14.P08
