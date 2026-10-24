import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0022
import IrregularNine14P08C0023

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7800 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 164 25 400 97 97 225 353), lower := (rows 7 74 164 25 400 32 64 128 256), losses := [] }

theorem u7800 : Upper (D 8) (R 8) [6,72,160,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7801 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 74 164 41 49 496 464 464 464), lower := (rows 7 74 164 41 49 32 64 128 256), losses := [] }

theorem u7801 : Upper (D 8) (R 8) [6,72,160,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7802 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 41 81 432 496 432 432), lower := (rows 7 74 164 41 81 32 64 128 256), losses := [] }

theorem u7802 : Upper (D 8) (R 8) [6,72,160,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7803 : Route 9 := (fun mask => (mask,id))

def c7803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7803 : Upper (D 8) (R 8) [6,72,160,33,96] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,96] 13 (by decide) (choices 1) [1,16,128,256] r7803 c7803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1372
  · exact u1373
  · exact u1374
  · exact u1375

def b7804 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 164 41 145 368 368 496 368), lower := (rows 7 74 164 41 145 32 64 128 256), losses := [] }

theorem u7804 : Upper (D 8) (R 8) [6,72,160,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7805 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 164 41 176 369 337 465 337), lower := (rows 7 74 164 41 176 32 64 128 256), losses := [] }

theorem u7805 : Upper (D 8) (R 8) [6,72,160,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7806 : Route 9 := (fun mask => (mask,id))

def c7806 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7806 : Upper (D 8) (R 8) [6,72,160,33,192] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,192] 13 (by decide) (choices 1) [1,16,256] r7806 c7806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1376
  · exact u1377
  · exact u1378

def b7807 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 41 273 240 240 240 496), lower := (rows 7 74 164 41 273 32 64 128 256), losses := [] }

theorem u7807 : Upper (D 8) (R 8) [6,72,160,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7808 : Route 9 := (fun mask => (mask,id))

def c7808 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7808 : Upper (D 8) (R 8) [6,72,160,33,288] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,288] 13 (by decide) (choices 1) [1,16,64,128] r7808 c7808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1379
  · exact u1380
  · exact u1381
  · exact u1382

def r7809 : Route 9 := (fun mask => (mask,id))

def c7809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7809 : Upper (D 8) (R 8) [6,72,160,33,320] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,320] 13 (by decide) (choices 1) [1,16,128] r7809 c7809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1383
  · exact u1384
  · exact u1385

def r7810 : Route 9 := (fun mask => (mask,id))

def c7810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7810 : Upper (D 8) (R 8) [6,72,160,33,384] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,384] 13 (by decide) (choices 1) [1,16,64] r7810 c7810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1386
  · exact u1387
  · exact u1388

def b7811 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 74 164 56 49 481 449 449 449), lower := (rows 7 74 164 56 49 32 64 128 256), losses := [] }

theorem u7811 : Upper (D 8) (R 8) [6,72,160,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7812 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 56 81 417 481 417 417), lower := (rows 7 74 164 56 81 32 64 128 256), losses := [] }

theorem u7812 : Upper (D 8) (R 8) [6,72,160,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7813 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 56 112 417 449 385 385), lower := (rows 7 74 164 56 112 32 64 128 256), losses := [] }

theorem u7813 : Upper (D 8) (R 8) [6,72,160,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7813 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7814 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 164 56 145 353 353 481 353), lower := (rows 7 74 164 56 145 32 64 128 256), losses := [] }

theorem u7814 : Upper (D 8) (R 8) [6,72,160,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7815 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 74 164 56 176 353 321 449 321), lower := (rows 7 74 164 56 176 32 64 128 256), losses := [] }

theorem u7815 : Upper (D 8) (R 8) [6,72,160,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7816 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 56 208 289 353 417 289), lower := (rows 7 74 164 56 208 32 64 128 256), losses := [] }

theorem u7816 : Upper (D 8) (R 8) [6,72,160,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7817 : Route 9 := (fun mask => (mask,id))

def c7817 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7817 : Upper (D 8) (R 8) [6,72,160,48,257] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,257] 13 (by decide) (choices 1) [1,64,128] r7817 c7817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1389
  · exact u1390
  · exact u1391

def b7818 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 74 164 56 304 225 193 193 449), lower := (rows 7 74 164 56 304 32 64 128 256), losses := [] }

theorem u7818 : Upper (D 8) (R 8) [6,72,160,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7818 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7819 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 56 336 161 225 161 417), lower := (rows 7 74 164 56 336 32 64 128 256), losses := [] }

theorem u7819 : Upper (D 8) (R 8) [6,72,160,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7820 : Route 9 := (fun mask => (mask,id))

def c7820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7820 : Upper (D 8) (R 8) [6,72,160,48,384] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,384] 13 (by decide) (choices 1) [1,64] r7820 c7820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1392
  · exact u1393

def b7821 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 265 49 240 240 240 496), lower := (rows 7 74 164 265 49 32 64 128 256), losses := [] }

theorem u7821 : Upper (D 8) (R 8) [6,72,160,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7822 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 265 81 176 240 176 432), lower := (rows 7 74 164 265 81 32 64 128 256), losses := [] }

theorem u7822 : Upper (D 8) (R 8) [6,72,160,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7823 : Route 9 := (fun mask => (mask,id))

def c7823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7823 : Upper (D 8) (R 8) [6,72,160,257,96] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,96] 13 (by decide) (choices 1) [1,16,128] r7823 c7823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1394
  · exact u1395
  · exact u1396

def b7824 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 164 265 145 112 112 240 368), lower := (rows 7 74 164 265 145 32 64 128 256), losses := [] }

theorem u7824 : Upper (D 8) (R 8) [6,72,160,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7825 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 164 265 176 113 113 241 369), lower := (rows 7 74 164 265 176 32 64 128 256), losses := [] }

theorem u7825 : Upper (D 8) (R 8) [6,72,160,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7826 : Route 9 := (fun mask => (mask,id))

def c7826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7826 : Upper (D 8) (R 8) [6,72,160,257,192] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,192] 13 (by decide) (choices 1) [1,16] r7826 c7826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1397
  · exact u1398

def r7827 : Route 9 := (fun mask => (mask,id))

def c7827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7827 : Upper (D 8) (R 8) [6,72,160,272,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,272,33] 13 (by decide) (choices 1) [1,64,128] r7827 c7827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1399
  · exact u1400
  · exact u1401

def b7828 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 280 81 161 225 161 417), lower := (rows 7 74 164 280 81 32 64 128 256), losses := [] }

theorem u7828 : Upper (D 8) (R 8) [6,72,160,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7829 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 280 112 161 225 161 417), lower := (rows 7 74 164 280 112 32 64 128 256), losses := [] }

theorem u7829 : Upper (D 8) (R 8) [6,72,160,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7830 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 164 280 145 97 97 225 353), lower := (rows 7 74 164 280 145 32 64 128 256), losses := [] }

theorem u7830 : Upper (D 8) (R 8) [6,72,160,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7831 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 164 280 176 97 97 225 353), lower := (rows 7 74 164 280 176 32 64 128 256), losses := [] }

theorem u7831 : Upper (D 8) (R 8) [6,72,160,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7832 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 280 208 33 97 161 289), lower := (rows 7 74 164 280 208 32 64 128 256), losses := [] }

theorem u7832 : Upper (D 8) (R 8) [6,72,160,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7833 : Route 9 := (fun mask => (mask,id))

def c7833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7833 : Upper (D 8) (R 8) [6,72,160,288,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,33] 13 (by decide) (choices 1) [1,16,64,128] r7833 c7833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1402
  · exact u1403
  · exact u1404
  · exact u1405

def b7834 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 296 81 177 241 177 433), lower := (rows 7 74 164 296 81 32 64 128 256), losses := [] }

theorem u7834 : Upper (D 8) (R 8) [6,72,160,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7835 : Route 9 := (fun mask => (mask,id))

def c7835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7835 : Upper (D 8) (R 8) [6,72,160,288,96] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,96] 13 (by decide) (choices 1) [1,16,128] r7835 c7835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1406
  · exact u1407
  · exact u1408

def b7836 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 164 296 145 113 113 241 369), lower := (rows 7 74 164 296 145 32 64 128 256), losses := [] }

theorem u7836 : Upper (D 8) (R 8) [6,72,160,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7837 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 164 296 176 113 81 209 337), lower := (rows 7 74 164 296 176 32 64 128 256), losses := [] }

theorem u7837 : Upper (D 8) (R 8) [6,72,160,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7838 : Route 9 := (fun mask => (mask,id))

def c7838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7838 : Upper (D 8) (R 8) [6,72,160,288,192] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,192] 13 (by decide) (choices 1) [1,16] r7838 c7838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1409
  · exact u1410

def b7839 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 56 49 224 224 224 480), lower := (rows 7 74 261 56 49 32 64 128 256), losses := [] }

theorem u7839 : Upper (D 8) (R 8) [6,72,257,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7840 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 261 56 81 160 224 160 416), lower := (rows 7 74 261 56 81 32 64 128 256), losses := [] }

theorem u7840 : Upper (D 8) (R 8) [6,72,257,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7841 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 56 112 161 225 161 417), lower := (rows 7 74 261 56 112 32 64 128 256), losses := [] }

theorem u7841 : Upper (D 8) (R 8) [6,72,257,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7842 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 56 145 224 224 224 480), lower := (rows 7 74 261 56 145 32 64 128 256), losses := [] }

theorem u7842 : Upper (D 8) (R 8) [6,72,257,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7843 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 74 261 56 176 225 225 225 481), lower := (rows 7 74 261 56 176 32 64 128 256), losses := [] }

theorem u7843 : Upper (D 8) (R 8) [6,72,257,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7844 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 261 56 208 161 225 161 417), lower := (rows 7 74 261 56 208 32 64 128 256), losses := [] }

theorem u7844 : Upper (D 8) (R 8) [6,72,257,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7845 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 152 49 224 224 224 480), lower := (rows 7 74 261 152 49 32 64 128 256), losses := [] }

theorem u7845 : Upper (D 8) (R 8) [6,72,257,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7846 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 261 152 81 160 224 160 416), lower := (rows 7 74 261 152 81 32 64 128 256), losses := [] }

theorem u7846 : Upper (D 8) (R 8) [6,72,257,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7847 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 261 152 112 161 225 161 417), lower := (rows 7 74 261 152 112 32 64 128 256), losses := [] }

theorem u7847 : Upper (D 8) (R 8) [6,72,257,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7848 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 261 152 145 96 96 224 352), lower := (rows 7 74 261 152 145 32 64 128 256), losses := [] }

theorem u7848 : Upper (D 8) (R 8) [6,72,257,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7849 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 261 152 176 97 97 225 353), lower := (rows 7 74 261 152 176 32 64 128 256), losses := [] }

theorem u7849 : Upper (D 8) (R 8) [6,72,257,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7850 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 152 208 33 97 161 289), lower := (rows 7 74 261 152 208 32 64 128 256), losses := [] }

theorem u7850 : Upper (D 8) (R 8) [6,72,257,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7851 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 168 49 240 240 240 496), lower := (rows 7 74 261 168 49 32 64 128 256), losses := [] }

theorem u7851 : Upper (D 8) (R 8) [6,72,257,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7852 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 170, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 168 81 176 240 176 432), lower := (rows 7 74 261 168 81 32 64 128 256), losses := [] }

theorem u7852 : Upper (D 8) (R 8) [6,72,257,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7853 : Route 9 := (fun mask => (mask,id))

def c7853 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7853 : Upper (D 8) (R 8) [6,72,257,160,96] 13 := by
  apply FastRouting.sound _ _ [6,72,257,160,96] 13 (by decide) (choices 1) [1,16,128] r7853 c7853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1411
  · exact u1412
  · exact u1413

def b7854 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 168 145 112 112 240 368), lower := (rows 7 74 261 168 145 32 64 128 256), losses := [] }

theorem u7854 : Upper (D 8) (R 8) [6,72,257,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7855 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 261 168 176 113 113 241 369), lower := (rows 7 74 261 168 176 32 64 128 256), losses := [] }

theorem u7855 : Upper (D 8) (R 8) [6,72,257,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7856 : Route 9 := (fun mask => (mask,id))

def c7856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7856 : Upper (D 8) (R 8) [6,72,257,160,192] 13 := by
  apply FastRouting.sound _ _ [6,72,257,160,192] 13 (by decide) (choices 1) [1,16] r7856 c7856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1414
  · exact u1415

def b7857 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 74 276 41 49 224 224 224 480), lower := (rows 7 74 276 41 49 32 64 128 256), losses := [] }

theorem u7857 : Upper (D 8) (R 8) [6,72,272,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7858 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 276 41 81 160 224 160 416), lower := (rows 7 74 276 41 81 32 64 128 256), losses := [] }

theorem u7858 : Upper (D 8) (R 8) [6,72,272,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7858 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7859 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 276 41 112 161 225 161 417), lower := (rows 7 74 276 41 112 32 64 128 256), losses := [] }

theorem u7859 : Upper (D 8) (R 8) [6,72,272,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u7859
end Delivery.IrregularNine14.P08
