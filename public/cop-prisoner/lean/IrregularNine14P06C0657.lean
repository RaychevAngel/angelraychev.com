import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0429
import IrregularNine14P06C0430

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39420 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 388 11 50 101 69 197 325), lower := (rows 41 82 388 11 50 32 64 128 256), losses := [] }

theorem u39420 : Upper (D 6) (R 6) [40,80,384,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39421 : Route 9 := (fun mask => (mask,id))

def c39421 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39421 : Upper (D 6) (R 6) [40,80,384,3,36] 13 := by
  apply FastRouting.sound _ _ [40,80,384,3,36] 13 (by decide) (choices 1) [1,2,4,64] r39421 c39421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25779
  · exact u25780
  · exact u25781
  · exact u25782

def b39422 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 10, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 41 82 388 11 81 38 102 166 294), lower := (rows 41 82 388 11 81 32 64 128 256), losses := [] }

theorem u39422 : Upper (D 6) (R 6) [40,80,384,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39423 : PairBound 9 := { available := 37, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 388 11 82 37 101 165 293), lower := (rows 41 82 388 11 82 32 64 128 256), losses := [] }

theorem u39423 : Upper (D 6) (R 6) [40,80,384,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39424 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 388 11 84 39 103 167 295), lower := (rows 41 82 388 11 84 32 64 128 256), losses := [] }

theorem u39424 : Upper (D 6) (R 6) [40,80,384,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39425 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 388 11 112 39 71 135 263), lower := (rows 41 82 388 11 112 32 64 128 256), losses := [] }

theorem u39425 : Upper (D 6) (R 6) [40,80,384,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39426 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 82 388 13 21 98 98 226 354), lower := (rows 41 82 388 13 21 32 64 128 256), losses := [] }

theorem u39426 : Upper (D 6) (R 6) [40,80,384,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39427 : Route 9 := (fun mask => (mask,id))

def c39427 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39427 : Upper (D 6) (R 6) [40,80,384,5,6] 13 := by
  apply FastRouting.sound _ _ [40,80,384,5,6] 13 (by decide) (choices 1) [1,2,64] r39427 c39427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25783
  · exact u25784
  · exact u25785

def b39428 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 82 388 13 49 102 70 198 326), lower := (rows 41 82 388 13 49 32 64 128 256), losses := [] }

theorem u39428 : Upper (D 6) (R 6) [40,80,384,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39429 : Route 9 := (fun mask => (mask,id))

def c39429 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39429 : Upper (D 6) (R 6) [40,80,384,5,34] 13 := by
  apply FastRouting.sound _ _ [40,80,384,5,34] 13 (by decide) (choices 1) [1,2,4,64] r39429 c39429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25786
  · exact u25787
  · exact u25788
  · exact u25789

def b39430 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 388 13 52 99 67 195 323), lower := (rows 41 82 388 13 52 32 64 128 256), losses := [] }

theorem u39430 : Upper (D 6) (R 6) [40,80,384,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39431 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 388 13 81 38 102 166 294), lower := (rows 41 82 388 13 81 32 64 128 256), losses := [] }

theorem u39431 : Upper (D 6) (R 6) [40,80,384,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39432 : PairBound 9 := { available := 39, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 388 13 82 39 103 167 295), lower := (rows 41 82 388 13 82 32 64 128 256), losses := [] }

theorem u39432 : Upper (D 6) (R 6) [40,80,384,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39433 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 388 13 84 35 99 163 291), lower := (rows 41 82 388 13 84 32 64 128 256), losses := [] }

theorem u39433 : Upper (D 6) (R 6) [40,80,384,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39434 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 388 13 112 39 71 135 263), lower := (rows 41 82 388 13 112 32 64 128 256), losses := [] }

theorem u39434 : Upper (D 6) (R 6) [40,80,384,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39435 : Route 9 := (fun mask => (mask,id))

def c39435 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39435 : Upper (D 6) (R 6) [40,80,384,6,5] 13 := by
  apply FastRouting.sound _ _ [40,80,384,6,5] 13 (by decide) (choices 1) [1,2,64] r39435 c39435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25790
  · exact u25791
  · exact u25792

def b39436 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 82 388 14 49 103 71 199 327), lower := (rows 41 82 388 14 49 32 64 128 256), losses := [] }

theorem u39436 : Upper (D 6) (R 6) [40,80,384,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39437 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 485, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 82 388 14 50 101 69 197 325), lower := (rows 41 82 388 14 50 32 64 128 256), losses := [] }

theorem u39437 : Upper (D 6) (R 6) [40,80,384,6,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39438 : Route 9 := (fun mask => (mask,id))

def c39438 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39438 : Upper (D 6) (R 6) [40,80,384,6,36] 13 := by
  apply FastRouting.sound _ _ [40,80,384,6,36] 13 (by decide) (choices 1) [1,2,64] r39438 c39438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25793
  · exact u25794
  · exact u25795

def b39439 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 388 14 81 39 103 167 295), lower := (rows 41 82 388 14 81 32 64 128 256), losses := [] }

theorem u39439 : Upper (D 6) (R 6) [40,80,384,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39440 : PairBound 9 := { available := 37, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 388 14 82 37 101 165 293), lower := (rows 41 82 388 14 82 32 64 128 256), losses := [] }

theorem u39440 : Upper (D 6) (R 6) [40,80,384,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39441 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 41 82 388 14 84 35 99 163 291), lower := (rows 41 82 388 14 84 32 64 128 256), losses := [] }

theorem u39441 : Upper (D 6) (R 6) [40,80,384,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39442 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 388 14 112 39 71 135 263), lower := (rows 41 82 388 14 112 32 64 128 256), losses := [] }

theorem u39442 : Upper (D 6) (R 6) [40,80,384,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39443 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 82 388 73 49 38 70 134 262), lower := (rows 41 82 388 73 49 32 64 128 256), losses := [] }

theorem u39443 : Upper (D 6) (R 6) [40,80,384,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39444 : PairBound 9 := { available := 7, camps := [], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 82 388 73 50 39 71 135 263), lower := (rows 41 82 388 73 50 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 17 32 64 128 256), good := (rows 58 82 388 90 50 32 64 128 256) },{ target := 1, region := (rows 17 0 4 10 16 32 64 128 256), good := (rows 41 89 388 73 57 32 64 128 256) }] }

theorem u39444 : Upper (D 6) (R 6) [40,80,384,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39445 : Route 9 := (fun mask => (mask,id))

def c39445 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39445 : Upper (D 6) (R 6) [40,80,384,65,36] 13 := by
  apply FastRouting.sound _ _ [40,80,384,65,36] 13 (by decide) (choices 1) [1,2,4] r39445 c39445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25796
  · exact u25797
  · exact u25798

def b39446 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 82 388 74 52 39 71 135 263), lower := (rows 41 82 388 74 52 32 64 128 256), losses := [] }

theorem u39446 : Upper (D 6) (R 6) [40,80,384,66,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39447 : Route 9 := (fun mask => (mask,id))

def c39447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39447 : Upper (D 6) (R 6) [40,80,384,68,36] 13 := by
  apply FastRouting.sound _ _ [40,80,384,68,36] 13 (by decide) (choices 1) [1,2] r39447 c39447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25799
  · exact u25800

def b39448 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 452, targets := 2 }], pairs := [(2,1),(2,5),(3,5)], upper := (rows 41 98 133 14 19 372 340 468 340), lower := (rows 41 98 133 14 19 32 64 128 256), losses := [] }

theorem u39448 : Upper (D 6) (R 6) [40,96,129,6,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39449 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 98 133 14 21 370 338 466 338), lower := (rows 41 98 133 14 21 32 64 128 256), losses := [] }

theorem u39449 : Upper (D 6) (R 6) [40,96,129,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39450 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 98 133 14 22 369 337 465 337), lower := (rows 41 98 133 14 22 32 64 128 256), losses := [] }

theorem u39450 : Upper (D 6) (R 6) [40,96,129,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39451 : Route 9 := (fun mask => (mask,id))

def c39451 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39451 : Upper (D 6) (R 6) [40,96,129,6,65] 13 := by
  apply FastRouting.sound _ _ [40,96,129,6,65] 13 (by decide) (choices 1) [2,4,16,256] r39451 c39451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25801
  · exact u25802
  · exact u25803
  · exact u25804

def b39452 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 133 14 82 309 341 405 277), lower := (rows 41 98 133 14 82 32 64 128 256), losses := [] }

theorem u39452 : Upper (D 6) (R 6) [40,96,129,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39453 : Route 9 := (fun mask => (mask,id))

def c39453 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39453 : Upper (D 6) (R 6) [40,96,129,6,68] 13 := by
  apply FastRouting.sound _ _ [40,96,129,6,68] 13 (by decide) (choices 1) [1,2,16,256] r39453 c39453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25805
  · exact u25806
  · exact u25807
  · exact u25808

def r39454 : Route 9 := (fun mask => (mask,id))

def c39454 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39454 : Upper (D 6) (R 6) [40,96,129,6,257] 13 := by
  apply FastRouting.sound _ _ [40,96,129,6,257] 13 (by decide) (choices 1) [2,4,16,64] r39454 c39454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25809
  · exact u25810
  · exact u25811
  · exact u25812

def r39455 : Route 9 := (fun mask => (mask,id))

def c39455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39455 : Upper (D 6) (R 6) [40,96,129,6,258] 13 := by
  apply FastRouting.sound _ _ [40,96,129,6,258] 13 (by decide) (choices 1) [1,4,16,64] r39455 c39455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25813
  · exact u25814
  · exact u25815
  · exact u25816

def r39456 : Route 9 := (fun mask => (mask,id))

def c39456 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39456 : Upper (D 6) (R 6) [40,96,129,6,260] 13 := by
  apply FastRouting.sound _ _ [40,96,129,6,260] 13 (by decide) (choices 1) [1,2,16,64] r39456 c39456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25817
  · exact u25818
  · exact u25819
  · exact u25820

def r39457 : Route 9 := (fun mask => (mask,id))

def c39457 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39457 : Upper (D 6) (R 6) [40,96,129,6,320] 13 := by
  apply FastRouting.sound _ _ [40,96,129,6,320] 13 (by decide) (choices 1) [1,2,4,16] r39457 c39457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25821
  · exact u25822
  · exact u25823
  · exact u25824

def b39458 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 41 98 133 25 22 358 326 454 326), lower := (rows 41 98 133 25 22 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 80 144 272), good := (rows 13 66 133 477 470 0 64 128 256) }] }

theorem u39458 : Upper (D 6) (R 6) [40,96,129,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39459 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 133 25 82 294 326 390 262), lower := (rows 41 98 133 25 82 32 64 128 256), losses := [] }

theorem u39459 : Upper (D 6) (R 6) [40,96,129,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39460 : Route 9 := (fun mask => (mask,id))

def c39460 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39460 : Upper (D 6) (R 6) [40,96,129,17,68] 13 := by
  apply FastRouting.sound _ _ [40,96,129,17,68] 13 (by decide) (choices 1) [2,4,256] r39460 c39460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25825
  · exact u25826
  · exact u25827

def r39461 : Route 9 := (fun mask => (mask,id))

def c39461 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39461 : Upper (D 6) (R 6) [40,96,129,17,258] 13 := by
  apply FastRouting.sound _ _ [40,96,129,17,258] 13 (by decide) (choices 1) [2,4,64] r39461 c39461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25828
  · exact u25829
  · exact u25830

def r39462 : Route 9 := (fun mask => (mask,id))

def c39462 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39462 : Upper (D 6) (R 6) [40,96,129,17,260] 13 := by
  apply FastRouting.sound _ _ [40,96,129,17,260] 13 (by decide) (choices 1) [2,4,64] r39462 c39462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25831
  · exact u25832
  · exact u25833

def r39463 : Route 9 := (fun mask => (mask,id))

def c39463 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39463 : Upper (D 6) (R 6) [40,96,129,17,320] 13 := by
  apply FastRouting.sound _ _ [40,96,129,17,320] 13 (by decide) (choices 1) [2,4] r39463 c39463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25834
  · exact u25835

def b39464 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 133 26 19 356 324 452 324), lower := (rows 41 98 133 26 19 32 64 128 256), losses := [] }

theorem u39464 : Upper (D 6) (R 6) [40,96,129,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39465 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 98 133 26 21 358 326 454 326), lower := (rows 41 98 133 26 21 32 64 128 256), losses := [] }

theorem u39465 : Upper (D 6) (R 6) [40,96,129,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39466 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 98 133 26 22 357 325 453 325), lower := (rows 41 98 133 26 22 32 64 128 256), losses := [] }

theorem u39466 : Upper (D 6) (R 6) [40,96,129,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39467 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 133 26 81 294 326 390 262), lower := (rows 41 98 133 26 81 32 64 128 256), losses := [] }

theorem u39467 : Upper (D 6) (R 6) [40,96,129,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39468 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 41 98 133 26 82 293 325 389 261), lower := (rows 41 98 133 26 82 32 64 128 256), losses := [] }

theorem u39468 : Upper (D 6) (R 6) [40,96,129,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39469 : Route 9 := (fun mask => (mask,id))

def c39469 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39469 : Upper (D 6) (R 6) [40,96,129,18,68] 13 := by
  apply FastRouting.sound _ _ [40,96,129,18,68] 13 (by decide) (choices 1) [1,2,4,256] r39469 c39469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25836
  · exact u25837
  · exact u25838
  · exact u25839

def r39470 : Route 9 := (fun mask => (mask,id))

def c39470 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39470 : Upper (D 6) (R 6) [40,96,129,18,257] 13 := by
  apply FastRouting.sound _ _ [40,96,129,18,257] 13 (by decide) (choices 1) [2,4,64] r39470 c39470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25840
  · exact u25841
  · exact u25842

def b39471 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 98 133 26 274 101 69 197 325), lower := (rows 41 98 133 26 274 32 64 128 256), losses := [] }

theorem u39471 : Upper (D 6) (R 6) [40,96,129,18,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39472 : Route 9 := (fun mask => (mask,id))

def c39472 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39472 : Upper (D 6) (R 6) [40,96,129,18,260] 13 := by
  apply FastRouting.sound _ _ [40,96,129,18,260] 13 (by decide) (choices 1) [1,2,4,64] r39472 c39472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25843
  · exact u25844
  · exact u25845
  · exact u25846

def r39473 : Route 9 := (fun mask => (mask,id))

def c39473 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39473 : Upper (D 6) (R 6) [40,96,129,18,320] 13 := by
  apply FastRouting.sound _ _ [40,96,129,18,320] 13 (by decide) (choices 1) [1,2,4] r39473 c39473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25847
  · exact u25848
  · exact u25849

def b39474 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 2, region := 354, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 41 98 133 28 19 358 326 454 326), lower := (rows 41 98 133 28 19 32 64 128 256), losses := [] }

theorem u39474 : Upper (D 6) (R 6) [40,96,129,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39475 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 41 98 133 28 21 354 322 450 322), lower := (rows 41 98 133 28 21 32 64 128 256), losses := [] }

theorem u39475 : Upper (D 6) (R 6) [40,96,129,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39476 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 98 133 28 22 355 323 451 323), lower := (rows 41 98 133 28 22 32 64 128 256), losses := [] }

theorem u39476 : Upper (D 6) (R 6) [40,96,129,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39477 : Route 9 := (fun mask => (mask,id))

def c39477 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39477 : Upper (D 6) (R 6) [40,96,129,20,65] 13 := by
  apply FastRouting.sound _ _ [40,96,129,20,65] 13 (by decide) (choices 1) [2,4,256] r39477 c39477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25850
  · exact u25851
  · exact u25852

def b39478 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 133 28 82 295 327 391 263), lower := (rows 41 98 133 28 82 32 64 128 256), losses := [] }

theorem u39478 : Upper (D 6) (R 6) [40,96,129,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39479 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 98 133 28 84 291 323 387 259), lower := (rows 41 98 133 28 84 32 64 128 256), losses := [] }

theorem u39479 : Upper (D 6) (R 6) [40,96,129,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u39479
end Delivery.IrregularNine14.P06
