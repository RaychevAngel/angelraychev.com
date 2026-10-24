import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0358
import IrregularNine14P06C0359

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36840 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 74 196 25 273 38 102 166 294), lower := (rows 35 74 196 25 273 32 64 128 256), losses := [] }

theorem u36840 : Upper (D 6) (R 6) [34,72,192,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36841 : Route 9 := (fun mask => (mask,id))

def c36841 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36841 : Upper (D 6) (R 6) [34,72,192,17,258] 13 := by
  apply FastRouting.sound _ _ [34,72,192,17,258] 13 (by decide) (choices 1) [1,4] r36841 c36841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21489
  · exact u21490

def r36842 : Route 9 := (fun mask => (mask,id))

def c36842 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36842 : Upper (D 6) (R 6) [34,72,192,17,260] 13 := by
  apply FastRouting.sound _ _ [34,72,192,17,260] 13 (by decide) (choices 1) [1,2,4] r36842 c36842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21491
  · exact u21492
  · exact u21493

def r36843 : Route 9 := (fun mask => (mask,id))

def c36843 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36843 : Upper (D 6) (R 6) [34,72,192,17,288] 13 := by
  apply FastRouting.sound _ _ [34,72,192,17,288] 13 (by decide) (choices 1) [1,2,4] r36843 c36843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21494
  · exact u21495
  · exact u21496

def b36844 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 74 196 26 21 293 357 421 293), lower := (rows 35 74 196 26 21 32 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 16 48 0 144 272), good := (rows 35 11 132 443 437 32 0 128 256) }] }

theorem u36844 : Upper (D 6) (R 6) [34,72,192,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36845 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 196 26 49 293 325 389 261), lower := (rows 35 74 196 26 49 32 64 128 256), losses := [] }

theorem u36845 : Upper (D 6) (R 6) [34,72,192,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36846 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 35 74 196 26 52 293 325 389 261), lower := (rows 35 74 196 26 52 32 64 128 256), losses := [] }

theorem u36846 : Upper (D 6) (R 6) [34,72,192,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36847 : Route 9 := (fun mask => (mask,id))

def c36847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36847 : Upper (D 6) (R 6) [34,72,192,18,257] 13 := by
  apply FastRouting.sound _ _ [34,72,192,18,257] 13 (by decide) (choices 1) [1,4] r36847 c36847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21497
  · exact u21498

def r36848 : Route 9 := (fun mask => (mask,id))

def c36848 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36848 : Upper (D 6) (R 6) [34,72,192,18,260] 13 := by
  apply FastRouting.sound _ _ [34,72,192,18,260] 13 (by decide) (choices 1) [1,4] r36848 c36848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21499
  · exact u21500

def b36849 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 35 74 196 26 304 37 69 133 261), lower := (rows 35 74 196 26 304 32 64 128 256), losses := [] }

theorem u36849 : Upper (D 6) (R 6) [34,72,192,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36850 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 196 28 19 293 357 421 293), lower := (rows 35 74 196 28 19 32 64 128 256), losses := [] }

theorem u36850 : Upper (D 6) (R 6) [34,72,192,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36851 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 196 28 21 291 355 419 291), lower := (rows 35 74 196 28 21 32 64 128 256), losses := [] }

theorem u36851 : Upper (D 6) (R 6) [34,72,192,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36852 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 26, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 196 28 22 289 353 417 289), lower := (rows 35 74 196 28 22 32 64 128 256), losses := [] }

theorem u36852 : Upper (D 6) (R 6) [34,72,192,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36853 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 196 28 49 295 327 391 263), lower := (rows 35 74 196 28 49 32 64 128 256), losses := [] }

theorem u36853 : Upper (D 6) (R 6) [34,72,192,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36854 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 196 28 50 293 325 389 261), lower := (rows 35 74 196 28 50 32 64 128 256), losses := [] }

theorem u36854 : Upper (D 6) (R 6) [34,72,192,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36855 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 196 28 52 291 323 387 259), lower := (rows 35 74 196 28 52 32 64 128 256), losses := [] }

theorem u36855 : Upper (D 6) (R 6) [34,72,192,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36856 : Route 9 := (fun mask => (mask,id))

def c36856 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36856 : Upper (D 6) (R 6) [34,72,192,20,257] 13 := by
  apply FastRouting.sound _ _ [34,72,192,20,257] 13 (by decide) (choices 1) [1,2,4] r36856 c36856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21501
  · exact u21502
  · exact u21503

def r36857 : Route 9 := (fun mask => (mask,id))

def c36857 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36857 : Upper (D 6) (R 6) [34,72,192,20,258] 13 := by
  apply FastRouting.sound _ _ [34,72,192,20,258] 13 (by decide) (choices 1) [1,4] r36857 c36857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21504
  · exact u21505

def b36858 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 196 28 276 35 99 163 291), lower := (rows 35 74 196 28 276 32 64 128 256), losses := [] }

theorem u36858 : Upper (D 6) (R 6) [34,72,192,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36859 : Route 9 := (fun mask => (mask,id))

def c36859 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36859 : Upper (D 6) (R 6) [34,72,192,20,288] 13 := by
  apply FastRouting.sound _ _ [34,72,192,20,288] 13 (by decide) (choices 1) [1,2,4] r36859 c36859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21506
  · exact u21507
  · exact u21508

def b36860 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 74 196 44 19 309 341 405 277), lower := (rows 35 74 196 44 19 32 64 128 256), losses := [] }

theorem u36860 : Upper (D 6) (R 6) [34,72,192,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36861 : Route 9 := (fun mask => (mask,id))

def c36861 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36861 : Upper (D 6) (R 6) [34,72,192,36,5] 13 := by
  apply FastRouting.sound _ _ [34,72,192,36,5] 13 (by decide) (choices 1) [1,2,16,256] r36861 c36861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21509
  · exact u21510
  · exact u21511
  · exact u21512

def b36862 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 196 44 22 305 337 401 273), lower := (rows 35 74 196 44 22 32 64 128 256), losses := [] }

theorem u36862 : Upper (D 6) (R 6) [34,72,192,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36863 : Route 9 := (fun mask => (mask,id))

def c36863 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36863 : Upper (D 6) (R 6) [34,72,192,36,257] 13 := by
  apply FastRouting.sound _ _ [34,72,192,36,257] 13 (by decide) (choices 1) [1,2,4,16] r36863 c36863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21513
  · exact u21514
  · exact u21515
  · exact u21516

def r36864 : Route 9 := (fun mask => (mask,id))

def c36864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36864 : Upper (D 6) (R 6) [34,72,192,36,258] 13 := by
  apply FastRouting.sound _ _ [34,72,192,36,258] 13 (by decide) (choices 1) [1,4,16] r36864 c36864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21517
  · exact u21518
  · exact u21519

def r36865 : Route 9 := (fun mask => (mask,id))

def c36865 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36865 : Upper (D 6) (R 6) [34,72,192,36,260] 13 := by
  apply FastRouting.sound _ _ [34,72,192,36,260] 13 (by decide) (choices 1) [1,2,16] r36865 c36865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21520
  · exact u21521
  · exact u21522

def b36866 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 196 56 19 293 325 389 261), lower := (rows 35 74 196 56 19 32 64 128 256), losses := [] }

theorem u36866 : Upper (D 6) (R 6) [34,72,192,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36867 : Route 9 := (fun mask => (mask,id))

def c36867 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36867 : Upper (D 6) (R 6) [34,72,192,48,5] 13 := by
  apply FastRouting.sound _ _ [34,72,192,48,5] 13 (by decide) (choices 1) [1,2,4,256] r36867 c36867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21523
  · exact u21524
  · exact u21525
  · exact u21526

def b36868 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 196 56 22 293 325 389 261), lower := (rows 35 74 196 56 22 32 64 128 256), losses := [] }

theorem u36868 : Upper (D 6) (R 6) [34,72,192,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36869 : Route 9 := (fun mask => (mask,id))

def c36869 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36869 : Upper (D 6) (R 6) [34,72,192,48,257] 13 := by
  apply FastRouting.sound _ _ [34,72,192,48,257] 13 (by decide) (choices 1) [1,2,4] r36869 c36869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21527
  · exact u21528
  · exact u21529

def b36870 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 35 74 196 56 274 37 69 133 261), lower := (rows 35 74 196 56 274 32 64 128 256), losses := [] }

theorem u36870 : Upper (D 6) (R 6) [34,72,192,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36871 : Route 9 := (fun mask => (mask,id))

def c36871 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36871 : Upper (D 6) (R 6) [34,72,192,48,260] 13 := by
  apply FastRouting.sound _ _ [34,72,192,48,260] 13 (by decide) (choices 1) [1,2,4] r36871 c36871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21530
  · exact u21531
  · exact u21532

def b36872 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 196 265 19 52 116 180 308), lower := (rows 35 74 196 265 19 32 64 128 256), losses := [] }

theorem u36872 : Upper (D 6) (R 6) [34,72,192,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36873 : Route 9 := (fun mask => (mask,id))

def c36873 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36873 : Upper (D 6) (R 6) [34,72,192,257,5] 13 := by
  apply FastRouting.sound _ _ [34,72,192,257,5] 13 (by decide) (choices 1) [2,4,16] r36873 c36873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21533
  · exact u21534
  · exact u21535

def r36874 : Route 9 := (fun mask => (mask,id))

def c36874 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36874 : Upper (D 6) (R 6) [34,72,192,257,6] 13 := by
  apply FastRouting.sound _ _ [34,72,192,257,6] 13 (by decide) (choices 1) [1,4,16] r36874 c36874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21536
  · exact u21537
  · exact u21538

def b36875 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 196 265 49 54 86 150 278), lower := (rows 35 74 196 265 49 32 64 128 256), losses := [] }

theorem u36875 : Upper (D 6) (R 6) [34,72,192,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36876 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 196 265 50 53 85 149 277), lower := (rows 35 74 196 265 50 32 64 128 256), losses := [] }

theorem u36876 : Upper (D 6) (R 6) [34,72,192,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36877 : Route 9 := (fun mask => (mask,id))

def c36877 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36877 : Upper (D 6) (R 6) [34,72,192,257,36] 13 := by
  apply FastRouting.sound _ _ [34,72,192,257,36] 13 (by decide) (choices 1) [1,2,4,16] r36877 c36877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21539
  · exact u21540
  · exact u21541
  · exact u21542

def r36878 : Route 9 := (fun mask => (mask,id))

def c36878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36878 : Upper (D 6) (R 6) [34,72,192,258,5] 13 := by
  apply FastRouting.sound _ _ [34,72,192,258,5] 13 (by decide) (choices 1) [1,4,16] r36878 c36878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21543
  · exact u21544
  · exact u21545

def b36879 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 74 196 266 49 53 85 149 277), lower := (rows 35 74 196 266 49 32 64 128 256), losses := [] }

theorem u36879 : Upper (D 6) (R 6) [34,72,192,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36880 : Route 9 := (fun mask => (mask,id))

def c36880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36880 : Upper (D 6) (R 6) [34,72,192,258,36] 13 := by
  apply FastRouting.sound _ _ [34,72,192,258,36] 13 (by decide) (choices 1) [1,4,16] r36880 c36880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21546
  · exact u21547
  · exact u21548

def b36881 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 196 268 19 53 117 181 309), lower := (rows 35 74 196 268 19 32 64 128 256), losses := [] }

theorem u36881 : Upper (D 6) (R 6) [34,72,192,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36882 : Route 9 := (fun mask => (mask,id))

def c36882 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36882 : Upper (D 6) (R 6) [34,72,192,260,5] 13 := by
  apply FastRouting.sound _ _ [34,72,192,260,5] 13 (by decide) (choices 1) [1,2,16] r36882 c36882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21549
  · exact u21550
  · exact u21551

def b36883 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 297, targets := 64 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 74 196 268 22 49 113 177 305), lower := (rows 35 74 196 268 22 32 64 128 256), losses := [] }

theorem u36883 : Upper (D 6) (R 6) [34,72,192,260,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36884 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 196 268 49 55 87 151 279), lower := (rows 35 74 196 268 49 32 64 128 256), losses := [] }

theorem u36884 : Upper (D 6) (R 6) [34,72,192,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36885 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 196 268 50 53 85 149 277), lower := (rows 35 74 196 268 50 32 64 128 256), losses := [] }

theorem u36885 : Upper (D 6) (R 6) [34,72,192,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36886 : Route 9 := (fun mask => (mask,id))

def c36886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36886 : Upper (D 6) (R 6) [34,72,192,260,36] 13 := by
  apply FastRouting.sound _ _ [34,72,192,260,36] 13 (by decide) (choices 1) [1,2,16] r36886 c36886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21552
  · exact u21553
  · exact u21554

def b36887 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 196 280 19 37 101 165 293), lower := (rows 35 74 196 280 19 32 64 128 256), losses := [] }

theorem u36887 : Upper (D 6) (R 6) [34,72,192,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36888 : Route 9 := (fun mask => (mask,id))

def c36888 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36888 : Upper (D 6) (R 6) [34,72,192,272,5] 13 := by
  apply FastRouting.sound _ _ [34,72,192,272,5] 13 (by decide) (choices 1) [1,2,4] r36888 c36888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21555
  · exact u21556
  · exact u21557

def b36889 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 297, targets := 64 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,6),(2,1),(3,6)], upper := (rows 35 74 196 280 22 37 101 165 293), lower := (rows 35 74 196 280 22 32 64 128 256), losses := [] }

theorem u36889 : Upper (D 6) (R 6) [34,72,192,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36890 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 196 280 49 39 71 135 263), lower := (rows 35 74 196 280 49 32 64 128 256), losses := [] }

theorem u36890 : Upper (D 6) (R 6) [34,72,192,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36891 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 196 280 50 37 69 133 261), lower := (rows 35 74 196 280 50 32 64 128 256), losses := [] }

theorem u36891 : Upper (D 6) (R 6) [34,72,192,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36892 : Route 9 := (fun mask => (mask,id))

def c36892 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36892 : Upper (D 6) (R 6) [34,72,192,272,36] 13 := by
  apply FastRouting.sound _ _ [34,72,192,272,36] 13 (by decide) (choices 1) [1,2,4] r36892 c36892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21558
  · exact u21559
  · exact u21560

def b36893 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 74 196 296 19 53 85 149 277), lower := (rows 35 74 196 296 19 32 64 128 256), losses := [] }

theorem u36893 : Upper (D 6) (R 6) [34,72,192,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36894 : Route 9 := (fun mask => (mask,id))

def c36894 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36894 : Upper (D 6) (R 6) [34,72,192,288,5] 13 := by
  apply FastRouting.sound _ _ [34,72,192,288,5] 13 (by decide) (choices 1) [1,2,4,16] r36894 c36894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21561
  · exact u21562
  · exact u21563
  · exact u21564

def b36895 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 196 296 22 53 85 149 277), lower := (rows 35 74 196 296 22 32 64 128 256), losses := [] }

theorem u36895 : Upper (D 6) (R 6) [34,72,192,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36896 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 388 13 19 116 116 244 372), lower := (rows 35 74 388 13 19 32 64 128 256), losses := [] }

theorem u36896 : Upper (D 6) (R 6) [34,72,384,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36897 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 74 388 13 21 114 114 242 370), lower := (rows 35 74 388 13 21 32 64 128 256), losses := [] }

theorem u36897 : Upper (D 6) (R 6) [34,72,384,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36898 : Route 9 := (fun mask => (mask,id))

def c36898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36898 : Upper (D 6) (R 6) [34,72,384,5,6] 13 := by
  apply FastRouting.sound _ _ [34,72,384,5,6] 13 (by decide) (choices 1) [1,16,64] r36898 c36898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21565
  · exact u21566
  · exact u21567

def b36899 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 388 13 49 118 86 214 342), lower := (rows 35 74 388 13 49 32 64 128 256), losses := [] }

theorem u36899 : Upper (D 6) (R 6) [34,72,384,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u36899
end Delivery.IrregularNine14.P06
