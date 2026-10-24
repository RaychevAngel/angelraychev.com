import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0390
import IrregularNine14P06C0391

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37860 : Route 9 := (fun mask => (mask,id))

def c37860 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37860 : Upper (D 6) (R 6) [34,132,264,17,66] 13 := by
  apply FastRouting.sound _ _ [34,132,264,17,66] 13 (by decide) (choices 1) [1,4,64] r37860 c37860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23412
  · exact u23413
  · exact u23414

def r37861 : Route 9 := (fun mask => (mask,id))

def c37861 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37861 : Upper (D 6) (R 6) [34,132,264,17,68] 13 := by
  apply FastRouting.sound _ _ [34,132,264,17,68] 13 (by decide) (choices 1) [1,2,64] r37861 c37861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23415
  · exact u23416
  · exact u23417

def r37862 : Route 9 := (fun mask => (mask,id))

def c37862 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37862 : Upper (D 6) (R 6) [34,132,264,17,96] 13 := by
  apply FastRouting.sound _ _ [34,132,264,17,96] 13 (by decide) (choices 1) [1,2,4,64] r37862 c37862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23418
  · exact u23419
  · exact u23420
  · exact u23421

def r37863 : Route 9 := (fun mask => (mask,id))

def c37863 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37863 : Upper (D 6) (R 6) [34,132,264,18,5] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,5] 13 (by decide) (choices 1) [1,64] r37863 c37863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23422
  · exact u23423

def b37864 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 268 26 49 101 69 197 325), lower := (rows 35 134 268 26 49 32 64 128 256), losses := [] }

theorem u37864 : Upper (D 6) (R 6) [34,132,264,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37865 : Route 9 := (fun mask => (mask,id))

def c37865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37865 : Upper (D 6) (R 6) [34,132,264,18,36] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,36] 13 (by decide) (choices 1) [1,64] r37865 c37865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23424
  · exact u23425

def r37866 : Route 9 := (fun mask => (mask,id))

def c37866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37866 : Upper (D 6) (R 6) [34,132,264,18,65] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,65] 13 (by decide) (choices 1) [1,4,64] r37866 c37866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23426
  · exact u23427
  · exact u23428

def r37867 : Route 9 := (fun mask => (mask,id))

def c37867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37867 : Upper (D 6) (R 6) [34,132,264,18,68] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,68] 13 (by decide) (choices 1) [1,64] r37867 c37867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23429
  · exact u23430

def r37868 : Route 9 := (fun mask => (mask,id))

def c37868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37868 : Upper (D 6) (R 6) [34,132,264,18,96] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,96] 13 (by decide) (choices 1) [1,4,64] r37868 c37868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23431
  · exact u23432
  · exact u23433

def b37869 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(4,5),(4,6)], upper := (rows 35 134 268 28 19 97 97 225 353), lower := (rows 35 134 268 28 19 32 64 128 256), losses := [] }

theorem u37869 : Upper (D 6) (R 6) [34,132,264,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37870 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 134 268 28 49 99 67 195 323), lower := (rows 35 134 268 28 49 32 64 128 256), losses := [] }

theorem u37870 : Upper (D 6) (R 6) [34,132,264,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37871 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 35 134 268 28 50 97 65 193 321), lower := (rows 35 134 268 28 50 32 64 128 256), losses := [] }

theorem u37871 : Upper (D 6) (R 6) [34,132,264,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37872 : Route 9 := (fun mask => (mask,id))

def c37872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37872 : Upper (D 6) (R 6) [34,132,264,20,65] 13 := by
  apply FastRouting.sound _ _ [34,132,264,20,65] 13 (by decide) (choices 1) [1,2,64] r37872 c37872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23434
  · exact u23435
  · exact u23436

def r37873 : Route 9 := (fun mask => (mask,id))

def c37873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37873 : Upper (D 6) (R 6) [34,132,264,20,66] 13 := by
  apply FastRouting.sound _ _ [34,132,264,20,66] 13 (by decide) (choices 1) [1,64] r37873 c37873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23437
  · exact u23438

def r37874 : Route 9 := (fun mask => (mask,id))

def c37874 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37874 : Upper (D 6) (R 6) [34,132,264,20,96] 13 := by
  apply FastRouting.sound _ _ [34,132,264,20,96] 13 (by decide) (choices 1) [1,2,64] r37874 c37874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23439
  · exact u23440
  · exact u23441

def b37875 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 268 56 19 101 69 197 325), lower := (rows 35 134 268 56 19 32 64 128 256), losses := [] }

theorem u37875 : Upper (D 6) (R 6) [34,132,264,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37876 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 4 },{ cop := 4, region := 194, targets := 32 }], pairs := [(0,2),(1,5),(3,2)], upper := (rows 35 134 268 56 21 99 67 195 323), lower := (rows 35 134 268 56 21 32 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 24 16 35 67 131 259), good := (rows 483 483 264 56 505 32 64 128 256) }] }

theorem u37876 : Upper (D 6) (R 6) [34,132,264,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37877 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 268 56 22 97 65 193 321), lower := (rows 35 134 268 56 22 32 64 128 256), losses := [] }

theorem u37877 : Upper (D 6) (R 6) [34,132,264,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37878 : Route 9 := (fun mask => (mask,id))

def c37878 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37878 : Upper (D 6) (R 6) [34,132,264,48,65] 13 := by
  apply FastRouting.sound _ _ [34,132,264,48,65] 13 (by decide) (choices 1) [1,2,4,64] r37878 c37878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23442
  · exact u23443
  · exact u23444
  · exact u23445

def r37879 : Route 9 := (fun mask => (mask,id))

def c37879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37879 : Upper (D 6) (R 6) [34,132,264,48,66] 13 := by
  apply FastRouting.sound _ _ [34,132,264,48,66] 13 (by decide) (choices 1) [1,4,64] r37879 c37879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23446
  · exact u23447
  · exact u23448

def r37880 : Route 9 := (fun mask => (mask,id))

def c37880 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37880 : Upper (D 6) (R 6) [34,132,264,48,68] 13 := by
  apply FastRouting.sound _ _ [34,132,264,48,68] 13 (by decide) (choices 1) [1,2,64] r37880 c37880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23449
  · exact u23450
  · exact u23451

def b37881 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 134 268 73 19 116 116 244 372), lower := (rows 35 134 268 73 19 32 64 128 256), losses := [] }

theorem u37881 : Upper (D 6) (R 6) [34,132,264,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37882 : Route 9 := (fun mask => (mask,id))

def c37882 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37882 : Upper (D 6) (R 6) [34,132,264,65,5] 13 := by
  apply FastRouting.sound _ _ [34,132,264,65,5] 13 (by decide) (choices 1) [2,16,64] r37882 c37882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23452
  · exact u23453
  · exact u23454

def b37883 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 268 73 22 113 113 241 369), lower := (rows 35 134 268 73 22 32 64 128 256), losses := [] }

theorem u37883 : Upper (D 6) (R 6) [34,132,264,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37884 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 268 73 49 118 86 214 342), lower := (rows 35 134 268 73 49 32 64 128 256), losses := [] }

theorem u37884 : Upper (D 6) (R 6) [34,132,264,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37885 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 268 73 50 117 85 213 341), lower := (rows 35 134 268 73 50 32 64 128 256), losses := [] }

theorem u37885 : Upper (D 6) (R 6) [34,132,264,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37886 : Route 9 := (fun mask => (mask,id))

def c37886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37886 : Upper (D 6) (R 6) [34,132,264,65,36] 13 := by
  apply FastRouting.sound _ _ [34,132,264,65,36] 13 (by decide) (choices 1) [1,2,16,64] r37886 c37886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23455
  · exact u23456
  · exact u23457
  · exact u23458

def b37887 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 134 268 73 81 54 118 182 310), lower := (rows 35 134 268 73 81 32 64 128 256), losses := [] }

theorem u37887 : Upper (D 6) (R 6) [34,132,264,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37888 : Route 9 := (fun mask => (mask,id))

def c37888 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37888 : Upper (D 6) (R 6) [34,132,264,65,66] 13 := by
  apply FastRouting.sound _ _ [34,132,264,65,66] 13 (by decide) (choices 1) [1,4,16] r37888 c37888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23459
  · exact u23460
  · exact u23461

def r37889 : Route 9 := (fun mask => (mask,id))

def c37889 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37889 : Upper (D 6) (R 6) [34,132,264,65,68] 13 := by
  apply FastRouting.sound _ _ [34,132,264,65,68] 13 (by decide) (choices 1) [1,2,16] r37889 c37889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23462
  · exact u23463
  · exact u23464

def r37890 : Route 9 := (fun mask => (mask,id))

def c37890 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37890 : Upper (D 6) (R 6) [34,132,264,65,96] 13 := by
  apply FastRouting.sound _ _ [34,132,264,65,96] 13 (by decide) (choices 1) [1,2,4,16] r37890 c37890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23465
  · exact u23466
  · exact u23467
  · exact u23468

def r37891 : Route 9 := (fun mask => (mask,id))

def c37891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37891 : Upper (D 6) (R 6) [34,132,264,66,5] 13 := by
  apply FastRouting.sound _ _ [34,132,264,66,5] 13 (by decide) (choices 1) [1,16,64] r37891 c37891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23469
  · exact u23470
  · exact u23471

def b37892 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 268 74 49 117 85 213 341), lower := (rows 35 134 268 74 49 32 64 128 256), losses := [] }

theorem u37892 : Upper (D 6) (R 6) [34,132,264,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37893 : Route 9 := (fun mask => (mask,id))

def c37893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37893 : Upper (D 6) (R 6) [34,132,264,66,36] 13 := by
  apply FastRouting.sound _ _ [34,132,264,66,36] 13 (by decide) (choices 1) [1,16,64] r37893 c37893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23472
  · exact u23473
  · exact u23474

def r37894 : Route 9 := (fun mask => (mask,id))

def c37894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37894 : Upper (D 6) (R 6) [34,132,264,66,65] 13 := by
  apply FastRouting.sound _ _ [34,132,264,66,65] 13 (by decide) (choices 1) [1,4,16] r37894 c37894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23475
  · exact u23476
  · exact u23477

def r37895 : Route 9 := (fun mask => (mask,id))

def c37895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37895 : Upper (D 6) (R 6) [34,132,264,66,68] 13 := by
  apply FastRouting.sound _ _ [34,132,264,66,68] 13 (by decide) (choices 1) [1,16] r37895 c37895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23478
  · exact u23479

def r37896 : Route 9 := (fun mask => (mask,id))

def c37896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37896 : Upper (D 6) (R 6) [34,132,264,66,96] 13 := by
  apply FastRouting.sound _ _ [34,132,264,66,96] 13 (by decide) (choices 1) [1,4,16] r37896 c37896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23480
  · exact u23481
  · exact u23482

def b37897 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(4,5),(4,6)], upper := (rows 35 134 268 76 19 113 113 241 369), lower := (rows 35 134 268 76 19 32 64 128 256), losses := [] }

theorem u37897 : Upper (D 6) (R 6) [34,132,264,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37898 : PairBound 9 := { available := 83, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 134 268 76 49 115 83 211 339), lower := (rows 35 134 268 76 49 32 64 128 256), losses := [] }

theorem u37898 : Upper (D 6) (R 6) [34,132,264,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37899 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 35 134 268 76 50 113 81 209 337), lower := (rows 35 134 268 76 50 32 64 128 256), losses := [] }

theorem u37899 : Upper (D 6) (R 6) [34,132,264,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37900 : Route 9 := (fun mask => (mask,id))

def c37900 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37900 : Upper (D 6) (R 6) [34,132,264,68,65] 13 := by
  apply FastRouting.sound _ _ [34,132,264,68,65] 13 (by decide) (choices 1) [1,2,16] r37900 c37900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23483
  · exact u23484
  · exact u23485

def b37901 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 268 76 82 49 113 177 305), lower := (rows 35 134 268 76 82 32 64 128 256), losses := [] }

theorem u37901 : Upper (D 6) (R 6) [34,132,264,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37902 : Route 9 := (fun mask => (mask,id))

def c37902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37902 : Upper (D 6) (R 6) [34,132,264,68,96] 13 := by
  apply FastRouting.sound _ _ [34,132,264,68,96] 13 (by decide) (choices 1) [1,2,16] r37902 c37902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23486
  · exact u23487
  · exact u23488

def b37903 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 134 268 88 19 101 101 229 357), lower := (rows 35 134 268 88 19 32 64 128 256), losses := [] }

theorem u37903 : Upper (D 6) (R 6) [34,132,264,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37904 : Route 9 := (fun mask => (mask,id))

def c37904 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37904 : Upper (D 6) (R 6) [34,132,264,80,5] 13 := by
  apply FastRouting.sound _ _ [34,132,264,80,5] 13 (by decide) (choices 1) [1,2,64] r37904 c37904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23489
  · exact u23490
  · exact u23491

def b37905 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 268 88 22 97 97 225 353), lower := (rows 35 134 268 88 22 32 64 128 256), losses := [] }

theorem u37905 : Upper (D 6) (R 6) [34,132,264,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37906 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 268 88 49 103 71 199 327), lower := (rows 35 134 268 88 49 32 64 128 256), losses := [] }

theorem u37906 : Upper (D 6) (R 6) [34,132,264,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37907 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 268 88 50 101 69 197 325), lower := (rows 35 134 268 88 50 32 64 128 256), losses := [] }

theorem u37907 : Upper (D 6) (R 6) [34,132,264,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37908 : Route 9 := (fun mask => (mask,id))

def c37908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37908 : Upper (D 6) (R 6) [34,132,264,80,36] 13 := by
  apply FastRouting.sound _ _ [34,132,264,80,36] 13 (by decide) (choices 1) [1,2,64] r37908 c37908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23492
  · exact u23493
  · exact u23494

def b37909 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 268 88 81 39 103 167 295), lower := (rows 35 134 268 88 81 32 64 128 256), losses := [] }

theorem u37909 : Upper (D 6) (R 6) [34,132,264,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37910 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 268 88 82 37 101 165 293), lower := (rows 35 134 268 88 82 32 64 128 256), losses := [] }

theorem u37910 : Upper (D 6) (R 6) [34,132,264,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37911 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 268 88 84 35 99 163 291), lower := (rows 35 134 268 88 84 32 64 128 256), losses := [] }

theorem u37911 : Upper (D 6) (R 6) [34,132,264,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37912 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 268 88 112 39 71 135 263), lower := (rows 35 134 268 88 112 32 64 128 256), losses := [] }

theorem u37912 : Upper (D 6) (R 6) [34,132,264,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37913 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 134 268 104 19 117 85 213 341), lower := (rows 35 134 268 104 19 32 64 128 256), losses := [] }

theorem u37913 : Upper (D 6) (R 6) [34,132,264,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37914 : Route 9 := (fun mask => (mask,id))

def c37914 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37914 : Upper (D 6) (R 6) [34,132,264,96,5] 13 := by
  apply FastRouting.sound _ _ [34,132,264,96,5] 13 (by decide) (choices 1) [1,2,16,64] r37914 c37914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23495
  · exact u23496
  · exact u23497
  · exact u23498

def b37915 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 268 104 22 113 81 209 337), lower := (rows 35 134 268 104 22 32 64 128 256), losses := [] }

theorem u37915 : Upper (D 6) (R 6) [34,132,264,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37916 : Route 9 := (fun mask => (mask,id))

def c37916 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37916 : Upper (D 6) (R 6) [34,132,264,96,65] 13 := by
  apply FastRouting.sound _ _ [34,132,264,96,65] 13 (by decide) (choices 1) [1,2,4,16] r37916 c37916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23499
  · exact u23500
  · exact u23501
  · exact u23502

def r37917 : Route 9 := (fun mask => (mask,id))

def c37917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37917 : Upper (D 6) (R 6) [34,132,264,96,66] 13 := by
  apply FastRouting.sound _ _ [34,132,264,96,66] 13 (by decide) (choices 1) [1,4,16] r37917 c37917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23503
  · exact u23504
  · exact u23505

def r37918 : Route 9 := (fun mask => (mask,id))

def c37918 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37918 : Upper (D 6) (R 6) [34,132,264,96,68] 13 := by
  apply FastRouting.sound _ _ [34,132,264,96,68] 13 (by decide) (choices 1) [1,2,16] r37918 c37918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23506
  · exact u23507
  · exact u23508

def b37919 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 292 11 21 120 88 216 344), lower := (rows 35 134 292 11 21 32 64 128 256), losses := [] }

theorem u37919 : Upper (D 6) (R 6) [34,132,288,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u37919
end Delivery.IrregularNine14.P06
