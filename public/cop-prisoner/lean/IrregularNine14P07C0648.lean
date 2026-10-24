import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0440
import IrregularNine14P07C0441
import IrregularNine14P07C0442

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38880 : Route 9 := (fun mask => (mask,id))

def c38880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38880 : Upper (D 7) (R 7) [36,264,66,18,192] 13 := by
  apply FastRouting.sound _ _ [36,264,66,18,192] 13 (by decide) (choices 1) [1,128] r38880 c38880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26445
  · exact u26446

def b38881 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,1),(1,6),(3,6),(4,1)], upper := (rows 37 266 70 42 81 177 209 145 401), lower := (rows 37 266 70 42 81 32 64 128 256), losses := [] }

theorem u38881 : Upper (D 7) (R 7) [36,264,66,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38882 : Route 9 := (fun mask => (mask,id))

def c38882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38882 : Upper (D 7) (R 7) [36,264,66,34,129] 13 := by
  apply FastRouting.sound _ _ [36,264,66,34,129] 13 (by decide) (choices 1) [1,16,64,128] r38882 c38882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26447
  · exact u26448
  · exact u26449
  · exact u26450

def r38883 : Route 9 := (fun mask => (mask,id))

def c38883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38883 : Upper (D 7) (R 7) [36,264,66,34,192] 13 := by
  apply FastRouting.sound _ _ [36,264,66,34,192] 13 (by decide) (choices 1) [1,16,128] r38883 c38883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26451
  · exact u26452
  · exact u26453

def b38884 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 161, targets := 2 },{ cop := 4, region := 232, targets := 2 },{ cop := 4, region := 196, targets := 32 }], pairs := [(0,1),(1,5),(2,5),(3,1)], upper := (rows 37 266 70 56 19 225 193 193 449), lower := (rows 37 266 70 56 19 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 28 8 16 0 81 145 273), good := (rows 453 270 70 478 471 0 64 128 256) }] }

theorem u38884 : Upper (D 7) (R 7) [36,264,66,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38885 : Route 9 := (fun mask => (mask,id))

def c38885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38885 : Upper (D 7) (R 7) [36,264,66,48,65] 13 := by
  apply FastRouting.sound _ _ [36,264,66,48,65] 13 (by decide) (choices 1) [1,2,128] r38885 c38885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26454
  · exact u26455
  · exact u26456

def b38886 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 266 70 56 82 161 193 129 385), lower := (rows 37 266 70 56 82 32 64 128 256), losses := [] }

theorem u38886 : Upper (D 7) (R 7) [36,264,66,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38887 : Route 9 := (fun mask => (mask,id))

def c38887 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38887 : Upper (D 7) (R 7) [36,264,66,48,129] 13 := by
  apply FastRouting.sound _ _ [36,264,66,48,129] 13 (by decide) (choices 1) [1,2,64,128] r38887 c38887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26457
  · exact u26458
  · exact u26459
  · exact u26460

def r38888 : Route 9 := (fun mask => (mask,id))

def c38888 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38888 : Upper (D 7) (R 7) [36,264,66,48,130] 13 := by
  apply FastRouting.sound _ _ [36,264,66,48,130] 13 (by decide) (choices 1) [1,64,128] r38888 c38888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26461
  · exact u26462
  · exact u26463

def r38889 : Route 9 := (fun mask => (mask,id))

def c38889 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38889 : Upper (D 7) (R 7) [36,264,66,48,192] 13 := by
  apply FastRouting.sound _ _ [36,264,66,48,192] 13 (by decide) (choices 1) [1,2,128] r38889 c38889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26464
  · exact u26465
  · exact u26466

def b38890 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 228, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 37 266 70 73 19 176 240 176 432), lower := (rows 37 266 70 73 19 32 64 128 256), losses := [] }

theorem u38890 : Upper (D 7) (R 7) [36,264,66,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38891 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 70 73 49 178 210 146 402), lower := (rows 37 266 70 73 49 32 64 128 256), losses := [] }

theorem u38891 : Upper (D 7) (R 7) [36,264,66,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38892 : Route 9 := (fun mask => (mask,id))

def c38892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38892 : Upper (D 7) (R 7) [36,264,66,65,34] 13 := by
  apply FastRouting.sound _ _ [36,264,66,65,34] 13 (by decide) (choices 1) [1,16,128] r38892 c38892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26467
  · exact u26468
  · exact u26469

def r38893 : Route 9 := (fun mask => (mask,id))

def c38893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38893 : Upper (D 7) (R 7) [36,264,66,65,129] 13 := by
  apply FastRouting.sound _ _ [36,264,66,65,129] 13 (by decide) (choices 1) [2,16,128] r38893 c38893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26470
  · exact u26471
  · exact u26472

def r38894 : Route 9 := (fun mask => (mask,id))

def c38894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38894 : Upper (D 7) (R 7) [36,264,66,65,130] 13 := by
  apply FastRouting.sound _ _ [36,264,66,65,130] 13 (by decide) (choices 1) [1,16,128] r38894 c38894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26473
  · exact u26474
  · exact u26475

def r38895 : Route 9 := (fun mask => (mask,id))

def c38895 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38895 : Upper (D 7) (R 7) [36,264,66,65,160] 13 := by
  apply FastRouting.sound _ _ [36,264,66,65,160] 13 (by decide) (choices 1) [1,2,16,128] r38895 c38895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26476
  · exact u26477
  · exact u26478
  · exact u26479

def b38896 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 2, region := 161, targets := 2 },{ cop := 4, region := 232, targets := 2 }], pairs := [(0,1),(0,6),(3,1),(4,6)], upper := (rows 37 266 70 88 19 161 225 161 417), lower := (rows 37 266 70 88 19 32 64 128 256), losses := [] }

theorem u38896 : Upper (D 7) (R 7) [36,264,66,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38897 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 70 88 49 163 195 131 387), lower := (rows 37 266 70 88 49 32 64 128 256), losses := [] }

theorem u38897 : Upper (D 7) (R 7) [36,264,66,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38898 : Route 9 := (fun mask => (mask,id))

def c38898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38898 : Upper (D 7) (R 7) [36,264,66,80,34] 13 := by
  apply FastRouting.sound _ _ [36,264,66,80,34] 13 (by decide) (choices 1) [1,128] r38898 c38898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26480
  · exact u26481

def r38899 : Route 9 := (fun mask => (mask,id))

def c38899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38899 : Upper (D 7) (R 7) [36,264,66,80,129] 13 := by
  apply FastRouting.sound _ _ [36,264,66,80,129] 13 (by decide) (choices 1) [1,2,128] r38899 c38899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26482
  · exact u26483
  · exact u26484

def r38900 : Route 9 := (fun mask => (mask,id))

def c38900 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38900 : Upper (D 7) (R 7) [36,264,66,80,130] 13 := by
  apply FastRouting.sound _ _ [36,264,66,80,130] 13 (by decide) (choices 1) [1,128] r38900 c38900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26485
  · exact u26486

def r38901 : Route 9 := (fun mask => (mask,id))

def c38901 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38901 : Upper (D 7) (R 7) [36,264,66,80,160] 13 := by
  apply FastRouting.sound _ _ [36,264,66,80,160] 13 (by decide) (choices 1) [1,2,128] r38901 c38901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26487
  · exact u26488
  · exact u26489

def b38902 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 232, targets := 2 },{ cop := 4, region := 196, targets := 32 }], pairs := [(0,6),(2,5),(3,1),(4,6)], upper := (rows 37 266 70 104 19 177 209 145 401), lower := (rows 37 266 70 104 19 32 64 128 256), losses := [] }

theorem u38902 : Upper (D 7) (R 7) [36,264,66,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38903 : Route 9 := (fun mask => (mask,id))

def c38903 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38903 : Upper (D 7) (R 7) [36,264,66,96,129] 13 := by
  apply FastRouting.sound _ _ [36,264,66,96,129] 13 (by decide) (choices 1) [1,2,16,128] r38903 c38903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26490
  · exact u26491
  · exact u26492
  · exact u26493

def r38904 : Route 9 := (fun mask => (mask,id))

def c38904 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38904 : Upper (D 7) (R 7) [36,264,66,96,130] 13 := by
  apply FastRouting.sound _ _ [36,264,66,96,130] 13 (by decide) (choices 1) [1,16,128] r38904 c38904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26494
  · exact u26495
  · exact u26496

def r38905 : Route 9 := (fun mask => (mask,id))

def c38905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38905 : Upper (D 7) (R 7) [36,264,66,129,3] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129,3] 13 (by decide) (choices 1) [16,64,128] r38905 c38905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26497
  · exact u26498
  · exact u26499

def b38906 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 70 137 49 242 210 210 466), lower := (rows 37 266 70 137 49 32 64 128 256), losses := [] }

theorem u38906 : Upper (D 7) (R 7) [36,264,66,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38907 : Route 9 := (fun mask => (mask,id))

def c38907 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38907 : Upper (D 7) (R 7) [36,264,66,129,34] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129,34] 13 (by decide) (choices 1) [1,16,64,128] r38907 c38907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26500
  · exact u26501
  · exact u26502
  · exact u26503

def r38908 : Route 9 := (fun mask => (mask,id))

def c38908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38908 : Upper (D 7) (R 7) [36,264,66,129,65] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129,65] 13 (by decide) (choices 1) [2,16,128] r38908 c38908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26504
  · exact u26505
  · exact u26506

def b38909 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 266 70 137 82 177 241 177 433), lower := (rows 37 266 70 137 82 32 64 128 256), losses := [] }

theorem u38909 : Upper (D 7) (R 7) [36,264,66,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38910 : Route 9 := (fun mask => (mask,id))

def c38910 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38910 : Upper (D 7) (R 7) [36,264,66,129,96] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129,96] 13 (by decide) (choices 1) [1,2,16,128] r38910 c38910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26507
  · exact u26508
  · exact u26509
  · exact u26510

def b38911 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 266 70 137 145 114 114 242 370), lower := (rows 37 266 70 137 145 32 64 128 256), losses := [] }

theorem u38911 : Upper (D 7) (R 7) [36,264,66,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38912 : Route 9 := (fun mask => (mask,id))

def c38912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38912 : Upper (D 7) (R 7) [36,264,66,129,130] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129,130] 13 (by decide) (choices 1) [1,16,64] r38912 c38912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26511
  · exact u26512
  · exact u26513

def r38913 : Route 9 := (fun mask => (mask,id))

def c38913 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38913 : Upper (D 7) (R 7) [36,264,66,129,160] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129,160] 13 (by decide) (choices 1) [1,2,16,64] r38913 c38913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26514
  · exact u26515
  · exact u26516
  · exact u26517

def r38914 : Route 9 := (fun mask => (mask,id))

def c38914 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38914 : Upper (D 7) (R 7) [36,264,66,129,192] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129,192] 13 (by decide) (choices 1) [1,2,16] r38914 c38914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26518
  · exact u26519
  · exact u26520

def b38915 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 266 70 138 49 241 209 209 465), lower := (rows 37 266 70 138 49 32 64 128 256), losses := [] }

theorem u38915 : Upper (D 7) (R 7) [36,264,66,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38916 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,1),(1,6),(3,6),(4,1)], upper := (rows 37 266 70 138 81 177 241 177 433), lower := (rows 37 266 70 138 81 32 64 128 256), losses := [] }

theorem u38916 : Upper (D 7) (R 7) [36,264,66,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38917 : Route 9 := (fun mask => (mask,id))

def c38917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38917 : Upper (D 7) (R 7) [36,264,66,130,96] 13 := by
  apply FastRouting.sound _ _ [36,264,66,130,96] 13 (by decide) (choices 1) [1,16,128] r38917 c38917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26521
  · exact u26522
  · exact u26523

def r38918 : Route 9 := (fun mask => (mask,id))

def c38918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38918 : Upper (D 7) (R 7) [36,264,66,130,129] 13 := by
  apply FastRouting.sound _ _ [36,264,66,130,129] 13 (by decide) (choices 1) [1,16,64] r38918 c38918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26524
  · exact u26525
  · exact u26526

def r38919 : Route 9 := (fun mask => (mask,id))

def c38919 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38919 : Upper (D 7) (R 7) [36,264,66,130,160] 13 := by
  apply FastRouting.sound _ _ [36,264,66,130,160] 13 (by decide) (choices 1) [1,16,64] r38919 c38919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26527
  · exact u26528
  · exact u26529

def r38920 : Route 9 := (fun mask => (mask,id))

def c38920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38920 : Upper (D 7) (R 7) [36,264,66,130,192] 13 := by
  apply FastRouting.sound _ _ [36,264,66,130,192] 13 (by decide) (choices 1) [1,16] r38920 c38920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26530
  · exact u26531

def r38921 : Route 9 := (fun mask => (mask,id))

def c38921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38921 : Upper (D 7) (R 7) [36,264,66,144,3] 13 := by
  apply FastRouting.sound _ _ [36,264,66,144,3] 13 (by decide) (choices 1) [1,64,128] r38921 c38921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26532
  · exact u26533
  · exact u26534

def b38922 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 70 152 49 227 195 195 451), lower := (rows 37 266 70 152 49 32 64 128 256), losses := [] }

theorem u38922 : Upper (D 7) (R 7) [36,264,66,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38923 : Route 9 := (fun mask => (mask,id))

def c38923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38923 : Upper (D 7) (R 7) [36,264,66,144,34] 13 := by
  apply FastRouting.sound _ _ [36,264,66,144,34] 13 (by decide) (choices 1) [1,64,128] r38923 c38923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26535
  · exact u26536
  · exact u26537

def r38924 : Route 9 := (fun mask => (mask,id))

def c38924 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38924 : Upper (D 7) (R 7) [36,264,66,144,65] 13 := by
  apply FastRouting.sound _ _ [36,264,66,144,65] 13 (by decide) (choices 1) [1,2,128] r38924 c38924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26538
  · exact u26539
  · exact u26540

def b38925 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 266 70 152 82 161 225 161 417), lower := (rows 37 266 70 152 82 32 64 128 256), losses := [] }

theorem u38925 : Upper (D 7) (R 7) [36,264,66,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38926 : Route 9 := (fun mask => (mask,id))

def c38926 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38926 : Upper (D 7) (R 7) [36,264,66,144,96] 13 := by
  apply FastRouting.sound _ _ [36,264,66,144,96] 13 (by decide) (choices 1) [1,2,128] r38926 c38926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26541
  · exact u26542
  · exact u26543

def b38927 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 266 70 152 145 99 99 227 355), lower := (rows 37 266 70 152 145 32 64 128 256), losses := [] }

theorem u38927 : Upper (D 7) (R 7) [36,264,66,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38928 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 266 70 152 146 97 97 225 353), lower := (rows 37 266 70 152 146 32 64 128 256), losses := [] }

theorem u38928 : Upper (D 7) (R 7) [36,264,66,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38929 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 266 70 152 176 99 67 195 323), lower := (rows 37 266 70 152 176 32 64 128 256), losses := [] }

theorem u38929 : Upper (D 7) (R 7) [36,264,66,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38930 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 266 70 152 208 35 99 163 291), lower := (rows 37 266 70 152 208 32 64 128 256), losses := [] }

theorem u38930 : Upper (D 7) (R 7) [36,264,66,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38931 : Route 9 := (fun mask => (mask,id))

def c38931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38931 : Upper (D 7) (R 7) [36,264,66,160,3] 13 := by
  apply FastRouting.sound _ _ [36,264,66,160,3] 13 (by decide) (choices 1) [1,16,64,128] r38931 c38931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26544
  · exact u26545
  · exact u26546
  · exact u26547

def r38932 : Route 9 := (fun mask => (mask,id))

def c38932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38932 : Upper (D 7) (R 7) [36,264,66,160,65] 13 := by
  apply FastRouting.sound _ _ [36,264,66,160,65] 13 (by decide) (choices 1) [1,2,16,128] r38932 c38932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26548
  · exact u26549
  · exact u26550
  · exact u26551

def b38933 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 266 70 168 82 177 209 145 401), lower := (rows 37 266 70 168 82 32 64 128 256), losses := [] }

theorem u38933 : Upper (D 7) (R 7) [36,264,66,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38934 : Route 9 := (fun mask => (mask,id))

def c38934 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38934 : Upper (D 7) (R 7) [36,264,66,160,129] 13 := by
  apply FastRouting.sound _ _ [36,264,66,160,129] 13 (by decide) (choices 1) [1,2,16,64] r38934 c38934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26552
  · exact u26553
  · exact u26554
  · exact u26555

def r38935 : Route 9 := (fun mask => (mask,id))

def c38935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38935 : Upper (D 7) (R 7) [36,264,66,160,130] 13 := by
  apply FastRouting.sound _ _ [36,264,66,160,130] 13 (by decide) (choices 1) [1,16,64] r38935 c38935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26556
  · exact u26557
  · exact u26558

def r38936 : Route 9 := (fun mask => (mask,id))

def c38936 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38936 : Upper (D 7) (R 7) [36,264,66,160,192] 13 := by
  apply FastRouting.sound _ _ [36,264,66,160,192] 13 (by decide) (choices 1) [1,2,16] r38936 c38936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26559
  · exact u26560
  · exact u26561

def r38937 : Route 9 := (fun mask => (mask,id))

def c38937 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38937 : Upper (D 7) (R 7) [36,264,66,192,3] 13 := by
  apply FastRouting.sound _ _ [36,264,66,192,3] 13 (by decide) (choices 1) [1,16,128] r38937 c38937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26562
  · exact u26563
  · exact u26564

def b38938 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 70 200 49 179 211 147 403), lower := (rows 37 266 70 200 49 32 64 128 256), losses := [] }

theorem u38938 : Upper (D 7) (R 7) [36,264,66,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38939 : Route 9 := (fun mask => (mask,id))

def c38939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38939 : Upper (D 7) (R 7) [36,264,66,192,34] 13 := by
  apply FastRouting.sound _ _ [36,264,66,192,34] 13 (by decide) (choices 1) [1,16,128] r38939 c38939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26565
  · exact u26566
  · exact u26567

#print axioms u38939
end Delivery.IrregularNine14.P07
