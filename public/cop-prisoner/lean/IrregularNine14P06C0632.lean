import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0391
import IrregularNine14P06C0392
import IrregularNine14P06C0393

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37920 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 292 11 25 116 84 212 340), lower := (rows 35 134 292 11 25 32 64 128 256), losses := [] }

theorem u37920 : Upper (D 6) (R 6) [34,132,288,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37921 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 292 11 28 113 81 209 337), lower := (rows 35 134 292 11 28 32 64 128 256), losses := [] }

theorem u37921 : Upper (D 6) (R 6) [34,132,288,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37922 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 292 11 81 124 92 220 348), lower := (rows 35 134 292 11 81 32 64 128 256), losses := [] }

theorem u37922 : Upper (D 6) (R 6) [34,132,288,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37923 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 292 11 84 121 89 217 345), lower := (rows 35 134 292 11 84 32 64 128 256), losses := [] }

theorem u37923 : Upper (D 6) (R 6) [34,132,288,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37924 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 292 11 88 117 85 213 341), lower := (rows 35 134 292 11 88 32 64 128 256), losses := [] }

theorem u37924 : Upper (D 6) (R 6) [34,132,288,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37925 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 292 13 25 114 82 210 338), lower := (rows 35 134 292 13 25 32 64 128 256), losses := [] }

theorem u37925 : Upper (D 6) (R 6) [34,132,288,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37926 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 134 292 13 26 113 81 209 337), lower := (rows 35 134 292 13 26 32 64 128 256), losses := [] }

theorem u37926 : Upper (D 6) (R 6) [34,132,288,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37927 : Route 9 := (fun mask => (mask,id))

def c37927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37927 : Upper (D 6) (R 6) [34,132,288,5,65] 13 := by
  apply FastRouting.sound _ _ [34,132,288,5,65] 13 (by decide) (choices 1) [2,8,16,64] r37927 c37927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23509
  · exact u23510
  · exact u23511
  · exact u23512

def r37928 : Route 9 := (fun mask => (mask,id))

def c37928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37928 : Upper (D 6) (R 6) [34,132,288,5,66] 13 := by
  apply FastRouting.sound _ _ [34,132,288,5,66] 13 (by decide) (choices 1) [1,8,16,64] r37928 c37928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23513
  · exact u23514
  · exact u23515
  · exact u23516

def r37929 : Route 9 := (fun mask => (mask,id))

def c37929 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37929 : Upper (D 6) (R 6) [34,132,288,5,72] 13 := by
  apply FastRouting.sound _ _ [34,132,288,5,72] 13 (by decide) (choices 1) [1,2,16,64] r37929 c37929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23517
  · exact u23518
  · exact u23519
  · exact u23520

def b37930 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 292 14 25 113 81 209 337), lower := (rows 35 134 292 14 25 32 64 128 256), losses := [] }

theorem u37930 : Upper (D 6) (R 6) [34,132,288,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37931 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 292 14 81 121 89 217 345), lower := (rows 35 134 292 14 81 32 64 128 256), losses := [] }

theorem u37931 : Upper (D 6) (R 6) [34,132,288,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37932 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 292 14 88 113 81 209 337), lower := (rows 35 134 292 14 88 32 64 128 256), losses := [] }

theorem u37932 : Upper (D 6) (R 6) [34,132,288,6,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37933 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 292 25 25 102 70 198 326), lower := (rows 35 134 292 25 25 32 64 128 256), losses := [] }

theorem u37933 : Upper (D 6) (R 6) [34,132,288,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37934 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 292 25 26 101 69 197 325), lower := (rows 35 134 292 25 26 32 64 128 256), losses := [] }

theorem u37934 : Upper (D 6) (R 6) [34,132,288,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37935 : Route 9 := (fun mask => (mask,id))

def c37935 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37935 : Upper (D 6) (R 6) [34,132,288,17,12] 13 := by
  apply FastRouting.sound _ _ [34,132,288,17,12] 13 (by decide) (choices 1) [1,2,64] r37935 c37935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23521
  · exact u23522
  · exact u23523

def b37936 : PairBound 9 := { available := 78, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 292 25 81 110 78 206 334), lower := (rows 35 134 292 25 81 32 64 128 256), losses := [] }

theorem u37936 : Upper (D 6) (R 6) [34,132,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37937 : Route 9 := (fun mask => (mask,id))

def c37937 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37937 : Upper (D 6) (R 6) [34,132,288,17,66] 13 := by
  apply FastRouting.sound _ _ [34,132,288,17,66] 13 (by decide) (choices 1) [1,4,8,64] r37937 c37937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23524
  · exact u23525
  · exact u23526
  · exact u23527

def r37938 : Route 9 := (fun mask => (mask,id))

def c37938 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37938 : Upper (D 6) (R 6) [34,132,288,17,68] 13 := by
  apply FastRouting.sound _ _ [34,132,288,17,68] 13 (by decide) (choices 1) [1,2,8,64] r37938 c37938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23528
  · exact u23529
  · exact u23530
  · exact u23531

def r37939 : Route 9 := (fun mask => (mask,id))

def c37939 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37939 : Upper (D 6) (R 6) [34,132,288,17,72] 13 := by
  apply FastRouting.sound _ _ [34,132,288,17,72] 13 (by decide) (choices 1) [1,2,4,64] r37939 c37939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23532
  · exact u23533
  · exact u23534
  · exact u23535

def b37940 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 292 26 28 97 65 193 321), lower := (rows 35 134 292 26 28 32 64 128 256), losses := [] }

theorem u37940 : Upper (D 6) (R 6) [34,132,288,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37941 : Route 9 := (fun mask => (mask,id))

def c37941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37941 : Upper (D 6) (R 6) [34,132,288,18,65] 13 := by
  apply FastRouting.sound _ _ [34,132,288,18,65] 13 (by decide) (choices 1) [1,4,8,64] r37941 c37941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23536
  · exact u23537
  · exact u23538
  · exact u23539

def r37942 : Route 9 := (fun mask => (mask,id))

def c37942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37942 : Upper (D 6) (R 6) [34,132,288,18,68] 13 := by
  apply FastRouting.sound _ _ [34,132,288,18,68] 13 (by decide) (choices 1) [1,8,64] r37942 c37942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23540
  · exact u23541
  · exact u23542

def r37943 : Route 9 := (fun mask => (mask,id))

def c37943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37943 : Upper (D 6) (R 6) [34,132,288,18,72] 13 := by
  apply FastRouting.sound _ _ [34,132,288,18,72] 13 (by decide) (choices 1) [1,4,64] r37943 c37943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23543
  · exact u23544
  · exact u23545

def r37944 : Route 9 := (fun mask => (mask,id))

def c37944 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37944 : Upper (D 6) (R 6) [34,132,288,20,65] 13 := by
  apply FastRouting.sound _ _ [34,132,288,20,65] 13 (by decide) (choices 1) [1,2,8,64] r37944 c37944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23546
  · exact u23547
  · exact u23548
  · exact u23549

def r37945 : Route 9 := (fun mask => (mask,id))

def c37945 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37945 : Upper (D 6) (R 6) [34,132,288,20,66] 13 := by
  apply FastRouting.sound _ _ [34,132,288,20,66] 13 (by decide) (choices 1) [1,8,64] r37945 c37945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23550
  · exact u23551
  · exact u23552

def r37946 : Route 9 := (fun mask => (mask,id))

def c37946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37946 : Upper (D 6) (R 6) [34,132,288,20,72] 13 := by
  apply FastRouting.sound _ _ [34,132,288,20,72] 13 (by decide) (choices 1) [1,2,64] r37946 c37946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23553
  · exact u23554
  · exact u23555

def b37947 : PairBound 9 := { available := 30, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 134 292 73 81 62 94 158 286), lower := (rows 35 134 292 73 81 32 64 128 256), losses := [] }

theorem u37947 : Upper (D 6) (R 6) [34,132,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37948 : Route 9 := (fun mask => (mask,id))

def c37948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37948 : Upper (D 6) (R 6) [34,132,288,65,66] 13 := by
  apply FastRouting.sound _ _ [34,132,288,65,66] 13 (by decide) (choices 1) [1,4,8,16] r37948 c37948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23556
  · exact u23557
  · exact u23558
  · exact u23559

def r37949 : Route 9 := (fun mask => (mask,id))

def c37949 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37949 : Upper (D 6) (R 6) [34,132,288,65,68] 13 := by
  apply FastRouting.sound _ _ [34,132,288,65,68] 13 (by decide) (choices 1) [1,2,8,16] r37949 c37949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23560
  · exact u23561
  · exact u23562
  · exact u23563

def b37950 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 134 292 73 88 55 87 151 279), lower := (rows 35 134 292 73 88 32 64 128 256), losses := [] }

theorem u37950 : Upper (D 6) (R 6) [34,132,288,65,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37951 : Route 9 := (fun mask => (mask,id))

def c37951 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37951 : Upper (D 6) (R 6) [34,132,288,66,68] 13 := by
  apply FastRouting.sound _ _ [34,132,288,66,68] 13 (by decide) (choices 1) [1,8,16] r37951 c37951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23564
  · exact u23565
  · exact u23566

def b37952 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 134 292 74 88 53 85 149 277), lower := (rows 35 134 292 74 88 32 64 128 256), losses := [] }

theorem u37952 : Upper (D 6) (R 6) [34,132,288,66,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37953 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 134 292 76 88 51 83 147 275), lower := (rows 35 134 292 76 88 32 64 128 256), losses := [] }

theorem u37953 : Upper (D 6) (R 6) [34,132,288,68,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37954 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 292 88 88 39 71 135 263), lower := (rows 35 134 292 88 88 32 64 128 256), losses := [] }

theorem u37954 : Upper (D 6) (R 6) [34,132,288,80,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37955 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 324 11 21 120 120 248 376), lower := (rows 35 134 324 11 21 32 64 128 256), losses := [] }

theorem u37955 : Upper (D 6) (R 6) [34,132,320,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37956 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 324 11 25 116 116 244 372), lower := (rows 35 134 324 11 25 32 64 128 256), losses := [] }

theorem u37956 : Upper (D 6) (R 6) [34,132,320,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37957 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 324 11 28 113 113 241 369), lower := (rows 35 134 324 11 28 32 64 128 256), losses := [] }

theorem u37957 : Upper (D 6) (R 6) [34,132,320,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37958 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 324 11 52 121 89 217 345), lower := (rows 35 134 324 11 52 32 64 128 256), losses := [] }

theorem u37958 : Upper (D 6) (R 6) [34,132,320,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37959 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 324 11 56 117 85 213 341), lower := (rows 35 134 324 11 56 32 64 128 256), losses := [] }

theorem u37959 : Upper (D 6) (R 6) [34,132,320,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37960 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 324 11 81 60 124 188 316), lower := (rows 35 134 324 11 81 32 64 128 256), losses := [] }

theorem u37960 : Upper (D 6) (R 6) [34,132,320,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37961 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 324 11 88 53 117 181 309), lower := (rows 35 134 324 11 88 32 64 128 256), losses := [] }

theorem u37961 : Upper (D 6) (R 6) [34,132,320,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37962 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 324 11 112 61 93 157 285), lower := (rows 35 134 324 11 112 32 64 128 256), losses := [] }

theorem u37962 : Upper (D 6) (R 6) [34,132,320,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37963 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 134 324 13 25 114 114 242 370), lower := (rows 35 134 324 13 25 32 64 128 256), losses := [] }

theorem u37963 : Upper (D 6) (R 6) [34,132,320,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37964 : Route 9 := (fun mask => (mask,id))

def c37964 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37964 : Upper (D 6) (R 6) [34,132,320,5,10] 13 := by
  apply FastRouting.sound _ _ [34,132,320,5,10] 13 (by decide) (choices 1) [1,16,64] r37964 c37964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23567
  · exact u23568
  · exact u23569

def b37965 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 324 13 49 122 90 218 346), lower := (rows 35 134 324 13 49 32 64 128 256), losses := [] }

theorem u37965 : Upper (D 6) (R 6) [34,132,320,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37966 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 324 13 50 121 89 217 345), lower := (rows 35 134 324 13 50 32 64 128 256), losses := [] }

theorem u37966 : Upper (D 6) (R 6) [34,132,320,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37967 : Route 9 := (fun mask => (mask,id))

def c37967 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37967 : Upper (D 6) (R 6) [34,132,320,5,40] 13 := by
  apply FastRouting.sound _ _ [34,132,320,5,40] 13 (by decide) (choices 1) [1,2,16,64] r37967 c37967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23570
  · exact u23571
  · exact u23572
  · exact u23573

def r37968 : Route 9 := (fun mask => (mask,id))

def c37968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37968 : Upper (D 6) (R 6) [34,132,320,5,65] 13 := by
  apply FastRouting.sound _ _ [34,132,320,5,65] 13 (by decide) (choices 1) [2,8,16] r37968 c37968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23574
  · exact u23575
  · exact u23576

def r37969 : Route 9 := (fun mask => (mask,id))

def c37969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37969 : Upper (D 6) (R 6) [34,132,320,5,66] 13 := by
  apply FastRouting.sound _ _ [34,132,320,5,66] 13 (by decide) (choices 1) [1,8,16] r37969 c37969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23577
  · exact u23578
  · exact u23579

def r37970 : Route 9 := (fun mask => (mask,id))

def c37970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37970 : Upper (D 6) (R 6) [34,132,320,5,72] 13 := by
  apply FastRouting.sound _ _ [34,132,320,5,72] 13 (by decide) (choices 1) [1,2,16] r37970 c37970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23580
  · exact u23581
  · exact u23582

def r37971 : Route 9 := (fun mask => (mask,id))

def c37971 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37971 : Upper (D 6) (R 6) [34,132,320,5,96] 13 := by
  apply FastRouting.sound _ _ [34,132,320,5,96] 13 (by decide) (choices 1) [1,2,8,16] r37971 c37971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23583
  · exact u23584
  · exact u23585
  · exact u23586

def b37972 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 324 14 25 113 113 241 369), lower := (rows 35 134 324 14 25 32 64 128 256), losses := [] }

theorem u37972 : Upper (D 6) (R 6) [34,132,320,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37973 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 324 14 56 113 81 209 337), lower := (rows 35 134 324 14 56 32 64 128 256), losses := [] }

theorem u37973 : Upper (D 6) (R 6) [34,132,320,6,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37974 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 324 14 81 57 121 185 313), lower := (rows 35 134 324 14 81 32 64 128 256), losses := [] }

theorem u37974 : Upper (D 6) (R 6) [34,132,320,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37975 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 324 14 88 49 113 177 305), lower := (rows 35 134 324 14 88 32 64 128 256), losses := [] }

theorem u37975 : Upper (D 6) (R 6) [34,132,320,6,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37976 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 324 14 112 57 89 153 281), lower := (rows 35 134 324 14 112 32 64 128 256), losses := [] }

theorem u37976 : Upper (D 6) (R 6) [34,132,320,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37977 : PairBound 9 := { available := 102, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 324 25 25 102 102 230 358), lower := (rows 35 134 324 25 25 32 64 128 256), losses := [] }

theorem u37977 : Upper (D 6) (R 6) [34,132,320,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37978 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 324 25 26 101 101 229 357), lower := (rows 35 134 324 25 26 32 64 128 256), losses := [] }

theorem u37978 : Upper (D 6) (R 6) [34,132,320,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37979 : Route 9 := (fun mask => (mask,id))

def c37979 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37979 : Upper (D 6) (R 6) [34,132,320,17,12] 13 := by
  apply FastRouting.sound _ _ [34,132,320,17,12] 13 (by decide) (choices 1) [1,2,64] r37979 c37979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23587
  · exact u23588
  · exact u23589

#print axioms u37979
end Delivery.IrregularNine14.P06
