import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0230
import IrregularNine14P06C0231
import IrregularNine14P06C0232

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31620 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 38 196 104 19 309 341 405 277), lower := (rows 11 38 196 104 19 32 64 128 256), losses := [] }

theorem u31620 : Upper (D 6) (R 6) [10,36,192,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31621 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 38 196 104 21 307 339 403 275), lower := (rows 11 38 196 104 21 32 64 128 256), losses := [] }

theorem u31621 : Upper (D 6) (R 6) [10,36,192,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31622 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 196 104 22 305 337 401 273), lower := (rows 11 38 196 104 22 32 64 128 256), losses := [] }

theorem u31622 : Upper (D 6) (R 6) [10,36,192,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31623 : Route 9 := (fun mask => (mask,id))

def c31623 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31623 : Upper (D 6) (R 6) [10,36,192,96,257] 13 := by
  apply FastRouting.sound _ _ [10,36,192,96,257] 13 (by decide) (choices 1) [1,2,4,16] r31623 c31623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13846
  · exact u13847
  · exact u13848
  · exact u13849

def r31624 : Route 9 := (fun mask => (mask,id))

def c31624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31624 : Upper (D 6) (R 6) [10,36,192,96,258] 13 := by
  apply FastRouting.sound _ _ [10,36,192,96,258] 13 (by decide) (choices 1) [1,4,16] r31624 c31624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13850
  · exact u13851
  · exact u13852

def r31625 : Route 9 := (fun mask => (mask,id))

def c31625 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31625 : Upper (D 6) (R 6) [10,36,192,96,260] 13 := by
  apply FastRouting.sound _ _ [10,36,192,96,260] 13 (by decide) (choices 1) [1,2,16] r31625 c31625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13853
  · exact u13854
  · exact u13855

def b31626 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 196 265 19 116 116 244 372), lower := (rows 11 38 196 265 19 32 64 128 256), losses := [] }

theorem u31626 : Upper (D 6) (R 6) [10,36,192,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31627 : Route 9 := (fun mask => (mask,id))

def c31627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31627 : Upper (D 6) (R 6) [10,36,192,257,5] 13 := by
  apply FastRouting.sound _ _ [10,36,192,257,5] 13 (by decide) (choices 1) [2,16,64] r31627 c31627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13856
  · exact u13857
  · exact u13858

def b31628 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 196 265 22 113 113 241 369), lower := (rows 11 38 196 265 22 32 64 128 256), losses := [] }

theorem u31628 : Upper (D 6) (R 6) [10,36,192,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31629 : Route 9 := (fun mask => (mask,id))

def c31629 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31629 : Upper (D 6) (R 6) [10,36,192,257,33] 13 := by
  apply FastRouting.sound _ _ [10,36,192,257,33] 13 (by decide) (choices 1) [2,4,16,64] r31629 c31629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13859
  · exact u13860
  · exact u13861
  · exact u13862

def b31630 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 196 265 50 117 85 213 341), lower := (rows 11 38 196 265 50 32 64 128 256), losses := [] }

theorem u31630 : Upper (D 6) (R 6) [10,36,192,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31631 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 196 265 52 115 83 211 339), lower := (rows 11 38 196 265 52 32 64 128 256), losses := [] }

theorem u31631 : Upper (D 6) (R 6) [10,36,192,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31632 : Route 9 := (fun mask => (mask,id))

def c31632 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31632 : Upper (D 6) (R 6) [10,36,192,257,65] 13 := by
  apply FastRouting.sound _ _ [10,36,192,257,65] 13 (by decide) (choices 1) [2,4,16] r31632 c31632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13863
  · exact u13864
  · exact u13865

def r31633 : Route 9 := (fun mask => (mask,id))

def c31633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31633 : Upper (D 6) (R 6) [10,36,192,257,66] 13 := by
  apply FastRouting.sound _ _ [10,36,192,257,66] 13 (by decide) (choices 1) [1,4,16] r31633 c31633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13866
  · exact u13867
  · exact u13868

def b31634 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 196 265 84 51 115 179 307), lower := (rows 11 38 196 265 84 32 64 128 256), losses := [] }

theorem u31634 : Upper (D 6) (R 6) [10,36,192,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31635 : Route 9 := (fun mask => (mask,id))

def c31635 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31635 : Upper (D 6) (R 6) [10,36,192,257,96] 13 := by
  apply FastRouting.sound _ _ [10,36,192,257,96] 13 (by decide) (choices 1) [1,2,4,16] r31635 c31635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13869
  · exact u13870
  · exact u13871
  · exact u13872

def b31636 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 38 196 268 19 113 113 241 369), lower := (rows 11 38 196 268 19 32 64 128 256), losses := [] }

theorem u31636 : Upper (D 6) (R 6) [10,36,192,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31637 : Route 9 := (fun mask => (mask,id))

def c31637 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31637 : Upper (D 6) (R 6) [10,36,192,260,33] 13 := by
  apply FastRouting.sound _ _ [10,36,192,260,33] 13 (by decide) (choices 1) [1,2,16,64] r31637 c31637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13873
  · exact u13874
  · exact u13875
  · exact u13876

def b31638 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 196 268 50 113 81 209 337), lower := (rows 11 38 196 268 50 32 64 128 256), losses := [] }

theorem u31638 : Upper (D 6) (R 6) [10,36,192,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31639 : Route 9 := (fun mask => (mask,id))

def c31639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31639 : Upper (D 6) (R 6) [10,36,192,260,65] 13 := by
  apply FastRouting.sound _ _ [10,36,192,260,65] 13 (by decide) (choices 1) [1,2,16] r31639 c31639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13877
  · exact u13878
  · exact u13879

def r31640 : Route 9 := (fun mask => (mask,id))

def c31640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31640 : Upper (D 6) (R 6) [10,36,192,260,66] 13 := by
  apply FastRouting.sound _ _ [10,36,192,260,66] 13 (by decide) (choices 1) [1,16] r31640 c31640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13880
  · exact u13881

def r31641 : Route 9 := (fun mask => (mask,id))

def c31641 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31641 : Upper (D 6) (R 6) [10,36,192,260,96] 13 := by
  apply FastRouting.sound _ _ [10,36,192,260,96] 13 (by decide) (choices 1) [1,2,16] r31641 c31641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13882
  · exact u13883
  · exact u13884

def b31642 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 196 280 19 101 101 229 357), lower := (rows 11 38 196 280 19 32 64 128 256), losses := [] }

theorem u31642 : Upper (D 6) (R 6) [10,36,192,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31643 : Route 9 := (fun mask => (mask,id))

def c31643 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31643 : Upper (D 6) (R 6) [10,36,192,272,5] 13 := by
  apply FastRouting.sound _ _ [10,36,192,272,5] 13 (by decide) (choices 1) [1,2,64] r31643 c31643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13885
  · exact u13886
  · exact u13887

def b31644 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 196 280 22 97 97 225 353), lower := (rows 11 38 196 280 22 32 64 128 256), losses := [] }

theorem u31644 : Upper (D 6) (R 6) [10,36,192,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31645 : Route 9 := (fun mask => (mask,id))

def c31645 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31645 : Upper (D 6) (R 6) [10,36,192,272,33] 13 := by
  apply FastRouting.sound _ _ [10,36,192,272,33] 13 (by decide) (choices 1) [1,2,4,64] r31645 c31645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13888
  · exact u13889
  · exact u13890
  · exact u13891

def b31646 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 196 280 50 101 69 197 325), lower := (rows 11 38 196 280 50 32 64 128 256), losses := [] }

theorem u31646 : Upper (D 6) (R 6) [10,36,192,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31647 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 196 280 52 99 67 195 323), lower := (rows 11 38 196 280 52 32 64 128 256), losses := [] }

theorem u31647 : Upper (D 6) (R 6) [10,36,192,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31648 : Route 9 := (fun mask => (mask,id))

def c31648 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31648 : Upper (D 6) (R 6) [10,36,192,272,65] 13 := by
  apply FastRouting.sound _ _ [10,36,192,272,65] 13 (by decide) (choices 1) [1,2,4] r31648 c31648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13892
  · exact u13893
  · exact u13894

def r31649 : Route 9 := (fun mask => (mask,id))

def c31649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31649 : Upper (D 6) (R 6) [10,36,192,272,66] 13 := by
  apply FastRouting.sound _ _ [10,36,192,272,66] 13 (by decide) (choices 1) [1,4] r31649 c31649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13895
  · exact u13896

def b31650 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 196 280 84 35 99 163 291), lower := (rows 11 38 196 280 84 32 64 128 256), losses := [] }

theorem u31650 : Upper (D 6) (R 6) [10,36,192,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31651 : Route 9 := (fun mask => (mask,id))

def c31651 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31651 : Upper (D 6) (R 6) [10,36,192,272,96] 13 := by
  apply FastRouting.sound _ _ [10,36,192,272,96] 13 (by decide) (choices 1) [1,2,4] r31651 c31651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13897
  · exact u13898
  · exact u13899

def b31652 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 38 196 296 19 117 85 213 341), lower := (rows 11 38 196 296 19 32 64 128 256), losses := [] }

theorem u31652 : Upper (D 6) (R 6) [10,36,192,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31653 : Route 9 := (fun mask => (mask,id))

def c31653 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31653 : Upper (D 6) (R 6) [10,36,192,288,5] 13 := by
  apply FastRouting.sound _ _ [10,36,192,288,5] 13 (by decide) (choices 1) [1,2,16,64] r31653 c31653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13900
  · exact u13901
  · exact u13902
  · exact u13903

def b31654 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 196 296 22 113 81 209 337), lower := (rows 11 38 196 296 22 32 64 128 256), losses := [] }

theorem u31654 : Upper (D 6) (R 6) [10,36,192,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31655 : Route 9 := (fun mask => (mask,id))

def c31655 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31655 : Upper (D 6) (R 6) [10,36,192,288,65] 13 := by
  apply FastRouting.sound _ _ [10,36,192,288,65] 13 (by decide) (choices 1) [1,2,4,16] r31655 c31655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13904
  · exact u13905
  · exact u13906
  · exact u13907

def r31656 : Route 9 := (fun mask => (mask,id))

def c31656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31656 : Upper (D 6) (R 6) [10,36,192,288,66] 13 := by
  apply FastRouting.sound _ _ [10,36,192,288,66] 13 (by decide) (choices 1) [1,4,16] r31656 c31656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13908
  · exact u13909
  · exact u13910

def b31657 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 196 296 84 51 83 147 275), lower := (rows 11 38 196 296 84 32 64 128 256), losses := [] }

theorem u31657 : Upper (D 6) (R 6) [10,36,192,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31658 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 196 328 19 53 117 181 309), lower := (rows 11 38 196 328 19 32 64 128 256), losses := [] }

theorem u31658 : Upper (D 6) (R 6) [10,36,192,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31659 : Route 9 := (fun mask => (mask,id))

def c31659 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31659 : Upper (D 6) (R 6) [10,36,192,320,5] 13 := by
  apply FastRouting.sound _ _ [10,36,192,320,5] 13 (by decide) (choices 1) [1,2,16] r31659 c31659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13911
  · exact u13912
  · exact u13913

def b31660 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 196 328 22 49 113 177 305), lower := (rows 11 38 196 328 22 32 64 128 256), losses := [] }

theorem u31660 : Upper (D 6) (R 6) [10,36,192,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31661 : Route 9 := (fun mask => (mask,id))

def c31661 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31661 : Upper (D 6) (R 6) [10,36,192,320,33] 13 := by
  apply FastRouting.sound _ _ [10,36,192,320,33] 13 (by decide) (choices 1) [1,2,4,16] r31661 c31661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13914
  · exact u13915
  · exact u13916
  · exact u13917

def b31662 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 196 328 50 53 85 149 277), lower := (rows 11 38 196 328 50 32 64 128 256), losses := [] }

theorem u31662 : Upper (D 6) (R 6) [10,36,192,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31663 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 196 328 52 51 83 147 275), lower := (rows 11 38 196 328 52 32 64 128 256), losses := [] }

theorem u31663 : Upper (D 6) (R 6) [10,36,192,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31664 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 388 25 19 100 100 228 356), lower := (rows 11 38 388 25 19 32 64 128 256), losses := [] }

theorem u31664 : Upper (D 6) (R 6) [10,36,384,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31665 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 388 25 21 98 98 226 354), lower := (rows 11 38 388 25 21 32 64 128 256), losses := [] }

theorem u31665 : Upper (D 6) (R 6) [10,36,384,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31666 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 388 25 22 97 97 225 353), lower := (rows 11 38 388 25 22 32 64 128 256), losses := [] }

theorem u31666 : Upper (D 6) (R 6) [10,36,384,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31667 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 388 25 49 102 70 198 326), lower := (rows 11 38 388 25 49 32 64 128 256), losses := [] }

theorem u31667 : Upper (D 6) (R 6) [10,36,384,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31668 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 388 25 50 101 69 197 325), lower := (rows 11 38 388 25 50 32 64 128 256), losses := [] }

theorem u31668 : Upper (D 6) (R 6) [10,36,384,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31669 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 388 25 52 99 67 195 323), lower := (rows 11 38 388 25 52 32 64 128 256), losses := [] }

theorem u31669 : Upper (D 6) (R 6) [10,36,384,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31670 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 38 388 25 81 102 102 230 358), lower := (rows 11 38 388 25 81 32 64 128 256), losses := [] }

theorem u31670 : Upper (D 6) (R 6) [10,36,384,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31671 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 388 25 82 101 101 229 357), lower := (rows 11 38 388 25 82 32 64 128 256), losses := [] }

theorem u31671 : Upper (D 6) (R 6) [10,36,384,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31672 : Route 9 := (fun mask => (mask,id))

def c31672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31672 : Upper (D 6) (R 6) [10,36,384,17,68] 13 := by
  apply FastRouting.sound _ _ [10,36,384,17,68] 13 (by decide) (choices 1) [1,2,64] r31672 c31672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13918
  · exact u13919
  · exact u13920

def r31673 : Route 9 := (fun mask => (mask,id))

def c31673 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31673 : Upper (D 6) (R 6) [10,36,384,17,96] 13 := by
  apply FastRouting.sound _ _ [10,36,384,17,96] 13 (by decide) (choices 1) [1,2,4,64] r31673 c31673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13921
  · exact u13922
  · exact u13923
  · exact u13924

def b31674 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 388 28 19 97 97 225 353), lower := (rows 11 38 388 28 19 32 64 128 256), losses := [] }

theorem u31674 : Upper (D 6) (R 6) [10,36,384,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31675 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 388 28 49 99 67 195 323), lower := (rows 11 38 388 28 49 32 64 128 256), losses := [] }

theorem u31675 : Upper (D 6) (R 6) [10,36,384,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31676 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 388 28 50 97 65 193 321), lower := (rows 11 38 388 28 50 32 64 128 256), losses := [] }

theorem u31676 : Upper (D 6) (R 6) [10,36,384,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31677 : Route 9 := (fun mask => (mask,id))

def c31677 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31677 : Upper (D 6) (R 6) [10,36,384,20,65] 13 := by
  apply FastRouting.sound _ _ [10,36,384,20,65] 13 (by decide) (choices 1) [1,2,64] r31677 c31677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13925
  · exact u13926
  · exact u13927

def r31678 : Route 9 := (fun mask => (mask,id))

def c31678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31678 : Upper (D 6) (R 6) [10,36,384,20,66] 13 := by
  apply FastRouting.sound _ _ [10,36,384,20,66] 13 (by decide) (choices 1) [1,64] r31678 c31678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13928
  · exact u13929

def r31679 : Route 9 := (fun mask => (mask,id))

def c31679 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31679 : Upper (D 6) (R 6) [10,36,384,20,96] 13 := by
  apply FastRouting.sound _ _ [10,36,384,20,96] 13 (by decide) (choices 1) [1,2,64] r31679 c31679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13930
  · exact u13931
  · exact u13932

#print axioms u31679
end Delivery.IrregularNine14.P06
