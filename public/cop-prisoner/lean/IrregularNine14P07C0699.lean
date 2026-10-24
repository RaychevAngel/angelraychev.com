import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0562
import IrregularNine14P07C0563
import IrregularNine14P07C0564
import IrregularNine14P07C0565
import IrregularNine14P07C0566

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41940 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 392 252 252 252 252 508), lower := (rows 35 67 7 392 16 32 64 128 256), losses := [] }

theorem u41940 : Upper (D 7) (R 7) [34,65,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41941 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 67 13 14 496 496 496 496 496), lower := (rows 35 67 13 14 16 32 64 128 256), losses := [] }

theorem u41941 : Upper (D 7) (R 7) [34,65,9,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41942 : Route 9 := (fun mask => (mask,id))

def c41942 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41942 : Upper (D 7) (R 7) [34,65,9,18] 13 := by
  apply FastRouting.sound _ _ [34,65,9,18] 13 (by decide) (choices 2) [36,68,96,132,160,192,260,288,320,384] r41942 c41942
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33761
  · exact u33762
  · exact u33763
  · exact u33764
  · exact u33765
  · exact u33766
  · exact u33767
  · exact u33768
  · exact u33769
  · exact u33770

def r41943 : Route 9 := (fun mask => (mask,id))

def c41943 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41943 : Upper (D 7) (R 7) [34,65,9,20] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41943 c41943
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33771
  · exact u33772
  · exact u33773
  · exact u33774
  · exact u33775
  · exact u33776
  · exact u33777
  · exact u33778
  · exact u33779
  · exact u33780

def b41944 : PairBound 9 := { available := 468, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 13 42 468 500 468 468 468), lower := (rows 35 67 13 42 16 32 64 128 256), losses := [] }

theorem u41944 : Upper (D 7) (R 7) [34,65,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41945 : PairBound 9 := { available := 466, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 67 13 44 466 498 466 466 466), lower := (rows 35 67 13 44 16 32 64 128 256), losses := [] }

theorem u41945 : Upper (D 7) (R 7) [34,65,9,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41946_6 : Upper (D 7) (R 7) [34,65,9,48,6] 13 :=
  permutation_upper _ _ _ [34,65,9,18,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33762

def r41946 : Route 9 := (fun mask => (mask,id))

def c41946 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41946 : Upper (D 7) (R 7) [34,65,9,48] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48] 13 (by decide) (choices 2) [6,66,68,130,132,192,258,260,320,384] r41946 c41946
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41946_6
  · exact u33792
  · exact u33793
  · exact u33794
  · exact u33795
  · exact u33796
  · exact u33797
  · exact u33798
  · exact u33799
  · exact u33800

def b41947 : PairBound 9 := { available := 436, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 74 436 436 500 436 436), lower := (rows 35 67 13 74 16 32 64 128 256), losses := [] }

theorem u41947 : Upper (D 7) (R 7) [34,65,9,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41948 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 76 434 434 498 434 434), lower := (rows 35 67 13 76 16 32 64 128 256), losses := [] }

theorem u41948 : Upper (D 7) (R 7) [34,65,9,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41949_6 : Upper (D 7) (R 7) [34,65,9,80,6] 13 :=
  permutation_upper _ _ _ [34,65,9,18,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33761

def r41949 : Route 9 := (fun mask => (mask,id))

def c41949 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 66 => 6 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41949 : Upper (D 7) (R 7) [34,65,9,80] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80] 13 (by decide) (choices 2) [6,34,36,130,132,160,258,260,288,384] r41949 c41949
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41949_6
  · exact u33812
  · exact u33813
  · exact u33814
  · exact u33815
  · exact u33816
  · exact u33817
  · exact u33818
  · exact u33819
  · exact u33820

def b41950 : PairBound 9 := { available := 406, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 35 67 13 104 406 438 470 406 406), lower := (rows 35 67 13 104 16 32 64 128 256), losses := [] }

theorem u41950 : Upper (D 7) (R 7) [34,65,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41951 : Route 9 := (fun mask => (mask,id))

def c41951 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41951 : Upper (D 7) (R 7) [34,65,9,130] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130] 13 (by decide) (choices 2) [36,68,96,132,160,192,260,288,320,384] r41951 c41951
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33826
  · exact u33827
  · exact u33828
  · exact u33829
  · exact u33830
  · exact u33831
  · exact u33832
  · exact u33833
  · exact u33834
  · exact u33835

def r41952 : Route 9 := (fun mask => (mask,id))

def c41952 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41952 : Upper (D 7) (R 7) [34,65,9,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41952 c41952
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33836
  · exact u33837
  · exact u33838
  · exact u33839
  · exact u33840
  · exact u33841
  · exact u33842
  · exact u33843
  · exact u33844
  · exact u33845

theorem m41953_6 : Upper (D 7) (R 7) [34,65,9,144,6] 13 :=
  permutation_upper _ _ _ [34,65,9,18,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33764

def r41953 : Route 9 := (fun mask => (mask,id))

def c41953 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41953 : Upper (D 7) (R 7) [34,65,9,144] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,258,260,288,320,384] r41953 c41953
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41953_6
  · exact u33846
  · exact u33847
  · exact u33848
  · exact u33849
  · exact u33850
  · exact u33851
  · exact u33852
  · exact u33853
  · exact u33854
  · exact u33855
  · exact u33856
  · exact u33857
  · exact u33858
  · exact u33859

theorem m41954_6 : Upper (D 7) (R 7) [34,65,9,160,6] 13 :=
  permutation_upper _ _ _ [34,65,9,18,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33766

def r41954 : Route 9 := (fun mask => (mask,id))

def c41954 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41954 : Upper (D 7) (R 7) [34,65,9,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160] 13 (by decide) (choices 2) [6,66,68,130,132,192,258,260,320,384] r41954 c41954
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41954_6
  · exact u33860
  · exact u33861
  · exact u33862
  · exact u33863
  · exact u33864
  · exact u33865
  · exact u33866
  · exact u33867
  · exact u33868

theorem m41955_6 : Upper (D 7) (R 7) [34,65,9,192,6] 13 :=
  permutation_upper _ _ _ [34,65,9,18,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33765

def r41955 : Route 9 := (fun mask => (mask,id))

def c41955 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 66 => 6 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41955 : Upper (D 7) (R 7) [34,65,9,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192] 13 (by decide) (choices 2) [6,34,36,130,132,160,258,260,288,384] r41955 c41955
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41955_6
  · exact u33869
  · exact u33870
  · exact u33871
  · exact u33872
  · exact u33873
  · exact u33874
  · exact u33875
  · exact u33876
  · exact u33877

def r41956 : Route 9 := (fun mask => (mask,id))

def c41956 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41956 : Upper (D 7) (R 7) [34,65,9,258] 13 := by
  apply FastRouting.sound _ _ [34,65,9,258] 13 (by decide) (choices 2) [36,68,96,132,160,192] r41956 c41956
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33878
  · exact u33879
  · exact u33880
  · exact u33881
  · exact u33882
  · exact u33883

def r41957 : Route 9 := (fun mask => (mask,id))

def c41957 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41957 : Upper (D 7) (R 7) [34,65,9,260] 13 := by
  apply FastRouting.sound _ _ [34,65,9,260] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41957 c41957
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33884
  · exact u33885
  · exact u33886
  · exact u33887
  · exact u33888
  · exact u33889

theorem m41958_6 : Upper (D 7) (R 7) [34,65,9,272,6] 13 :=
  permutation_upper _ _ _ [34,65,9,18,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33767

def r41958 : Route 9 := (fun mask => (mask,id))

def c41958 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 258 => 8 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41958 : Upper (D 7) (R 7) [34,65,9,272] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192] r41958 c41958
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41958_6
  · exact u33890
  · exact u33891
  · exact u33892
  · exact u33893
  · exact u33894
  · exact u33895
  · exact u33896
  · exact u33897
  · exact u33898

theorem m41959_6 : Upper (D 7) (R 7) [34,65,9,288,6] 13 :=
  permutation_upper _ _ _ [34,65,9,18,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33769

def r41959 : Route 9 := (fun mask => (mask,id))

def c41959 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41959 : Upper (D 7) (R 7) [34,65,9,288] 13 := by
  apply FastRouting.sound _ _ [34,65,9,288] 13 (by decide) (choices 2) [6,66,68,130,132,192] r41959 c41959
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41959_6
  · exact u33899
  · exact u33900
  · exact u33901
  · exact u33902
  · exact u33903

theorem m41960_6 : Upper (D 7) (R 7) [34,65,9,320,6] 13 :=
  permutation_upper _ _ _ [34,65,9,18,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33768

def r41960 : Route 9 := (fun mask => (mask,id))

def c41960 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41960 : Upper (D 7) (R 7) [34,65,9,320] 13 := by
  apply FastRouting.sound _ _ [34,65,9,320] 13 (by decide) (choices 2) [6,34,36,130,132,160] r41960 c41960
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41960_6
  · exact u33904
  · exact u33905
  · exact u33906
  · exact u33907
  · exact u33908

theorem m41961_6 : Upper (D 7) (R 7) [34,65,9,384,6] 13 :=
  permutation_upper _ _ _ [34,65,9,18,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33770

def r41961 : Route 9 := (fun mask => (mask,id))

def c41961 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 258 => 8 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41961 : Upper (D 7) (R 7) [34,65,9,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192] r41961 c41961
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41961_6
  · exact u33909
  · exact u33910
  · exact u33911
  · exact u33912
  · exact u33913
  · exact u33914
  · exact u33915
  · exact u33916
  · exact u33917

theorem m41962_10 : Upper (D 7) (R 7) [34,65,17,36,10] 13 :=
  permutation_upper _ _ _ [34,65,9,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33761

theorem m41962_66 : Upper (D 7) (R 7) [34,65,17,36,66] 13 :=
  permutation_upper _ _ _ [34,65,9,66,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33801

theorem m41962_72 : Upper (D 7) (R 7) [34,65,17,36,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33813

theorem m41962_130 : Upper (D 7) (R 7) [34,65,17,36,130] 13 :=
  permutation_upper _ _ _ [34,65,9,130,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33826

theorem m41962_136 : Upper (D 7) (R 7) [34,65,17,36,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33847

theorem m41962_192 : Upper (D 7) (R 7) [34,65,17,36,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33870

theorem m41962_258 : Upper (D 7) (R 7) [34,65,17,36,258] 13 :=
  permutation_upper _ _ _ [34,65,9,258,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33878

theorem m41962_264 : Upper (D 7) (R 7) [34,65,17,36,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33891

theorem m41962_320 : Upper (D 7) (R 7) [34,65,17,36,320] 13 :=
  permutation_upper _ _ _ [34,65,9,320,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33905

theorem m41962_384 : Upper (D 7) (R 7) [34,65,17,36,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33910

def r41962 : Route 9 := (fun mask => (mask,id))

def c41962 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41962 : Upper (D 7) (R 7) [34,65,17,36] 13 := by
  apply FastRouting.sound _ _ [34,65,17,36] 13 (by decide) (choices 2) [10,66,72,130,136,192,258,264,320,384] r41962 c41962
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41962_10
  · exact m41962_66
  · exact m41962_72
  · exact m41962_130
  · exact m41962_136
  · exact m41962_192
  · exact m41962_258
  · exact m41962_264
  · exact m41962_320
  · exact m41962_384

theorem m41963_10 : Upper (D 7) (R 7) [34,65,17,68,10] 13 :=
  permutation_upper _ _ _ [34,65,9,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33762

theorem m41963_34 : Upper (D 7) (R 7) [34,65,17,68,34] 13 :=
  permutation_upper _ _ _ [34,65,9,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33781

theorem m41963_40 : Upper (D 7) (R 7) [34,65,17,68,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33793

theorem m41963_130 : Upper (D 7) (R 7) [34,65,17,68,130] 13 :=
  permutation_upper _ _ _ [34,65,9,130,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33827

theorem m41963_136 : Upper (D 7) (R 7) [34,65,17,68,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33849

theorem m41963_160 : Upper (D 7) (R 7) [34,65,17,68,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33861

theorem m41963_258 : Upper (D 7) (R 7) [34,65,17,68,258] 13 :=
  permutation_upper _ _ _ [34,65,9,258,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33879

theorem m41963_264 : Upper (D 7) (R 7) [34,65,17,68,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33893

theorem m41963_288 : Upper (D 7) (R 7) [34,65,17,68,288] 13 :=
  permutation_upper _ _ _ [34,65,9,288,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33900

theorem m41963_384 : Upper (D 7) (R 7) [34,65,17,68,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33912

def r41963 : Route 9 := (fun mask => (mask,id))

def c41963 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41963 : Upper (D 7) (R 7) [34,65,17,68] 13 := by
  apply FastRouting.sound _ _ [34,65,17,68] 13 (by decide) (choices 2) [10,34,40,130,136,160,258,264,288,384] r41963 c41963
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41963_10
  · exact m41963_34
  · exact m41963_40
  · exact m41963_130
  · exact m41963_136
  · exact m41963_160
  · exact m41963_258
  · exact m41963_264
  · exact m41963_288
  · exact m41963_384

theorem m41964_6 : Upper (D 7) (R 7) [34,65,17,96,6] 13 :=
  permutation_upper _ _ _ [34,65,9,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33757

theorem m41964_10 : Upper (D 7) (R 7) [34,65,17,96,10] 13 :=
  permutation_upper _ _ _ [34,65,9,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33763

theorem m41964_12 : Upper (D 7) (R 7) [34,65,17,96,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33773

theorem m41964_130 : Upper (D 7) (R 7) [34,65,17,96,130] 13 :=
  permutation_upper _ _ _ [34,65,9,130,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33828

theorem m41964_132 : Upper (D 7) (R 7) [34,65,17,96,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33838

theorem m41964_136 : Upper (D 7) (R 7) [34,65,17,96,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33850

theorem m41964_258 : Upper (D 7) (R 7) [34,65,17,96,258] 13 :=
  permutation_upper _ _ _ [34,65,9,258,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33880

theorem m41964_260 : Upper (D 7) (R 7) [34,65,17,96,260] 13 :=
  permutation_upper _ _ _ [34,65,9,260,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33886

theorem m41964_264 : Upper (D 7) (R 7) [34,65,17,96,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33894

theorem m41964_384 : Upper (D 7) (R 7) [34,65,17,96,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33913

def r41964 : Route 9 := (fun mask => (mask,id))

def c41964 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41964 : Upper (D 7) (R 7) [34,65,17,96] 13 := by
  apply FastRouting.sound _ _ [34,65,17,96] 13 (by decide) (choices 2) [6,10,12,130,132,136,258,260,264,384] r41964 c41964
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41964_6
  · exact m41964_10
  · exact m41964_12
  · exact m41964_130
  · exact m41964_132
  · exact m41964_136
  · exact m41964_258
  · exact m41964_260
  · exact m41964_264
  · exact m41964_384

theorem m41965_12 : Upper (D 7) (R 7) [34,65,17,130,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33774

theorem m41965_36 : Upper (D 7) (R 7) [34,65,17,130,36] 13 :=
  permutation_upper _ _ _ [34,65,9,36,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33787

theorem m41965_40 : Upper (D 7) (R 7) [34,65,17,130,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33794

theorem m41965_68 : Upper (D 7) (R 7) [34,65,17,130,68] 13 :=
  permutation_upper _ _ _ [34,65,9,68,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33807

theorem m41965_72 : Upper (D 7) (R 7) [34,65,17,130,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33814

theorem m41965_96 : Upper (D 7) (R 7) [34,65,17,130,96] 13 :=
  permutation_upper _ _ _ [34,65,9,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33821

theorem m41965_132 : Upper (D 7) (R 7) [34,65,17,130,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33839

theorem m41965_136 : Upper (D 7) (R 7) [34,65,17,130,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33851

theorem m41965_160 : Upper (D 7) (R 7) [34,65,17,130,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33862

theorem m41965_192 : Upper (D 7) (R 7) [34,65,17,130,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33871

theorem m41965_260 : Upper (D 7) (R 7) [34,65,17,130,260] 13 :=
  permutation_upper _ _ _ [34,65,9,260,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33887

theorem m41965_264 : Upper (D 7) (R 7) [34,65,17,130,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33895

theorem m41965_288 : Upper (D 7) (R 7) [34,65,17,130,288] 13 :=
  permutation_upper _ _ _ [34,65,9,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33901

theorem m41965_320 : Upper (D 7) (R 7) [34,65,17,130,320] 13 :=
  permutation_upper _ _ _ [34,65,9,320,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33906

theorem m41965_384 : Upper (D 7) (R 7) [34,65,17,130,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33914

def r41965 : Route 9 := (fun mask => (mask,id))

def c41965 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u41965 : Upper (D 7) (R 7) [34,65,17,130] 13 := by
  apply FastRouting.sound _ _ [34,65,17,130] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192,260,264,288,320,384] r41965 c41965
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41965_12
  · exact m41965_36
  · exact m41965_40
  · exact m41965_68
  · exact m41965_72
  · exact m41965_96
  · exact m41965_132
  · exact m41965_136
  · exact m41965_160
  · exact m41965_192
  · exact m41965_260
  · exact m41965_264
  · exact m41965_288
  · exact m41965_320
  · exact m41965_384

theorem m41966_10 : Upper (D 7) (R 7) [34,65,17,132,10] 13 :=
  permutation_upper _ _ _ [34,65,9,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33764

theorem m41966_34 : Upper (D 7) (R 7) [34,65,17,132,34] 13 :=
  permutation_upper _ _ _ [34,65,9,34,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33782

theorem m41966_40 : Upper (D 7) (R 7) [34,65,17,132,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33795

theorem m41966_66 : Upper (D 7) (R 7) [34,65,17,132,66] 13 :=
  permutation_upper _ _ _ [34,65,9,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33802

theorem m41966_72 : Upper (D 7) (R 7) [34,65,17,132,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33815

theorem m41966_96 : Upper (D 7) (R 7) [34,65,17,132,96] 13 :=
  permutation_upper _ _ _ [34,65,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33822

theorem m41966_130 : Upper (D 7) (R 7) [34,65,17,132,130] 13 :=
  permutation_upper _ _ _ [34,65,9,130,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33829

theorem m41966_136 : Upper (D 7) (R 7) [34,65,17,132,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33852

theorem m41966_160 : Upper (D 7) (R 7) [34,65,17,132,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33863

theorem m41966_192 : Upper (D 7) (R 7) [34,65,17,132,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33872

theorem m41966_258 : Upper (D 7) (R 7) [34,65,17,132,258] 13 :=
  permutation_upper _ _ _ [34,65,9,258,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33881

theorem m41966_264 : Upper (D 7) (R 7) [34,65,17,132,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33896

theorem m41966_288 : Upper (D 7) (R 7) [34,65,17,132,288] 13 :=
  permutation_upper _ _ _ [34,65,9,288,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33902

theorem m41966_320 : Upper (D 7) (R 7) [34,65,17,132,320] 13 :=
  permutation_upper _ _ _ [34,65,9,320,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33907

theorem m41966_384 : Upper (D 7) (R 7) [34,65,17,132,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33915

def r41966 : Route 9 := (fun mask => (mask,id))

def c41966 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u41966 : Upper (D 7) (R 7) [34,65,17,132] 13 := by
  apply FastRouting.sound _ _ [34,65,17,132] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192,258,264,288,320,384] r41966 c41966
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41966_10
  · exact m41966_34
  · exact m41966_40
  · exact m41966_66
  · exact m41966_72
  · exact m41966_96
  · exact m41966_130
  · exact m41966_136
  · exact m41966_160
  · exact m41966_192
  · exact m41966_258
  · exact m41966_264
  · exact m41966_288
  · exact m41966_320
  · exact m41966_384

theorem m41967_6 : Upper (D 7) (R 7) [34,65,17,160,6] 13 :=
  permutation_upper _ _ _ [34,65,9,6,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33758

theorem m41967_10 : Upper (D 7) (R 7) [34,65,17,160,10] 13 :=
  permutation_upper _ _ _ [34,65,9,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33765

theorem m41967_12 : Upper (D 7) (R 7) [34,65,17,160,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33775

theorem m41967_66 : Upper (D 7) (R 7) [34,65,17,160,66] 13 :=
  permutation_upper _ _ _ [34,65,9,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33803

theorem m41967_68 : Upper (D 7) (R 7) [34,65,17,160,68] 13 :=
  permutation_upper _ _ _ [34,65,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33808

theorem m41967_72 : Upper (D 7) (R 7) [34,65,17,160,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33816

theorem m41967_130 : Upper (D 7) (R 7) [34,65,17,160,130] 13 :=
  permutation_upper _ _ _ [34,65,9,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33830

theorem m41967_132 : Upper (D 7) (R 7) [34,65,17,160,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33840

theorem m41967_136 : Upper (D 7) (R 7) [34,65,17,160,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33853

theorem m41967_192 : Upper (D 7) (R 7) [34,65,17,160,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33873

theorem m41967_258 : Upper (D 7) (R 7) [34,65,17,160,258] 13 :=
  permutation_upper _ _ _ [34,65,9,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33882

theorem m41967_260 : Upper (D 7) (R 7) [34,65,17,160,260] 13 :=
  permutation_upper _ _ _ [34,65,9,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33888

theorem m41967_264 : Upper (D 7) (R 7) [34,65,17,160,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33897

theorem m41967_320 : Upper (D 7) (R 7) [34,65,17,160,320] 13 :=
  permutation_upper _ _ _ [34,65,9,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33908

theorem m41967_384 : Upper (D 7) (R 7) [34,65,17,160,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33916

def r41967 : Route 9 := (fun mask => (mask,id))

def c41967 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 36 => 5 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41967 : Upper (D 7) (R 7) [34,65,17,160] 13 := by
  apply FastRouting.sound _ _ [34,65,17,160] 13 (by decide) (choices 2) [6,10,12,66,68,72,130,132,136,192,258,260,264,320,384] r41967 c41967
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41967_6
  · exact m41967_10
  · exact m41967_12
  · exact m41967_66
  · exact m41967_68
  · exact m41967_72
  · exact m41967_130
  · exact m41967_132
  · exact m41967_136
  · exact m41967_192
  · exact m41967_258
  · exact m41967_260
  · exact m41967_264
  · exact m41967_320
  · exact m41967_384

theorem m41968_6 : Upper (D 7) (R 7) [34,65,17,192,6] 13 :=
  permutation_upper _ _ _ [34,65,9,6,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33758

theorem m41968_10 : Upper (D 7) (R 7) [34,65,17,192,10] 13 :=
  permutation_upper _ _ _ [34,65,9,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33766

theorem m41968_12 : Upper (D 7) (R 7) [34,65,17,192,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33776

theorem m41968_34 : Upper (D 7) (R 7) [34,65,17,192,34] 13 :=
  permutation_upper _ _ _ [34,65,9,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33783

theorem m41968_36 : Upper (D 7) (R 7) [34,65,17,192,36] 13 :=
  permutation_upper _ _ _ [34,65,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33788

theorem m41968_40 : Upper (D 7) (R 7) [34,65,17,192,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33796

theorem m41968_130 : Upper (D 7) (R 7) [34,65,17,192,130] 13 :=
  permutation_upper _ _ _ [34,65,9,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33831

theorem m41968_132 : Upper (D 7) (R 7) [34,65,17,192,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33841

theorem m41968_136 : Upper (D 7) (R 7) [34,65,17,192,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33854

theorem m41968_160 : Upper (D 7) (R 7) [34,65,17,192,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33864

theorem m41968_258 : Upper (D 7) (R 7) [34,65,17,192,258] 13 :=
  permutation_upper _ _ _ [34,65,9,258,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33883

theorem m41968_260 : Upper (D 7) (R 7) [34,65,17,192,260] 13 :=
  permutation_upper _ _ _ [34,65,9,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33889

theorem m41968_264 : Upper (D 7) (R 7) [34,65,17,192,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33898

theorem m41968_288 : Upper (D 7) (R 7) [34,65,17,192,288] 13 :=
  permutation_upper _ _ _ [34,65,9,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33903

theorem m41968_384 : Upper (D 7) (R 7) [34,65,17,192,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33917

def r41968 : Route 9 := (fun mask => (mask,id))

def c41968 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41968 : Upper (D 7) (R 7) [34,65,17,192] 13 := by
  apply FastRouting.sound _ _ [34,65,17,192] 13 (by decide) (choices 2) [6,10,12,34,36,40,130,132,136,160,258,260,264,288,384] r41968 c41968
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41968_6
  · exact m41968_10
  · exact m41968_12
  · exact m41968_34
  · exact m41968_36
  · exact m41968_40
  · exact m41968_130
  · exact m41968_132
  · exact m41968_136
  · exact m41968_160
  · exact m41968_258
  · exact m41968_260
  · exact m41968_264
  · exact m41968_288
  · exact m41968_384

theorem m41969_12 : Upper (D 7) (R 7) [34,65,17,258,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33777

theorem m41969_36 : Upper (D 7) (R 7) [34,65,17,258,36] 13 :=
  permutation_upper _ _ _ [34,65,9,36,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33789

theorem m41969_40 : Upper (D 7) (R 7) [34,65,17,258,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33797

theorem m41969_68 : Upper (D 7) (R 7) [34,65,17,258,68] 13 :=
  permutation_upper _ _ _ [34,65,9,68,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33809

theorem m41969_72 : Upper (D 7) (R 7) [34,65,17,258,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33817

theorem m41969_96 : Upper (D 7) (R 7) [34,65,17,258,96] 13 :=
  permutation_upper _ _ _ [34,65,9,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33823

theorem m41969_132 : Upper (D 7) (R 7) [34,65,17,258,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33842

theorem m41969_136 : Upper (D 7) (R 7) [34,65,17,258,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33855

theorem m41969_160 : Upper (D 7) (R 7) [34,65,17,258,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33865

theorem m41969_192 : Upper (D 7) (R 7) [34,65,17,258,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33874

def r41969 : Route 9 := (fun mask => (mask,id))

def c41969 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41969 : Upper (D 7) (R 7) [34,65,17,258] 13 := by
  apply FastRouting.sound _ _ [34,65,17,258] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192] r41969 c41969
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41969_12
  · exact m41969_36
  · exact m41969_40
  · exact m41969_68
  · exact m41969_72
  · exact m41969_96
  · exact m41969_132
  · exact m41969_136
  · exact m41969_160
  · exact m41969_192

theorem m41970_10 : Upper (D 7) (R 7) [34,65,17,260,10] 13 :=
  permutation_upper _ _ _ [34,65,9,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33767

theorem m41970_34 : Upper (D 7) (R 7) [34,65,17,260,34] 13 :=
  permutation_upper _ _ _ [34,65,9,34,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33784

theorem m41970_40 : Upper (D 7) (R 7) [34,65,17,260,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33798

theorem m41970_66 : Upper (D 7) (R 7) [34,65,17,260,66] 13 :=
  permutation_upper _ _ _ [34,65,9,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33804

theorem m41970_72 : Upper (D 7) (R 7) [34,65,17,260,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33818

theorem m41970_96 : Upper (D 7) (R 7) [34,65,17,260,96] 13 :=
  permutation_upper _ _ _ [34,65,9,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33824

theorem m41970_130 : Upper (D 7) (R 7) [34,65,17,260,130] 13 :=
  permutation_upper _ _ _ [34,65,9,130,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33832

theorem m41970_136 : Upper (D 7) (R 7) [34,65,17,260,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33856

theorem m41970_160 : Upper (D 7) (R 7) [34,65,17,260,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33866

theorem m41970_192 : Upper (D 7) (R 7) [34,65,17,260,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33875

def r41970 : Route 9 := (fun mask => (mask,id))

def c41970 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41970 : Upper (D 7) (R 7) [34,65,17,260] 13 := by
  apply FastRouting.sound _ _ [34,65,17,260] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r41970 c41970
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41970_10
  · exact m41970_34
  · exact m41970_40
  · exact m41970_66
  · exact m41970_72
  · exact m41970_96
  · exact m41970_130
  · exact m41970_136
  · exact m41970_160
  · exact m41970_192

theorem m41971_6 : Upper (D 7) (R 7) [34,65,17,288,6] 13 :=
  permutation_upper _ _ _ [34,65,9,6,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33759

theorem m41971_10 : Upper (D 7) (R 7) [34,65,17,288,10] 13 :=
  permutation_upper _ _ _ [34,65,9,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33768

theorem m41971_12 : Upper (D 7) (R 7) [34,65,17,288,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33778

theorem m41971_66 : Upper (D 7) (R 7) [34,65,17,288,66] 13 :=
  permutation_upper _ _ _ [34,65,9,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33805

theorem m41971_68 : Upper (D 7) (R 7) [34,65,17,288,68] 13 :=
  permutation_upper _ _ _ [34,65,9,68,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33810

theorem m41971_72 : Upper (D 7) (R 7) [34,65,17,288,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33819

theorem m41971_130 : Upper (D 7) (R 7) [34,65,17,288,130] 13 :=
  permutation_upper _ _ _ [34,65,9,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33833

theorem m41971_132 : Upper (D 7) (R 7) [34,65,17,288,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33843

theorem m41971_136 : Upper (D 7) (R 7) [34,65,17,288,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33857

theorem m41971_192 : Upper (D 7) (R 7) [34,65,17,288,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33876

def r41971 : Route 9 := (fun mask => (mask,id))

def c41971 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41971 : Upper (D 7) (R 7) [34,65,17,288] 13 := by
  apply FastRouting.sound _ _ [34,65,17,288] 13 (by decide) (choices 2) [6,10,12,66,68,72,130,132,136,192] r41971 c41971
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41971_6
  · exact m41971_10
  · exact m41971_12
  · exact m41971_66
  · exact m41971_68
  · exact m41971_72
  · exact m41971_130
  · exact m41971_132
  · exact m41971_136
  · exact m41971_192

theorem m41972_6 : Upper (D 7) (R 7) [34,65,17,320,6] 13 :=
  permutation_upper _ _ _ [34,65,9,6,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33759

theorem m41972_10 : Upper (D 7) (R 7) [34,65,17,320,10] 13 :=
  permutation_upper _ _ _ [34,65,9,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33769

theorem m41972_12 : Upper (D 7) (R 7) [34,65,17,320,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33779

theorem m41972_34 : Upper (D 7) (R 7) [34,65,17,320,34] 13 :=
  permutation_upper _ _ _ [34,65,9,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33785

theorem m41972_36 : Upper (D 7) (R 7) [34,65,17,320,36] 13 :=
  permutation_upper _ _ _ [34,65,9,36,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33790

theorem m41972_40 : Upper (D 7) (R 7) [34,65,17,320,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33799

theorem m41972_130 : Upper (D 7) (R 7) [34,65,17,320,130] 13 :=
  permutation_upper _ _ _ [34,65,9,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33834

theorem m41972_132 : Upper (D 7) (R 7) [34,65,17,320,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33844

theorem m41972_136 : Upper (D 7) (R 7) [34,65,17,320,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33858

theorem m41972_160 : Upper (D 7) (R 7) [34,65,17,320,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33867

def r41972 : Route 9 := (fun mask => (mask,id))

def c41972 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41972 : Upper (D 7) (R 7) [34,65,17,320] 13 := by
  apply FastRouting.sound _ _ [34,65,17,320] 13 (by decide) (choices 2) [6,10,12,34,36,40,130,132,136,160] r41972 c41972
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41972_6
  · exact m41972_10
  · exact m41972_12
  · exact m41972_34
  · exact m41972_36
  · exact m41972_40
  · exact m41972_130
  · exact m41972_132
  · exact m41972_136
  · exact m41972_160

theorem m41973_6 : Upper (D 7) (R 7) [34,65,17,384,6] 13 :=
  permutation_upper _ _ _ [34,65,9,6,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33760

theorem m41973_10 : Upper (D 7) (R 7) [34,65,17,384,10] 13 :=
  permutation_upper _ _ _ [34,65,9,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33770

theorem m41973_12 : Upper (D 7) (R 7) [34,65,17,384,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33780

theorem m41973_34 : Upper (D 7) (R 7) [34,65,17,384,34] 13 :=
  permutation_upper _ _ _ [34,65,9,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33786

theorem m41973_36 : Upper (D 7) (R 7) [34,65,17,384,36] 13 :=
  permutation_upper _ _ _ [34,65,9,36,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33791

theorem m41973_40 : Upper (D 7) (R 7) [34,65,17,384,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33800

theorem m41973_66 : Upper (D 7) (R 7) [34,65,17,384,66] 13 :=
  permutation_upper _ _ _ [34,65,9,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33806

theorem m41973_68 : Upper (D 7) (R 7) [34,65,17,384,68] 13 :=
  permutation_upper _ _ _ [34,65,9,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33811

theorem m41973_72 : Upper (D 7) (R 7) [34,65,17,384,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33820

theorem m41973_96 : Upper (D 7) (R 7) [34,65,17,384,96] 13 :=
  permutation_upper _ _ _ [34,65,9,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33825

theorem m41973_130 : Upper (D 7) (R 7) [34,65,17,384,130] 13 :=
  permutation_upper _ _ _ [34,65,9,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33835

theorem m41973_132 : Upper (D 7) (R 7) [34,65,17,384,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33845

theorem m41973_136 : Upper (D 7) (R 7) [34,65,17,384,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33859

theorem m41973_160 : Upper (D 7) (R 7) [34,65,17,384,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33868

theorem m41973_192 : Upper (D 7) (R 7) [34,65,17,384,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33877

def r41973 : Route 9 := (fun mask => (mask,id))

def c41973 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41973 : Upper (D 7) (R 7) [34,65,17,384] 13 := by
  apply FastRouting.sound _ _ [34,65,17,384] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96,130,132,136,160,192] r41973 c41973
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41973_6
  · exact m41973_10
  · exact m41973_12
  · exact m41973_34
  · exact m41973_36
  · exact m41973_40
  · exact m41973_66
  · exact m41973_68
  · exact m41973_72
  · exact m41973_96
  · exact m41973_130
  · exact m41973_132
  · exact m41973_136
  · exact m41973_160
  · exact m41973_192

def b41974 : PairBound 9 := { available := 454, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 67 28 41 470 486 454 454 454), lower := (rows 35 67 28 41 16 32 64 128 256), losses := [] }

theorem u41974 : Upper (D 7) (R 7) [34,65,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41975 : PairBound 9 := { available := 453, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 67 28 42 469 485 453 453 453), lower := (rows 35 67 28 42 16 32 64 128 256), losses := [] }

theorem u41975 : Upper (D 7) (R 7) [34,65,24,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41976_3 : Upper (D 7) (R 7) [34,65,24,36,3] 13 :=
  permutation_upper _ _ _ [34,65,3,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33720

theorem m41976_65 : Upper (D 7) (R 7) [34,65,24,36,65] 13 :=
  permutation_upper _ _ _ [34,65,24,34,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33926

theorem m41976_66 : Upper (D 7) (R 7) [34,65,24,36,66] 13 :=
  permutation_upper _ _ _ [34,65,24,33,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33918

def r41976 : Route 9 := (fun mask => (mask,id))

def c41976 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41976 : Upper (D 7) (R 7) [34,65,24,36] 13 := by
  apply FastRouting.sound _ _ [34,65,24,36] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41976 c41976
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41976_3
  · exact m41976_65
  · exact m41976_66
  · exact u33934
  · exact u33935
  · exact u33936
  · exact u33937
  · exact u33938
  · exact u33939
  · exact u33940

theorem m41977_3 : Upper (D 7) (R 7) [34,65,24,96,3] 13 :=
  permutation_upper _ _ _ [34,65,3,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33721

theorem m41977_5 : Upper (D 7) (R 7) [34,65,24,96,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33773

theorem m41977_6 : Upper (D 7) (R 7) [34,65,24,96,6] 13 :=
  permutation_upper _ _ _ [34,65,9,20,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33773

theorem m41977_130 : Upper (D 7) (R 7) [34,65,24,96,130] 13 :=
  permutation_upper _ _ _ [34,65,24,96,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33941

theorem m41977_258 : Upper (D 7) (R 7) [34,65,24,96,258] 13 :=
  permutation_upper _ _ _ [34,65,24,96,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33943

def r41977 : Route 9 := (fun mask => (mask,id))

def c41977 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41977 : Upper (D 7) (R 7) [34,65,24,96] 13 := by
  apply FastRouting.sound _ _ [34,65,24,96] 13 (by decide) (choices 2) [3,5,6,129,130,132,257,258,260,384] r41977 c41977
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41977_3
  · exact m41977_5
  · exact m41977_6
  · exact u33941
  · exact m41977_130
  · exact u33942
  · exact u33943
  · exact m41977_258
  · exact u33944
  · exact u33945

theorem m41978_6 : Upper (D 7) (R 7) [34,65,24,129,6] 13 :=
  permutation_upper _ _ _ [34,65,9,20,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33774

theorem m41978_34 : Upper (D 7) (R 7) [34,65,24,129,34] 13 :=
  permutation_upper _ _ _ [34,65,24,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33927

theorem m41978_36 : Upper (D 7) (R 7) [34,65,24,129,36] 13 :=
  permutation_upper _ _ _ [34,65,24,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33934

theorem m41978_66 : Upper (D 7) (R 7) [34,65,24,129,66] 13 :=
  permutation_upper _ _ _ [34,65,24,33,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33919

theorem m41978_68 : Upper (D 7) (R 7) [34,65,24,129,68] 13 :=
  permutation_upper _ _ _ [34,65,24,36,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33935

theorem m41978_96 : Upper (D 7) (R 7) [34,65,24,129,96] 13 :=
  permutation_upper _ _ _ [34,65,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33941

def r41978 : Route 9 := (fun mask => (mask,id))

def c41978 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41978 : Upper (D 7) (R 7) [34,65,24,129] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,258,260,288,320,384] r41978 c41978
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41978_6
  · exact m41978_34
  · exact m41978_36
  · exact m41978_66
  · exact m41978_68
  · exact m41978_96
  · exact u33946
  · exact u33947
  · exact u33948
  · exact u33949
  · exact u33950
  · exact u33951
  · exact u33952
  · exact u33953
  · exact u33954

theorem m41979_3 : Upper (D 7) (R 7) [34,65,24,132,3] 13 :=
  permutation_upper _ _ _ [34,65,3,20,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33722

theorem m41979_33 : Upper (D 7) (R 7) [34,65,24,132,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33920

theorem m41979_34 : Upper (D 7) (R 7) [34,65,24,132,34] 13 :=
  permutation_upper _ _ _ [34,65,24,34,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33928

theorem m41979_65 : Upper (D 7) (R 7) [34,65,24,132,65] 13 :=
  permutation_upper _ _ _ [34,65,24,34,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33928

theorem m41979_66 : Upper (D 7) (R 7) [34,65,24,132,66] 13 :=
  permutation_upper _ _ _ [34,65,24,33,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33920

theorem m41979_96 : Upper (D 7) (R 7) [34,65,24,132,96] 13 :=
  permutation_upper _ _ _ [34,65,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33942

theorem m41979_129 : Upper (D 7) (R 7) [34,65,24,132,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33947

theorem m41979_130 : Upper (D 7) (R 7) [34,65,24,132,130] 13 :=
  permutation_upper _ _ _ [34,65,24,129,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33947

theorem m41979_192 : Upper (D 7) (R 7) [34,65,24,132,192] 13 :=
  permutation_upper _ _ _ [34,65,24,132,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33955

theorem m41979_258 : Upper (D 7) (R 7) [34,65,24,132,258] 13 :=
  permutation_upper _ _ _ [34,65,24,132,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33956

theorem m41979_320 : Upper (D 7) (R 7) [34,65,24,132,320] 13 :=
  permutation_upper _ _ _ [34,65,24,132,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33957

def r41979 : Route 9 := (fun mask => (mask,id))

def c41979 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41979 : Upper (D 7) (R 7) [34,65,24,132] 13 := by
  apply FastRouting.sound _ _ [34,65,24,132] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r41979 c41979
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41979_3
  · exact m41979_33
  · exact m41979_34
  · exact m41979_65
  · exact m41979_66
  · exact m41979_96
  · exact m41979_129
  · exact m41979_130
  · exact u33955
  · exact m41979_192
  · exact u33956
  · exact m41979_258
  · exact u33957
  · exact m41979_320
  · exact u33958

theorem m41980_3 : Upper (D 7) (R 7) [34,65,24,160,3] 13 :=
  permutation_upper _ _ _ [34,65,3,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33723

theorem m41980_5 : Upper (D 7) (R 7) [34,65,24,160,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33775

theorem m41980_6 : Upper (D 7) (R 7) [34,65,24,160,6] 13 :=
  permutation_upper _ _ _ [34,65,9,20,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33776

theorem m41980_65 : Upper (D 7) (R 7) [34,65,24,160,65] 13 :=
  permutation_upper _ _ _ [34,65,24,34,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33929

theorem m41980_66 : Upper (D 7) (R 7) [34,65,24,160,66] 13 :=
  permutation_upper _ _ _ [34,65,24,33,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33921

theorem m41980_68 : Upper (D 7) (R 7) [34,65,24,160,68] 13 :=
  permutation_upper _ _ _ [34,65,24,36,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33936

theorem m41980_129 : Upper (D 7) (R 7) [34,65,24,160,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33948

theorem m41980_130 : Upper (D 7) (R 7) [34,65,24,160,130] 13 :=
  permutation_upper _ _ _ [34,65,24,129,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33949

theorem m41980_132 : Upper (D 7) (R 7) [34,65,24,160,132] 13 :=
  permutation_upper _ _ _ [34,65,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33955

def r41980 : Route 9 := (fun mask => (mask,id))

def c41980 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41980 : Upper (D 7) (R 7) [34,65,24,160] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,257,258,260,320,384] r41980 c41980
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41980_3
  · exact m41980_5
  · exact m41980_6
  · exact m41980_65
  · exact m41980_66
  · exact m41980_68
  · exact m41980_129
  · exact m41980_130
  · exact m41980_132
  · exact u33959
  · exact u33960
  · exact u33961
  · exact u33962
  · exact u33963
  · exact u33964

theorem m41981_6 : Upper (D 7) (R 7) [34,65,24,257,6] 13 :=
  permutation_upper _ _ _ [34,65,9,20,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33777

theorem m41981_34 : Upper (D 7) (R 7) [34,65,24,257,34] 13 :=
  permutation_upper _ _ _ [34,65,24,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33930

theorem m41981_36 : Upper (D 7) (R 7) [34,65,24,257,36] 13 :=
  permutation_upper _ _ _ [34,65,24,36,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33937

theorem m41981_66 : Upper (D 7) (R 7) [34,65,24,257,66] 13 :=
  permutation_upper _ _ _ [34,65,24,33,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33922

theorem m41981_68 : Upper (D 7) (R 7) [34,65,24,257,68] 13 :=
  permutation_upper _ _ _ [34,65,24,36,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33938

theorem m41981_96 : Upper (D 7) (R 7) [34,65,24,257,96] 13 :=
  permutation_upper _ _ _ [34,65,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33943

theorem m41981_130 : Upper (D 7) (R 7) [34,65,24,257,130] 13 :=
  permutation_upper _ _ _ [34,65,24,129,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33950

theorem m41981_132 : Upper (D 7) (R 7) [34,65,24,257,132] 13 :=
  permutation_upper _ _ _ [34,65,24,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33956

theorem m41981_160 : Upper (D 7) (R 7) [34,65,24,257,160] 13 :=
  permutation_upper _ _ _ [34,65,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33960

theorem m41981_192 : Upper (D 7) (R 7) [34,65,24,257,192] 13 :=
  permutation_upper _ _ _ [34,65,24,160,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33961

def r41981 : Route 9 := (fun mask => (mask,id))

def c41981 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 258 => 8 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41981 : Upper (D 7) (R 7) [34,65,24,257] 13 := by
  apply FastRouting.sound _ _ [34,65,24,257] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192] r41981 c41981
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41981_6
  · exact m41981_34
  · exact m41981_36
  · exact m41981_66
  · exact m41981_68
  · exact m41981_96
  · exact m41981_130
  · exact m41981_132
  · exact m41981_160
  · exact m41981_192

theorem m41982_3 : Upper (D 7) (R 7) [34,65,24,260,3] 13 :=
  permutation_upper _ _ _ [34,65,3,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33724

theorem m41982_33 : Upper (D 7) (R 7) [34,65,24,260,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33923

theorem m41982_34 : Upper (D 7) (R 7) [34,65,24,260,34] 13 :=
  permutation_upper _ _ _ [34,65,24,34,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33931

theorem m41982_65 : Upper (D 7) (R 7) [34,65,24,260,65] 13 :=
  permutation_upper _ _ _ [34,65,24,34,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33931

theorem m41982_66 : Upper (D 7) (R 7) [34,65,24,260,66] 13 :=
  permutation_upper _ _ _ [34,65,24,33,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33923

theorem m41982_96 : Upper (D 7) (R 7) [34,65,24,260,96] 13 :=
  permutation_upper _ _ _ [34,65,24,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33944

theorem m41982_129 : Upper (D 7) (R 7) [34,65,24,260,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33951

theorem m41982_130 : Upper (D 7) (R 7) [34,65,24,260,130] 13 :=
  permutation_upper _ _ _ [34,65,24,129,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33951

theorem m41982_160 : Upper (D 7) (R 7) [34,65,24,260,160] 13 :=
  permutation_upper _ _ _ [34,65,24,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33962

theorem m41982_192 : Upper (D 7) (R 7) [34,65,24,260,192] 13 :=
  permutation_upper _ _ _ [34,65,24,160,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33962

def r41982 : Route 9 := (fun mask => (mask,id))

def c41982 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41982 : Upper (D 7) (R 7) [34,65,24,260] 13 := by
  apply FastRouting.sound _ _ [34,65,24,260] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41982 c41982
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41982_3
  · exact m41982_33
  · exact m41982_34
  · exact m41982_65
  · exact m41982_66
  · exact m41982_96
  · exact m41982_129
  · exact m41982_130
  · exact m41982_160
  · exact m41982_192

theorem m41983_3 : Upper (D 7) (R 7) [34,65,24,288,3] 13 :=
  permutation_upper _ _ _ [34,65,3,20,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33725

theorem m41983_5 : Upper (D 7) (R 7) [34,65,24,288,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33778

theorem m41983_6 : Upper (D 7) (R 7) [34,65,24,288,6] 13 :=
  permutation_upper _ _ _ [34,65,9,20,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33779

theorem m41983_65 : Upper (D 7) (R 7) [34,65,24,288,65] 13 :=
  permutation_upper _ _ _ [34,65,24,34,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33932

theorem m41983_66 : Upper (D 7) (R 7) [34,65,24,288,66] 13 :=
  permutation_upper _ _ _ [34,65,24,33,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33924

theorem m41983_68 : Upper (D 7) (R 7) [34,65,24,288,68] 13 :=
  permutation_upper _ _ _ [34,65,24,36,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33939

theorem m41983_129 : Upper (D 7) (R 7) [34,65,24,288,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33952

theorem m41983_130 : Upper (D 7) (R 7) [34,65,24,288,130] 13 :=
  permutation_upper _ _ _ [34,65,24,129,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33953

theorem m41983_132 : Upper (D 7) (R 7) [34,65,24,288,132] 13 :=
  permutation_upper _ _ _ [34,65,24,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33957

theorem m41983_192 : Upper (D 7) (R 7) [34,65,24,288,192] 13 :=
  permutation_upper _ _ _ [34,65,24,160,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33963

def r41983 : Route 9 := (fun mask => (mask,id))

def c41983 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 257 => 8 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41983 : Upper (D 7) (R 7) [34,65,24,288] 13 := by
  apply FastRouting.sound _ _ [34,65,24,288] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r41983 c41983
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41983_3
  · exact m41983_5
  · exact m41983_6
  · exact m41983_65
  · exact m41983_66
  · exact m41983_68
  · exact m41983_129
  · exact m41983_130
  · exact m41983_132
  · exact m41983_192

theorem m41984_3 : Upper (D 7) (R 7) [34,65,24,384,3] 13 :=
  permutation_upper _ _ _ [34,65,3,20,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33726

theorem m41984_5 : Upper (D 7) (R 7) [34,65,24,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33780

theorem m41984_6 : Upper (D 7) (R 7) [34,65,24,384,6] 13 :=
  permutation_upper _ _ _ [34,65,9,20,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33780

theorem m41984_33 : Upper (D 7) (R 7) [34,65,24,384,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33925

theorem m41984_34 : Upper (D 7) (R 7) [34,65,24,384,34] 13 :=
  permutation_upper _ _ _ [34,65,24,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33933

theorem m41984_36 : Upper (D 7) (R 7) [34,65,24,384,36] 13 :=
  permutation_upper _ _ _ [34,65,24,36,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33940

theorem m41984_65 : Upper (D 7) (R 7) [34,65,24,384,65] 13 :=
  permutation_upper _ _ _ [34,65,24,34,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33933

theorem m41984_66 : Upper (D 7) (R 7) [34,65,24,384,66] 13 :=
  permutation_upper _ _ _ [34,65,24,33,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33925

theorem m41984_68 : Upper (D 7) (R 7) [34,65,24,384,68] 13 :=
  permutation_upper _ _ _ [34,65,24,36,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33940

theorem m41984_96 : Upper (D 7) (R 7) [34,65,24,384,96] 13 :=
  permutation_upper _ _ _ [34,65,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33945

theorem m41984_129 : Upper (D 7) (R 7) [34,65,24,384,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33954

theorem m41984_130 : Upper (D 7) (R 7) [34,65,24,384,130] 13 :=
  permutation_upper _ _ _ [34,65,24,129,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33954

theorem m41984_132 : Upper (D 7) (R 7) [34,65,24,384,132] 13 :=
  permutation_upper _ _ _ [34,65,24,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33958

theorem m41984_160 : Upper (D 7) (R 7) [34,65,24,384,160] 13 :=
  permutation_upper _ _ _ [34,65,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33964

theorem m41984_192 : Upper (D 7) (R 7) [34,65,24,384,192] 13 :=
  permutation_upper _ _ _ [34,65,24,160,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33964

def r41984 : Route 9 := (fun mask => (mask,id))

def c41984 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41984 : Upper (D 7) (R 7) [34,65,24,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192] r41984 c41984
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41984_3
  · exact m41984_5
  · exact m41984_6
  · exact m41984_33
  · exact m41984_34
  · exact m41984_36
  · exact m41984_65
  · exact m41984_66
  · exact m41984_68
  · exact m41984_96
  · exact m41984_129
  · exact m41984_130
  · exact m41984_132
  · exact m41984_160
  · exact m41984_192

def b41985 : PairBound 9 := { available := 410, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 76 410 442 474 410 410), lower := (rows 35 67 37 76 16 32 64 128 256), losses := [] }

theorem u41985 : Upper (D 7) (R 7) [34,65,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41986 : PairBound 9 := { available := 476, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 138 476 508 476 476 476), lower := (rows 35 67 37 138 16 32 64 128 256), losses := [] }

theorem u41986 : Upper (D 7) (R 7) [34,65,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41987 : PairBound 9 := { available := 474, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 140 474 506 474 474 474), lower := (rows 35 67 37 140 16 32 64 128 256), losses := [] }

theorem u41987 : Upper (D 7) (R 7) [34,65,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41988 : PairBound 9 := { available := 414, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 200 414 446 478 414 414), lower := (rows 35 67 37 200 16 32 64 128 256), losses := [] }

theorem u41988 : Upper (D 7) (R 7) [34,65,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41989 : PairBound 9 := { available := 220, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 266 220 252 220 220 476), lower := (rows 35 67 37 266 16 32 64 128 256), losses := [] }

theorem u41989 : Upper (D 7) (R 7) [34,65,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41990 : PairBound 9 := { available := 218, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 268 218 250 218 218 474), lower := (rows 35 67 37 268 16 32 64 128 256), losses := [] }

theorem u41990 : Upper (D 7) (R 7) [34,65,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41991 : PairBound 9 := { available := 158, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 328 158 190 222 158 414), lower := (rows 35 67 37 328 16 32 64 128 256), losses := [] }

theorem u41991 : Upper (D 7) (R 7) [34,65,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41992 : PairBound 9 := { available := 222, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 67 37 392 222 254 222 222 478), lower := (rows 35 67 37 392 16 32 64 128 256), losses := [] }

theorem u41992 : Upper (D 7) (R 7) [34,65,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41993 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 76 409 441 473 409 409), lower := (rows 35 67 38 76 16 32 64 128 256), losses := [] }

theorem u41993 : Upper (D 7) (R 7) [34,65,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41994 : PairBound 9 := { available := 476, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 137 476 508 476 476 476), lower := (rows 35 67 38 137 16 32 64 128 256), losses := [] }

theorem u41994 : Upper (D 7) (R 7) [34,65,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41995 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 140 473 505 473 473 473), lower := (rows 35 67 38 140 16 32 64 128 256), losses := [] }

theorem u41995 : Upper (D 7) (R 7) [34,65,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41996 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 200 413 445 477 413 413), lower := (rows 35 67 38 200 16 32 64 128 256), losses := [] }

theorem u41996 : Upper (D 7) (R 7) [34,65,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41997 : PairBound 9 := { available := 220, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 265 220 252 220 220 476), lower := (rows 35 67 38 265 16 32 64 128 256), losses := [] }

theorem u41997 : Upper (D 7) (R 7) [34,65,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41998 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 268 217 249 217 217 473), lower := (rows 35 67 38 268 16 32 64 128 256), losses := [] }

theorem u41998 : Upper (D 7) (R 7) [34,65,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41999 : PairBound 9 := { available := 157, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 328 157 189 221 157 413), lower := (rows 35 67 38 328 16 32 64 128 256), losses := [] }

theorem u41999 : Upper (D 7) (R 7) [34,65,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u41999
end Delivery.IrregularNine14.P07
