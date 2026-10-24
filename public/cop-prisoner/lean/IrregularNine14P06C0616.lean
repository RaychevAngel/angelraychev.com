import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0360
import IrregularNine14P06C0361
import IrregularNine14P06C0362
import IrregularNine14P06C0363

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36960 : Route 9 := (fun mask => (mask,id))

def c36960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36960 : Upper (D 6) (R 6) [34,129,40,18,260] 13 := by
  apply FastRouting.sound _ _ [34,129,40,18,260] 13 (by decide) (choices 1) [1,4,64] r36960 c36960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21643
  · exact u21644
  · exact u21645

def r36961 : Route 9 := (fun mask => (mask,id))

def c36961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36961 : Upper (D 6) (R 6) [34,129,40,18,320] 13 := by
  apply FastRouting.sound _ _ [34,129,40,18,320] 13 (by decide) (choices 1) [1,4,64] r36961 c36961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21646
  · exact u21647
  · exact u21648

def b36962 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 28 19 356 324 452 324), lower := (rows 35 131 44 28 19 32 64 128 256), losses := [] }

theorem u36962 : Upper (D 6) (R 6) [34,129,40,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36963 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 28, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 131 44 28 21 354 322 450 322), lower := (rows 35 131 44 28 21 32 64 128 256), losses := [] }

theorem u36963 : Upper (D 6) (R 6) [34,129,40,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36964 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 44 28 22 353 321 449 321), lower := (rows 35 131 44 28 22 32 64 128 256), losses := [] }

theorem u36964 : Upper (D 6) (R 6) [34,129,40,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36965 : Route 9 := (fun mask => (mask,id))

def c36965 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36965 : Upper (D 6) (R 6) [34,129,40,20,65] 13 := by
  apply FastRouting.sound _ _ [34,129,40,20,65] 13 (by decide) (choices 1) [2,4,64,256] r36965 c36965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21649
  · exact u21650
  · exact u21651
  · exact u21652

def r36966 : Route 9 := (fun mask => (mask,id))

def c36966 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36966 : Upper (D 6) (R 6) [34,129,40,20,66] 13 := by
  apply FastRouting.sound _ _ [34,129,40,20,66] 13 (by decide) (choices 1) [1,4,64,256] r36966 c36966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21653
  · exact u21654
  · exact u21655
  · exact u21656

def b36967 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 44 28 84 355 323 451 323), lower := (rows 35 131 44 28 84 32 64 128 256), losses := [] }

theorem u36967 : Upper (D 6) (R 6) [34,129,40,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36968 : Route 9 := (fun mask => (mask,id))

def c36968 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36968 : Upper (D 6) (R 6) [34,129,40,20,257] 13 := by
  apply FastRouting.sound _ _ [34,129,40,20,257] 13 (by decide) (choices 1) [2,4,64] r36968 c36968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21657
  · exact u21658
  · exact u21659

def r36969 : Route 9 := (fun mask => (mask,id))

def c36969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36969 : Upper (D 6) (R 6) [34,129,40,20,258] 13 := by
  apply FastRouting.sound _ _ [34,129,40,20,258] 13 (by decide) (choices 1) [1,4,64] r36969 c36969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21660
  · exact u21661
  · exact u21662

def b36970 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 44 28 276 99 67 195 323), lower := (rows 35 131 44 28 276 32 64 128 256), losses := [] }

theorem u36970 : Upper (D 6) (R 6) [34,129,40,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36971 : Route 9 := (fun mask => (mask,id))

def c36971 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36971 : Upper (D 6) (R 6) [34,129,40,20,320] 13 := by
  apply FastRouting.sound _ _ [34,129,40,20,320] 13 (by decide) (choices 1) [1,2,4,64] r36971 c36971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21663
  · exact u21664
  · exact u21665
  · exact u21666

def r36972 : Route 9 := (fun mask => (mask,id))

def c36972 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u36972 : Upper (D 6) (R 6) [34,129,40,65,6] 13 := by
  apply FastRouting.sound _ _ [34,129,40,65,6] 13 (by decide) (choices 1) [4,16,64,256] r36972 c36972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21667
  · exact u21668
  · exact u21669
  · exact u21670

def r36973 : Route 9 := (fun mask => (mask,id))

def c36973 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36973 : Upper (D 6) (R 6) [34,129,40,65,66] 13 := by
  apply FastRouting.sound _ _ [34,129,40,65,66] 13 (by decide) (choices 1) [4,16,256] r36973 c36973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21671
  · exact u21672
  · exact u21673

def r36974 : Route 9 := (fun mask => (mask,id))

def c36974 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36974 : Upper (D 6) (R 6) [34,129,40,65,68] 13 := by
  apply FastRouting.sound _ _ [34,129,40,65,68] 13 (by decide) (choices 1) [2,4,16,256] r36974 c36974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21674
  · exact u21675
  · exact u21676
  · exact u21677

def r36975 : Route 9 := (fun mask => (mask,id))

def c36975 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36975 : Upper (D 6) (R 6) [34,129,40,65,258] 13 := by
  apply FastRouting.sound _ _ [34,129,40,65,258] 13 (by decide) (choices 1) [4,16,64] r36975 c36975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21678
  · exact u21679
  · exact u21680

def r36976 : Route 9 := (fun mask => (mask,id))

def c36976 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36976 : Upper (D 6) (R 6) [34,129,40,65,260] 13 := by
  apply FastRouting.sound _ _ [34,129,40,65,260] 13 (by decide) (choices 1) [2,4,16,64] r36976 c36976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21681
  · exact u21682
  · exact u21683
  · exact u21684

def r36977 : Route 9 := (fun mask => (mask,id))

def c36977 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36977 : Upper (D 6) (R 6) [34,129,40,65,320] 13 := by
  apply FastRouting.sound _ _ [34,129,40,65,320] 13 (by decide) (choices 1) [2,4,16] r36977 c36977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21685
  · exact u21686
  · exact u21687

def r36978 : Route 9 := (fun mask => (mask,id))

def c36978 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u36978 : Upper (D 6) (R 6) [34,129,40,66,5] 13 := by
  apply FastRouting.sound _ _ [34,129,40,66,5] 13 (by decide) (choices 1) [4,16,64,256] r36978 c36978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21688
  · exact u21689
  · exact u21690
  · exact u21691

def r36979 : Route 9 := (fun mask => (mask,id))

def c36979 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36979 : Upper (D 6) (R 6) [34,129,40,66,65] 13 := by
  apply FastRouting.sound _ _ [34,129,40,66,65] 13 (by decide) (choices 1) [4,16,256] r36979 c36979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21692
  · exact u21693
  · exact u21694

def r36980 : Route 9 := (fun mask => (mask,id))

def c36980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36980 : Upper (D 6) (R 6) [34,129,40,66,68] 13 := by
  apply FastRouting.sound _ _ [34,129,40,66,68] 13 (by decide) (choices 1) [1,4,16,256] r36980 c36980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21695
  · exact u21696
  · exact u21697
  · exact u21698

def r36981 : Route 9 := (fun mask => (mask,id))

def c36981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36981 : Upper (D 6) (R 6) [34,129,40,66,257] 13 := by
  apply FastRouting.sound _ _ [34,129,40,66,257] 13 (by decide) (choices 1) [4,16,64] r36981 c36981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21699
  · exact u21700
  · exact u21701

def r36982 : Route 9 := (fun mask => (mask,id))

def c36982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36982 : Upper (D 6) (R 6) [34,129,40,66,260] 13 := by
  apply FastRouting.sound _ _ [34,129,40,66,260] 13 (by decide) (choices 1) [1,4,16,64] r36982 c36982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21702
  · exact u21703
  · exact u21704
  · exact u21705

def r36983 : Route 9 := (fun mask => (mask,id))

def c36983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36983 : Upper (D 6) (R 6) [34,129,40,66,320] 13 := by
  apply FastRouting.sound _ _ [34,129,40,66,320] 13 (by decide) (choices 1) [1,4,16] r36983 c36983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21706
  · exact u21707
  · exact u21708

def b36984 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 76 19 372 340 468 340), lower := (rows 35 131 44 76 19 32 64 128 256), losses := [] }

theorem u36984 : Upper (D 6) (R 6) [34,129,40,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36985 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 483, targets := 4 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 131 44 76 21 370 338 466 338), lower := (rows 35 131 44 76 21 32 64 128 256), losses := [] }

theorem u36985 : Upper (D 6) (R 6) [34,129,40,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36986 : Route 9 := (fun mask => (mask,id))

def c36986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u36986 : Upper (D 6) (R 6) [34,129,40,68,6] 13 := by
  apply FastRouting.sound _ _ [34,129,40,68,6] 13 (by decide) (choices 1) [1,16,64,256] r36986 c36986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21709
  · exact u21710
  · exact u21711
  · exact u21712

def r36987 : Route 9 := (fun mask => (mask,id))

def c36987 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36987 : Upper (D 6) (R 6) [34,129,40,68,65] 13 := by
  apply FastRouting.sound _ _ [34,129,40,68,65] 13 (by decide) (choices 1) [2,4,16,256] r36987 c36987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21713
  · exact u21714
  · exact u21715
  · exact u21716

def r36988 : Route 9 := (fun mask => (mask,id))

def c36988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36988 : Upper (D 6) (R 6) [34,129,40,68,66] 13 := by
  apply FastRouting.sound _ _ [34,129,40,68,66] 13 (by decide) (choices 1) [1,4,16,256] r36988 c36988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21717
  · exact u21718
  · exact u21719
  · exact u21720

def b36989 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 44 76 84 307 339 403 275), lower := (rows 35 131 44 76 84 32 64 128 256), losses := [] }

theorem u36989 : Upper (D 6) (R 6) [34,129,40,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36990 : Route 9 := (fun mask => (mask,id))

def c36990 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36990 : Upper (D 6) (R 6) [34,129,40,68,257] 13 := by
  apply FastRouting.sound _ _ [34,129,40,68,257] 13 (by decide) (choices 1) [2,4,16,64] r36990 c36990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21721
  · exact u21722
  · exact u21723
  · exact u21724

def r36991 : Route 9 := (fun mask => (mask,id))

def c36991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36991 : Upper (D 6) (R 6) [34,129,40,68,258] 13 := by
  apply FastRouting.sound _ _ [34,129,40,68,258] 13 (by decide) (choices 1) [1,4,16,64] r36991 c36991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21725
  · exact u21726
  · exact u21727
  · exact u21728

def r36992 : Route 9 := (fun mask => (mask,id))

def c36992 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36992 : Upper (D 6) (R 6) [34,129,40,68,260] 13 := by
  apply FastRouting.sound _ _ [34,129,40,68,260] 13 (by decide) (choices 1) [1,2,16,64] r36992 c36992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21729
  · exact u21730
  · exact u21731
  · exact u21732

def r36993 : Route 9 := (fun mask => (mask,id))

def c36993 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36993 : Upper (D 6) (R 6) [34,129,40,68,320] 13 := by
  apply FastRouting.sound _ _ [34,129,40,68,320] 13 (by decide) (choices 1) [1,2,4,16] r36993 c36993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21733
  · exact u21734
  · exact u21735
  · exact u21736

def b36994 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 88 19 356 324 452 324), lower := (rows 35 131 44 88 19 32 64 128 256), losses := [] }

theorem u36994 : Upper (D 6) (R 6) [34,129,40,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36995 : Route 9 := (fun mask => (mask,id))

def c36995 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36995 : Upper (D 6) (R 6) [34,129,40,80,5] 13 := by
  apply FastRouting.sound _ _ [34,129,40,80,5] 13 (by decide) (choices 1) [2,4,64,256] r36995 c36995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21737
  · exact u21738
  · exact u21739
  · exact u21740

def r36996 : Route 9 := (fun mask => (mask,id))

def c36996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36996 : Upper (D 6) (R 6) [34,129,40,80,6] 13 := by
  apply FastRouting.sound _ _ [34,129,40,80,6] 13 (by decide) (choices 1) [1,4,64,256] r36996 c36996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21741
  · exact u21742
  · exact u21743
  · exact u21744

def b36997 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 44 88 81 294 326 390 262), lower := (rows 35 131 44 88 81 32 64 128 256), losses := [] }

theorem u36997 : Upper (D 6) (R 6) [34,129,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36998 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 44 88 82 293 325 389 261), lower := (rows 35 131 44 88 82 32 64 128 256), losses := [] }

theorem u36998 : Upper (D 6) (R 6) [34,129,40,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36999 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 44 88 84 295 327 391 263), lower := (rows 35 131 44 88 84 32 64 128 256), losses := [] }

theorem u36999 : Upper (D 6) (R 6) [34,129,40,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37000 : Route 9 := (fun mask => (mask,id))

def c37000 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37000 : Upper (D 6) (R 6) [34,129,40,80,257] 13 := by
  apply FastRouting.sound _ _ [34,129,40,80,257] 13 (by decide) (choices 1) [2,4,64] r37000 c37000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21745
  · exact u21746
  · exact u21747

def r37001 : Route 9 := (fun mask => (mask,id))

def c37001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37001 : Upper (D 6) (R 6) [34,129,40,80,258] 13 := by
  apply FastRouting.sound _ _ [34,129,40,80,258] 13 (by decide) (choices 1) [1,4,64] r37001 c37001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21748
  · exact u21749
  · exact u21750

def r37002 : Route 9 := (fun mask => (mask,id))

def c37002 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37002 : Upper (D 6) (R 6) [34,129,40,80,260] 13 := by
  apply FastRouting.sound _ _ [34,129,40,80,260] 13 (by decide) (choices 1) [1,2,4,64] r37002 c37002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21751
  · exact u21752
  · exact u21753
  · exact u21754

def b37003 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 44 88 336 39 71 135 263), lower := (rows 35 131 44 88 336 32 64 128 256), losses := [] }

theorem u37003 : Upper (D 6) (R 6) [34,129,40,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37004 : Route 9 := (fun mask => (mask,id))

def c37004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37004 : Upper (D 6) (R 6) [34,129,40,257,6] 13 := by
  apply FastRouting.sound _ _ [34,129,40,257,6] 13 (by decide) (choices 1) [4,16,64] r37004 c37004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21755
  · exact u21756
  · exact u21757

def r37005 : Route 9 := (fun mask => (mask,id))

def c37005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37005 : Upper (D 6) (R 6) [34,129,40,257,66] 13 := by
  apply FastRouting.sound _ _ [34,129,40,257,66] 13 (by decide) (choices 1) [4,16,64] r37005 c37005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21758
  · exact u21759
  · exact u21760

def r37006 : Route 9 := (fun mask => (mask,id))

def c37006 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37006 : Upper (D 6) (R 6) [34,129,40,257,68] 13 := by
  apply FastRouting.sound _ _ [34,129,40,257,68] 13 (by decide) (choices 1) [2,4,16,64] r37006 c37006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21761
  · exact u21762
  · exact u21763
  · exact u21764

def r37007 : Route 9 := (fun mask => (mask,id))

def c37007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37007 : Upper (D 6) (R 6) [34,129,40,258,5] 13 := by
  apply FastRouting.sound _ _ [34,129,40,258,5] 13 (by decide) (choices 1) [4,16,64] r37007 c37007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21765
  · exact u21766
  · exact u21767

def r37008 : Route 9 := (fun mask => (mask,id))

def c37008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37008 : Upper (D 6) (R 6) [34,129,40,258,65] 13 := by
  apply FastRouting.sound _ _ [34,129,40,258,65] 13 (by decide) (choices 1) [4,16,64] r37008 c37008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21768
  · exact u21769
  · exact u21770

def r37009 : Route 9 := (fun mask => (mask,id))

def c37009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37009 : Upper (D 6) (R 6) [34,129,40,258,68] 13 := by
  apply FastRouting.sound _ _ [34,129,40,258,68] 13 (by decide) (choices 1) [1,4,16,64] r37009 c37009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21771
  · exact u21772
  · exact u21773
  · exact u21774

def b37010 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 268 19 116 84 212 340), lower := (rows 35 131 44 268 19 32 64 128 256), losses := [] }

theorem u37010 : Upper (D 6) (R 6) [34,129,40,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37011 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 227, targets := 4 },{ cop := 4, region := 194, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 131 44 268 21 114 82 210 338), lower := (rows 35 131 44 268 21 32 64 128 256), losses := [] }

theorem u37011 : Upper (D 6) (R 6) [34,129,40,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37012 : Route 9 := (fun mask => (mask,id))

def c37012 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37012 : Upper (D 6) (R 6) [34,129,40,260,6] 13 := by
  apply FastRouting.sound _ _ [34,129,40,260,6] 13 (by decide) (choices 1) [1,16,64] r37012 c37012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21775
  · exact u21776
  · exact u21777

def r37013 : Route 9 := (fun mask => (mask,id))

def c37013 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37013 : Upper (D 6) (R 6) [34,129,40,260,65] 13 := by
  apply FastRouting.sound _ _ [34,129,40,260,65] 13 (by decide) (choices 1) [2,4,16,64] r37013 c37013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21778
  · exact u21779
  · exact u21780
  · exact u21781

def r37014 : Route 9 := (fun mask => (mask,id))

def c37014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37014 : Upper (D 6) (R 6) [34,129,40,260,66] 13 := by
  apply FastRouting.sound _ _ [34,129,40,260,66] 13 (by decide) (choices 1) [1,4,16,64] r37014 c37014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21782
  · exact u21783
  · exact u21784
  · exact u21785

def r37015 : Route 9 := (fun mask => (mask,id))

def c37015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37015 : Upper (D 6) (R 6) [34,129,40,260,68] 13 := by
  apply FastRouting.sound _ _ [34,129,40,260,68] 13 (by decide) (choices 1) [1,2,16,64] r37015 c37015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21786
  · exact u21787
  · exact u21788
  · exact u21789

def b37016 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 280 19 100 68 196 324), lower := (rows 35 131 44 280 19 32 64 128 256), losses := [] }

theorem u37016 : Upper (D 6) (R 6) [34,129,40,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37017 : Route 9 := (fun mask => (mask,id))

def c37017 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37017 : Upper (D 6) (R 6) [34,129,40,272,5] 13 := by
  apply FastRouting.sound _ _ [34,129,40,272,5] 13 (by decide) (choices 1) [2,4,64] r37017 c37017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21790
  · exact u21791
  · exact u21792

def r37018 : Route 9 := (fun mask => (mask,id))

def c37018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37018 : Upper (D 6) (R 6) [34,129,40,272,6] 13 := by
  apply FastRouting.sound _ _ [34,129,40,272,6] 13 (by decide) (choices 1) [1,4,64] r37018 c37018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21793
  · exact u21794
  · exact u21795

def r37019 : Route 9 := (fun mask => (mask,id))

def c37019 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37019 : Upper (D 6) (R 6) [34,129,40,272,65] 13 := by
  apply FastRouting.sound _ _ [34,129,40,272,65] 13 (by decide) (choices 1) [2,4,64] r37019 c37019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21796
  · exact u21797
  · exact u21798

#print axioms u37019
end Delivery.IrregularNine14.P06
