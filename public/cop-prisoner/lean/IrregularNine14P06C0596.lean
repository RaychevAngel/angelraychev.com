import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0329
import IrregularNine14P06C0330
import IrregularNine14P06C0331

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35760 : Route 9 := (fun mask => (mask,id))

def c35760 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35760 : Upper (D 6) (R 6) [34,65,136,260,96] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260,96] 13 (by decide) (choices 1) [1,2,4,16] r35760 c35760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19789
  · exact u19790
  · exact u19791
  · exact u19792

def b35761 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 140 280 19 100 100 228 356), lower := (rows 35 67 140 280 19 32 64 128 256), losses := [] }

theorem u35761 : Upper (D 6) (R 6) [34,65,136,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35762 : Route 9 := (fun mask => (mask,id))

def c35762 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35762 : Upper (D 6) (R 6) [34,65,136,272,5] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,5] 13 (by decide) (choices 1) [2,4,64] r35762 c35762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19793
  · exact u19794
  · exact u19795

def b35763 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 67 140 280 49 102 70 198 326), lower := (rows 35 67 140 280 49 32 64 128 256), losses := [] }

theorem u35763 : Upper (D 6) (R 6) [34,65,136,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35764 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 67 140 280 50 101 69 197 325), lower := (rows 35 67 140 280 50 32 64 128 256), losses := [] }

theorem u35764 : Upper (D 6) (R 6) [34,65,136,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35765 : Route 9 := (fun mask => (mask,id))

def c35765 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35765 : Upper (D 6) (R 6) [34,65,136,272,36] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,36] 13 (by decide) (choices 1) [1,2,4,64] r35765 c35765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19796
  · exact u19797
  · exact u19798
  · exact u19799

def r35766 : Route 9 := (fun mask => (mask,id))

def c35766 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35766 : Upper (D 6) (R 6) [34,65,136,272,96] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,96] 13 (by decide) (choices 1) [1,2,4] r35766 c35766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19800
  · exact u19801
  · exact u19802

def b35767 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 140 296 19 116 84 212 340), lower := (rows 35 67 140 296 19 32 64 128 256), losses := [] }

theorem u35767 : Upper (D 6) (R 6) [34,65,136,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35768 : Route 9 := (fun mask => (mask,id))

def c35768 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35768 : Upper (D 6) (R 6) [34,65,136,288,5] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,5] 13 (by decide) (choices 1) [2,4,16,64] r35768 c35768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19803
  · exact u19804
  · exact u19805
  · exact u19806

def r35769 : Route 9 := (fun mask => (mask,id))

def c35769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35769 : Upper (D 6) (R 6) [34,65,136,288,6] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,6] 13 (by decide) (choices 1) [1,4,16,64] r35769 c35769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19807
  · exact u19808
  · exact u19809
  · exact u19810

def b35770 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 16, targets := 36 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,5)], upper := (rows 35 67 140 296 81 54 86 150 278), lower := (rows 35 67 140 296 81 32 64 128 256), losses := [] }

theorem u35770 : Upper (D 6) (R 6) [34,65,136,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35771 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 140 296 82 53 85 149 277), lower := (rows 35 67 140 296 82 32 64 128 256), losses := [] }

theorem u35771 : Upper (D 6) (R 6) [34,65,136,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35772 : Route 9 := (fun mask => (mask,id))

def c35772 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35772 : Upper (D 6) (R 6) [34,65,136,288,68] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,68] 13 (by decide) (choices 1) [1,2,4,16] r35772 c35772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19811
  · exact u19812
  · exact u19813
  · exact u19814

def b35773 : PairBound 9 := { available := 340, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 164 11 28 372 340 468 340), lower := (rows 35 67 164 11 28 32 64 128 256), losses := [] }

theorem u35773 : Upper (D 6) (R 6) [34,65,160,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35774 : PairBound 9 := { available := 284, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 164 11 84 316 348 412 284), lower := (rows 35 67 164 11 84 32 64 128 256), losses := [] }

theorem u35774 : Upper (D 6) (R 6) [34,65,160,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35775 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 67 164 11 88 308 340 404 276), lower := (rows 35 67 164 11 88 32 64 128 256), losses := [] }

theorem u35775 : Upper (D 6) (R 6) [34,65,160,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35776 : PairBound 9 := { available := 92, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 164 11 276 124 92 220 348), lower := (rows 35 67 164 11 276 32 64 128 256), losses := [] }

theorem u35776 : Upper (D 6) (R 6) [34,65,160,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35777 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 164 11 280 116 84 212 340), lower := (rows 35 67 164 11 280 32 64 128 256), losses := [] }

theorem u35777 : Upper (D 6) (R 6) [34,65,160,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35778 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 164 11 336 60 92 156 284), lower := (rows 35 67 164 11 336 32 64 128 256), losses := [] }

theorem u35778 : Upper (D 6) (R 6) [34,65,160,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35779 : Route 9 := (fun mask => (mask,id))

def c35779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u35779 : Upper (D 6) (R 6) [34,65,160,5,6] 13 := by
  apply FastRouting.sound _ _ [34,65,160,5,6] 13 (by decide) (choices 1) [8,16,64,256] r35779 c35779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19815
  · exact u19816
  · exact u19817
  · exact u19818

def b35780 : PairBound 9 := { available := 340, camps := [{ cop := 3, region := 338, targets := 32 },{ cop := 4, region := 484, targets := 1 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 35 67 164 13 26 372 340 468 340), lower := (rows 35 67 164 13 26 32 64 128 256), losses := [] }

theorem u35780 : Upper (D 6) (R 6) [34,65,160,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35781 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 164 13 28 370 338 466 338), lower := (rows 35 67 164 13 28 32 64 128 256), losses := [] }

theorem u35781 : Upper (D 6) (R 6) [34,65,160,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35782 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 164 13 82 316 348 412 284), lower := (rows 35 67 164 13 82 32 64 128 256), losses := [] }

theorem u35782 : Upper (D 6) (R 6) [34,65,160,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35783 : Route 9 := (fun mask => (mask,id))

def c35783 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35783 : Upper (D 6) (R 6) [34,65,160,5,68] 13 := by
  apply FastRouting.sound _ _ [34,65,160,5,68] 13 (by decide) (choices 1) [2,8,16,256] r35783 c35783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19819
  · exact u19820
  · exact u19821
  · exact u19822

def r35784 : Route 9 := (fun mask => (mask,id))

def c35784 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35784 : Upper (D 6) (R 6) [34,65,160,5,72] 13 := by
  apply FastRouting.sound _ _ [34,65,160,5,72] 13 (by decide) (choices 1) [2,4,16,256] r35784 c35784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19823
  · exact u19824
  · exact u19825
  · exact u19826

def r35785 : Route 9 := (fun mask => (mask,id))

def c35785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35785 : Upper (D 6) (R 6) [34,65,160,5,258] 13 := by
  apply FastRouting.sound _ _ [34,65,160,5,258] 13 (by decide) (choices 1) [4,8,16,64] r35785 c35785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19827
  · exact u19828
  · exact u19829
  · exact u19830

def r35786 : Route 9 := (fun mask => (mask,id))

def c35786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35786 : Upper (D 6) (R 6) [34,65,160,5,260] 13 := by
  apply FastRouting.sound _ _ [34,65,160,5,260] 13 (by decide) (choices 1) [2,8,16,64] r35786 c35786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19831
  · exact u19832
  · exact u19833
  · exact u19834

def r35787 : Route 9 := (fun mask => (mask,id))

def c35787 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35787 : Upper (D 6) (R 6) [34,65,160,5,264] 13 := by
  apply FastRouting.sound _ _ [34,65,160,5,264] 13 (by decide) (choices 1) [2,4,16,64] r35787 c35787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19835
  · exact u19836
  · exact u19837
  · exact u19838

def r35788 : Route 9 := (fun mask => (mask,id))

def c35788 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35788 : Upper (D 6) (R 6) [34,65,160,5,320] 13 := by
  apply FastRouting.sound _ _ [34,65,160,5,320] 13 (by decide) (choices 1) [2,4,8,16] r35788 c35788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19839
  · exact u19840
  · exact u19841
  · exact u19842

def r35789 : Route 9 := (fun mask => (mask,id))

def c35789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u35789 : Upper (D 6) (R 6) [34,65,160,6,9] 13 := by
  apply FastRouting.sound _ _ [34,65,160,6,9] 13 (by decide) (choices 1) [4,16,64,256] r35789 c35789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19843
  · exact u19844
  · exact u19845
  · exact u19846

def b35790 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 67 164 14 28 369 337 465 337), lower := (rows 35 67 164 14 28 32 64 128 256), losses := [] }

theorem u35790 : Upper (D 6) (R 6) [34,65,160,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35791 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 16, targets := 36 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,5)], upper := (rows 35 67 164 14 81 316 348 412 284), lower := (rows 35 67 164 14 81 32 64 128 256), losses := [] }

theorem u35791 : Upper (D 6) (R 6) [34,65,160,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35792 : Route 9 := (fun mask => (mask,id))

def c35792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35792 : Upper (D 6) (R 6) [34,65,160,6,68] 13 := by
  apply FastRouting.sound _ _ [34,65,160,6,68] 13 (by decide) (choices 1) [1,8,16,256] r35792 c35792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19847
  · exact u19848
  · exact u19849
  · exact u19850

def r35793 : Route 9 := (fun mask => (mask,id))

def c35793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35793 : Upper (D 6) (R 6) [34,65,160,6,72] 13 := by
  apply FastRouting.sound _ _ [34,65,160,6,72] 13 (by decide) (choices 1) [1,4,16,256] r35793 c35793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19851
  · exact u19852
  · exact u19853
  · exact u19854

def r35794 : Route 9 := (fun mask => (mask,id))

def c35794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35794 : Upper (D 6) (R 6) [34,65,160,6,257] 13 := by
  apply FastRouting.sound _ _ [34,65,160,6,257] 13 (by decide) (choices 1) [4,8,16,64] r35794 c35794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19855
  · exact u19856
  · exact u19857
  · exact u19858

def r35795 : Route 9 := (fun mask => (mask,id))

def c35795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35795 : Upper (D 6) (R 6) [34,65,160,6,260] 13 := by
  apply FastRouting.sound _ _ [34,65,160,6,260] 13 (by decide) (choices 1) [1,8,16,64] r35795 c35795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19859
  · exact u19860
  · exact u19861
  · exact u19862

def r35796 : Route 9 := (fun mask => (mask,id))

def c35796 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35796 : Upper (D 6) (R 6) [34,65,160,6,264] 13 := by
  apply FastRouting.sound _ _ [34,65,160,6,264] 13 (by decide) (choices 1) [1,4,16,64] r35796 c35796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19863
  · exact u19864
  · exact u19865
  · exact u19866

def r35797 : Route 9 := (fun mask => (mask,id))

def c35797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35797 : Upper (D 6) (R 6) [34,65,160,6,320] 13 := by
  apply FastRouting.sound _ _ [34,65,160,6,320] 13 (by decide) (choices 1) [1,4,8,16] r35797 c35797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19867
  · exact u19868
  · exact u19869
  · exact u19870

def b35798 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 67 164 25 26 356 324 452 324), lower := (rows 35 67 164 25 26 32 64 128 256), losses := [] }

theorem u35798 : Upper (D 6) (R 6) [34,65,160,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35799 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 452, targets := 1 }], pairs := [(1,5),(2,0),(4,0)], upper := (rows 35 67 164 25 28 358 326 454 326), lower := (rows 35 67 164 25 28 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 15 8 24 35 67 131 259), good := (rows 486 486 164 508 28 32 64 128 256) },{ target := 5, region := (rows 1 10 4 8 16 0 80 144 272), good := (rows 3 67 132 475 478 0 64 128 256) }] }

theorem u35799 : Upper (D 6) (R 6) [34,65,160,17,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35800 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 67 164 25 82 300 332 396 268), lower := (rows 35 67 164 25 82 32 64 128 256), losses := [] }

theorem u35800 : Upper (D 6) (R 6) [34,65,160,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35801 : Route 9 := (fun mask => (mask,id))

def c35801 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35801 : Upper (D 6) (R 6) [34,65,160,17,68] 13 := by
  apply FastRouting.sound _ _ [34,65,160,17,68] 13 (by decide) (choices 1) [2,4,8,256] r35801 c35801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19871
  · exact u19872
  · exact u19873
  · exact u19874

def b35802 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 67 164 25 88 294 326 390 262), lower := (rows 35 67 164 25 88 32 64 128 256), losses := [] }

theorem u35802 : Upper (D 6) (R 6) [34,65,160,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35803 : Route 9 := (fun mask => (mask,id))

def c35803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35803 : Upper (D 6) (R 6) [34,65,160,17,258] 13 := by
  apply FastRouting.sound _ _ [34,65,160,17,258] 13 (by decide) (choices 1) [4,8,64] r35803 c35803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19875
  · exact u19876
  · exact u19877

def r35804 : Route 9 := (fun mask => (mask,id))

def c35804 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35804 : Upper (D 6) (R 6) [34,65,160,17,260] 13 := by
  apply FastRouting.sound _ _ [34,65,160,17,260] 13 (by decide) (choices 1) [2,4,8,64] r35804 c35804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19878
  · exact u19879
  · exact u19880
  · exact u19881

def r35805 : Route 9 := (fun mask => (mask,id))

def c35805 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35805 : Upper (D 6) (R 6) [34,65,160,17,264] 13 := by
  apply FastRouting.sound _ _ [34,65,160,17,264] 13 (by decide) (choices 1) [2,4,64] r35805 c35805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19882
  · exact u19883
  · exact u19884

def r35806 : Route 9 := (fun mask => (mask,id))

def c35806 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35806 : Upper (D 6) (R 6) [34,65,160,17,320] 13 := by
  apply FastRouting.sound _ _ [34,65,160,17,320] 13 (by decide) (choices 1) [2,4,8] r35806 c35806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19885
  · exact u19886
  · exact u19887

def r35807 : Route 9 := (fun mask => (mask,id))

def c35807 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35807 : Upper (D 6) (R 6) [34,65,160,18,12] 13 := by
  apply FastRouting.sound _ _ [34,65,160,18,12] 13 (by decide) (choices 1) [1,4,64,256] r35807 c35807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19888
  · exact u19889
  · exact u19890
  · exact u19891

def b35808 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 67 164 26 81 300 332 396 268), lower := (rows 35 67 164 26 81 32 64 128 256), losses := [] }

theorem u35808 : Upper (D 6) (R 6) [34,65,160,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35809 : Route 9 := (fun mask => (mask,id))

def c35809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35809 : Upper (D 6) (R 6) [34,65,160,18,68] 13 := by
  apply FastRouting.sound _ _ [34,65,160,18,68] 13 (by decide) (choices 1) [1,4,8,256] r35809 c35809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19892
  · exact u19893
  · exact u19894
  · exact u19895

def b35810 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 24, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 67 164 26 88 293 325 389 261), lower := (rows 35 67 164 26 88 32 64 128 256), losses := [] }

theorem u35810 : Upper (D 6) (R 6) [34,65,160,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35811 : Route 9 := (fun mask => (mask,id))

def c35811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35811 : Upper (D 6) (R 6) [34,65,160,18,257] 13 := by
  apply FastRouting.sound _ _ [34,65,160,18,257] 13 (by decide) (choices 1) [4,8,64] r35811 c35811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19896
  · exact u19897
  · exact u19898

def r35812 : Route 9 := (fun mask => (mask,id))

def c35812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35812 : Upper (D 6) (R 6) [34,65,160,18,260] 13 := by
  apply FastRouting.sound _ _ [34,65,160,18,260] 13 (by decide) (choices 1) [1,4,8,64] r35812 c35812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19899
  · exact u19900
  · exact u19901
  · exact u19902

def r35813 : Route 9 := (fun mask => (mask,id))

def c35813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35813 : Upper (D 6) (R 6) [34,65,160,18,264] 13 := by
  apply FastRouting.sound _ _ [34,65,160,18,264] 13 (by decide) (choices 1) [1,4,64] r35813 c35813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19903
  · exact u19904
  · exact u19905

def r35814 : Route 9 := (fun mask => (mask,id))

def c35814 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35814 : Upper (D 6) (R 6) [34,65,160,18,320] 13 := by
  apply FastRouting.sound _ _ [34,65,160,18,320] 13 (by decide) (choices 1) [1,4,8] r35814 c35814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19906
  · exact u19907
  · exact u19908

def b35815 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 164 28 28 355 323 451 323), lower := (rows 35 67 164 28 28 32 64 128 256), losses := [] }

theorem u35815 : Upper (D 6) (R 6) [34,65,160,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35816 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 16, targets := 36 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,5)], upper := (rows 35 67 164 28 81 302 334 398 270), lower := (rows 35 67 164 28 81 32 64 128 256), losses := [] }

theorem u35816 : Upper (D 6) (R 6) [34,65,160,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35817 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 164 28 82 301 333 397 269), lower := (rows 35 67 164 28 82 32 64 128 256), losses := [] }

theorem u35817 : Upper (D 6) (R 6) [34,65,160,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35818 : PairBound 9 := { available := 267, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 164 28 84 299 331 395 267), lower := (rows 35 67 164 28 84 32 64 128 256), losses := [] }

theorem u35818 : Upper (D 6) (R 6) [34,65,160,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35819 : Route 9 := (fun mask => (mask,id))

def c35819 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35819 : Upper (D 6) (R 6) [34,65,160,20,72] 13 := by
  apply FastRouting.sound _ _ [34,65,160,20,72] 13 (by decide) (choices 1) [1,2,4,256] r35819 c35819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19909
  · exact u19910
  · exact u19911
  · exact u19912

#print axioms u35819
end Delivery.IrregularNine14.P06
