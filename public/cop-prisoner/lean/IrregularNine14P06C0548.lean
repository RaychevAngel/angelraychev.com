import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0260
import IrregularNine14P06C0261

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32880 : Route 9 := (fun mask => (mask,id))

def c32880 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32880 : Upper (D 6) (R 6) [10,129,96,48,65] 13 := by
  apply FastRouting.sound _ _ [10,129,96,48,65] 13 (by decide) (choices 1) [2,4,256] r32880 c32880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15603
  · exact u15604
  · exact u15605

def r32881 : Route 9 := (fun mask => (mask,id))

def c32881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32881 : Upper (D 6) (R 6) [10,129,96,48,66] 13 := by
  apply FastRouting.sound _ _ [10,129,96,48,66] 13 (by decide) (choices 1) [1,4,256] r32881 c32881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15606
  · exact u15607
  · exact u15608

def b32882 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 100 56 84 295 327 391 263), lower := (rows 11 131 100 56 84 32 64 128 256), losses := [] }

theorem u32882 : Upper (D 6) (R 6) [10,129,96,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32883 : Route 9 := (fun mask => (mask,id))

def c32883 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32883 : Upper (D 6) (R 6) [10,129,96,48,257] 13 := by
  apply FastRouting.sound _ _ [10,129,96,48,257] 13 (by decide) (choices 1) [2,4,64] r32883 c32883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15609
  · exact u15610
  · exact u15611

def r32884 : Route 9 := (fun mask => (mask,id))

def c32884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32884 : Upper (D 6) (R 6) [10,129,96,48,258] 13 := by
  apply FastRouting.sound _ _ [10,129,96,48,258] 13 (by decide) (choices 1) [1,4,64] r32884 c32884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15612
  · exact u15613
  · exact u15614

def r32885 : Route 9 := (fun mask => (mask,id))

def c32885 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32885 : Upper (D 6) (R 6) [10,129,96,48,260] 13 := by
  apply FastRouting.sound _ _ [10,129,96,48,260] 13 (by decide) (choices 1) [1,2,4,64] r32885 c32885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15615
  · exact u15616
  · exact u15617
  · exact u15618

def r32886 : Route 9 := (fun mask => (mask,id))

def c32886 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32886 : Upper (D 6) (R 6) [10,129,96,48,320] 13 := by
  apply FastRouting.sound _ _ [10,129,96,48,320] 13 (by decide) (choices 1) [1,2,4] r32886 c32886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15619
  · exact u15620
  · exact u15621

def b32887 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 116, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 265 22 116 116 244 372), lower := (rows 11 131 100 265 22 32 64 128 256), losses := [] }

theorem u32887 : Upper (D 6) (R 6) [10,129,96,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32888 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 116, targets := 1 },{ cop := 4, region := 68, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 265 50 116 84 212 340), lower := (rows 11 131 100 265 50 32 64 128 256), losses := [] }

theorem u32888 : Upper (D 6) (R 6) [10,129,96,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32889 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 100 265 52 118 86 214 342), lower := (rows 11 131 100 265 52 32 64 128 256), losses := [] }

theorem u32889 : Upper (D 6) (R 6) [10,129,96,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32890 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 116, targets := 1 },{ cop := 2, region := 16, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 131 100 265 112 54 86 150 278), lower := (rows 11 131 100 265 112 32 64 128 256), losses := [] }

theorem u32890 : Upper (D 6) (R 6) [10,129,96,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32891 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 268 19 116 116 244 372), lower := (rows 11 131 100 268 19 32 64 128 256), losses := [] }

theorem u32891 : Upper (D 6) (R 6) [10,129,96,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32892 : Route 9 := (fun mask => (mask,id))

def c32892 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32892 : Upper (D 6) (R 6) [10,129,96,260,5] 13 := by
  apply FastRouting.sound _ _ [10,129,96,260,5] 13 (by decide) (choices 1) [2,16,64] r32892 c32892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15622
  · exact u15623
  · exact u15624

def r32893 : Route 9 := (fun mask => (mask,id))

def c32893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32893 : Upper (D 6) (R 6) [10,129,96,260,6] 13 := by
  apply FastRouting.sound _ _ [10,129,96,260,6] 13 (by decide) (choices 1) [1,16,64] r32893 c32893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15625
  · exact u15626
  · exact u15627

def r32894 : Route 9 := (fun mask => (mask,id))

def c32894 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32894 : Upper (D 6) (R 6) [10,129,96,260,33] 13 := by
  apply FastRouting.sound _ _ [10,129,96,260,33] 13 (by decide) (choices 1) [2,4,16,64] r32894 c32894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15628
  · exact u15629
  · exact u15630
  · exact u15631

def r32895 : Route 9 := (fun mask => (mask,id))

def c32895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32895 : Upper (D 6) (R 6) [10,129,96,260,34] 13 := by
  apply FastRouting.sound _ _ [10,129,96,260,34] 13 (by decide) (choices 1) [1,4,16,64] r32895 c32895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15632
  · exact u15633
  · exact u15634
  · exact u15635

def b32896 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 100 268 52 115 83 211 339), lower := (rows 11 131 100 268 52 32 64 128 256), losses := [] }

theorem u32896 : Upper (D 6) (R 6) [10,129,96,260,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32897 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 131 100 268 112 55 87 151 279), lower := (rows 11 131 100 268 112 32 64 128 256), losses := [] }

theorem u32897 : Upper (D 6) (R 6) [10,129,96,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32898 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 280 19 100 100 228 356), lower := (rows 11 131 100 280 19 32 64 128 256), losses := [] }

theorem u32898 : Upper (D 6) (R 6) [10,129,96,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32899 : Route 9 := (fun mask => (mask,id))

def c32899 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32899 : Upper (D 6) (R 6) [10,129,96,272,5] 13 := by
  apply FastRouting.sound _ _ [10,129,96,272,5] 13 (by decide) (choices 1) [2,4,64] r32899 c32899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15636
  · exact u15637
  · exact u15638

def r32900 : Route 9 := (fun mask => (mask,id))

def c32900 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32900 : Upper (D 6) (R 6) [10,129,96,272,6] 13 := by
  apply FastRouting.sound _ _ [10,129,96,272,6] 13 (by decide) (choices 1) [1,4,64] r32900 c32900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15639
  · exact u15640
  · exact u15641

def r32901 : Route 9 := (fun mask => (mask,id))

def c32901 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32901 : Upper (D 6) (R 6) [10,129,96,272,33] 13 := by
  apply FastRouting.sound _ _ [10,129,96,272,33] 13 (by decide) (choices 1) [2,4,64] r32901 c32901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15642
  · exact u15643
  · exact u15644

def r32902 : Route 9 := (fun mask => (mask,id))

def c32902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32902 : Upper (D 6) (R 6) [10,129,96,272,34] 13 := by
  apply FastRouting.sound _ _ [10,129,96,272,34] 13 (by decide) (choices 1) [1,4,64] r32902 c32902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15645
  · exact u15646
  · exact u15647

def b32903 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 100 280 52 103 71 199 327), lower := (rows 11 131 100 280 52 32 64 128 256), losses := [] }

theorem u32903 : Upper (D 6) (R 6) [10,129,96,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32904 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 131 100 280 112 39 71 135 263), lower := (rows 11 131 100 280 112 32 64 128 256), losses := [] }

theorem u32904 : Upper (D 6) (R 6) [10,129,96,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32905 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 296 19 116 84 212 340), lower := (rows 11 131 100 296 19 32 64 128 256), losses := [] }

theorem u32905 : Upper (D 6) (R 6) [10,129,96,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32906 : Route 9 := (fun mask => (mask,id))

def c32906 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32906 : Upper (D 6) (R 6) [10,129,96,288,5] 13 := by
  apply FastRouting.sound _ _ [10,129,96,288,5] 13 (by decide) (choices 1) [2,4,16,64] r32906 c32906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15648
  · exact u15649
  · exact u15650
  · exact u15651

def r32907 : Route 9 := (fun mask => (mask,id))

def c32907 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32907 : Upper (D 6) (R 6) [10,129,96,288,6] 13 := by
  apply FastRouting.sound _ _ [10,129,96,288,6] 13 (by decide) (choices 1) [1,4,16,64] r32907 c32907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15652
  · exact u15653
  · exact u15654
  · exact u15655

def r32908 : Route 9 := (fun mask => (mask,id))

def c32908 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32908 : Upper (D 6) (R 6) [10,129,96,288,65] 13 := by
  apply FastRouting.sound _ _ [10,129,96,288,65] 13 (by decide) (choices 1) [2,4,16] r32908 c32908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15656
  · exact u15657
  · exact u15658

def r32909 : Route 9 := (fun mask => (mask,id))

def c32909 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32909 : Upper (D 6) (R 6) [10,129,96,288,66] 13 := by
  apply FastRouting.sound _ _ [10,129,96,288,66] 13 (by decide) (choices 1) [1,4,16] r32909 c32909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15659
  · exact u15660
  · exact u15661

def b32910 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 131 100 296 84 55 87 151 279), lower := (rows 11 131 100 296 84 32 64 128 256), losses := [] }

theorem u32910 : Upper (D 6) (R 6) [10,129,96,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32911 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 261 28 22 96 96 224 352), lower := (rows 11 131 261 28 22 32 64 128 256), losses := [] }

theorem u32911 : Upper (D 6) (R 6) [10,129,257,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32912 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 131 261 28 50 100 100 228 356), lower := (rows 11 131 261 28 50 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 44 76 140 268), good := (rows 506 146 508 508 50 32 64 128 256) }] }

theorem u32912 : Upper (D 6) (R 6) [10,129,257,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32913 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 131 261 28 52 98 98 226 354), lower := (rows 11 131 261 28 52 32 64 128 256), losses := [] }

theorem u32913 : Upper (D 6) (R 6) [10,129,257,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32914 : Route 9 := (fun mask => (mask,id))

def c32914 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32914 : Upper (D 6) (R 6) [10,129,257,20,96] 13 := by
  apply FastRouting.sound _ _ [10,129,257,20,96] 13 (by decide) (choices 1) [2,4,64] r32914 c32914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15662
  · exact u15663
  · exact u15664

def r32915 : Route 9 := (fun mask => (mask,id))

def c32915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32915 : Upper (D 6) (R 6) [10,129,257,36,6] 13 := by
  apply FastRouting.sound _ _ [10,129,257,36,6] 13 (by decide) (choices 1) [16,64] r32915 c32915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15665
  · exact u15666

def r32916 : Route 9 := (fun mask => (mask,id))

def c32916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32916 : Upper (D 6) (R 6) [10,129,257,36,34] 13 := by
  apply FastRouting.sound _ _ [10,129,257,36,34] 13 (by decide) (choices 1) [4,16,64] r32916 c32916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15667
  · exact u15668
  · exact u15669

def b32917 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 261 44 52 114 82 210 338), lower := (rows 11 131 261 44 52 32 64 128 256), losses := [] }

theorem u32917 : Upper (D 6) (R 6) [10,129,257,36,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32918 : Route 9 := (fun mask => (mask,id))

def c32918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32918 : Upper (D 6) (R 6) [10,129,257,36,66] 13 := by
  apply FastRouting.sound _ _ [10,129,257,36,66] 13 (by decide) (choices 1) [4,16,64] r32918 c32918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15670
  · exact u15671
  · exact u15672

def r32919 : Route 9 := (fun mask => (mask,id))

def c32919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32919 : Upper (D 6) (R 6) [10,129,257,36,68] 13 := by
  apply FastRouting.sound _ _ [10,129,257,36,68] 13 (by decide) (choices 1) [2,16,64] r32919 c32919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15673
  · exact u15674
  · exact u15675

def r32920 : Route 9 := (fun mask => (mask,id))

def c32920 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32920 : Upper (D 6) (R 6) [10,129,257,36,96] 13 := by
  apply FastRouting.sound _ _ [10,129,257,36,96] 13 (by decide) (choices 1) [2,4,16,64] r32920 c32920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15676
  · exact u15677
  · exact u15678
  · exact u15679

def b32921 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 131 261 56 22 100 100 228 356), lower := (rows 11 131 261 56 22 32 64 128 256), losses := [] }

theorem u32921 : Upper (D 6) (R 6) [10,129,257,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32922 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 131 261 56 50 100 68 196 324), lower := (rows 11 131 261 56 50 32 64 128 256), losses := [] }

theorem u32922 : Upper (D 6) (R 6) [10,129,257,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32923 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 261 56 52 102 70 198 326), lower := (rows 11 131 261 56 52 32 64 128 256), losses := [] }

theorem u32923 : Upper (D 6) (R 6) [10,129,257,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32924 : Route 9 := (fun mask => (mask,id))

def c32924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32924 : Upper (D 6) (R 6) [10,129,257,48,66] 13 := by
  apply FastRouting.sound _ _ [10,129,257,48,66] 13 (by decide) (choices 1) [4,64] r32924 c32924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15680
  · exact u15681

def r32925 : Route 9 := (fun mask => (mask,id))

def c32925 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32925 : Upper (D 6) (R 6) [10,129,257,48,68] 13 := by
  apply FastRouting.sound _ _ [10,129,257,48,68] 13 (by decide) (choices 1) [2,4,64] r32925 c32925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15682
  · exact u15683
  · exact u15684

def b32926 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 261 56 112 102 70 198 326), lower := (rows 11 131 261 56 112 32 64 128 256), losses := [] }

theorem u32926 : Upper (D 6) (R 6) [10,129,257,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32927 : Route 9 := (fun mask => (mask,id))

def c32927 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32927 : Upper (D 6) (R 6) [10,129,257,96,6] 13 := by
  apply FastRouting.sound _ _ [10,129,257,96,6] 13 (by decide) (choices 1) [4,16,64] r32927 c32927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15685
  · exact u15686
  · exact u15687

def r32928 : Route 9 := (fun mask => (mask,id))

def c32928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32928 : Upper (D 6) (R 6) [10,129,257,96,34] 13 := by
  apply FastRouting.sound _ _ [10,129,257,96,34] 13 (by decide) (choices 1) [4,16,64] r32928 c32928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15688
  · exact u15689
  · exact u15690

def r32929 : Route 9 := (fun mask => (mask,id))

def c32929 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32929 : Upper (D 6) (R 6) [10,129,257,96,36] 13 := by
  apply FastRouting.sound _ _ [10,129,257,96,36] 13 (by decide) (choices 1) [2,4,16,64] r32929 c32929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15691
  · exact u15692
  · exact u15693
  · exact u15694

def b32930 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 131 261 104 112 54 86 150 278), lower := (rows 11 131 261 104 112 32 64 128 256), losses := [] }

theorem u32930 : Upper (D 6) (R 6) [10,129,257,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32931 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 262 28 21 96 96 224 352), lower := (rows 11 131 262 28 21 32 64 128 256), losses := [] }

theorem u32931 : Upper (D 6) (R 6) [10,129,258,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32932 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0),(4,1)], upper := (rows 11 131 262 28 49 100 100 228 356), lower := (rows 11 131 262 28 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 63 95 159 287), good := (rows 494 486 486 508 508 32 64 128 256) },{ target := 1, region := (rows 1 0 4 8 17 44 76 140 268), good := (rows 505 145 484 508 49 32 64 128 256) }] }

theorem u32932 : Upper (D 6) (R 6) [10,129,258,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32933 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 131 262 28 52 97 97 225 353), lower := (rows 11 131 262 28 52 32 64 128 256), losses := [] }

theorem u32933 : Upper (D 6) (R 6) [10,129,258,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32934 : Route 9 := (fun mask => (mask,id))

def c32934 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32934 : Upper (D 6) (R 6) [10,129,258,20,96] 13 := by
  apply FastRouting.sound _ _ [10,129,258,20,96] 13 (by decide) (choices 1) [1,4,64] r32934 c32934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15695
  · exact u15696
  · exact u15697

def b32935 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 131 262 44 21 112 112 240 368), lower := (rows 11 131 262 44 21 32 64 128 256), losses := [] }

theorem u32935 : Upper (D 6) (R 6) [10,129,258,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32936 : Route 9 := (fun mask => (mask,id))

def c32936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32936 : Upper (D 6) (R 6) [10,129,258,36,33] 13 := by
  apply FastRouting.sound _ _ [10,129,258,36,33] 13 (by decide) (choices 1) [4,16,64] r32936 c32936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15698
  · exact u15699
  · exact u15700

def b32937 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 262 44 52 113 81 209 337), lower := (rows 11 131 262 44 52 32 64 128 256), losses := [] }

theorem u32937 : Upper (D 6) (R 6) [10,129,258,36,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32938 : Route 9 := (fun mask => (mask,id))

def c32938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32938 : Upper (D 6) (R 6) [10,129,258,36,65] 13 := by
  apply FastRouting.sound _ _ [10,129,258,36,65] 13 (by decide) (choices 1) [4,16,64] r32938 c32938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15701
  · exact u15702
  · exact u15703

def r32939 : Route 9 := (fun mask => (mask,id))

def c32939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32939 : Upper (D 6) (R 6) [10,129,258,36,68] 13 := by
  apply FastRouting.sound _ _ [10,129,258,36,68] 13 (by decide) (choices 1) [1,16,64] r32939 c32939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15704
  · exact u15705
  · exact u15706

#print axioms u32939
end Delivery.IrregularNine14.P06
