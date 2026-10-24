import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0094
import IrregularNine14P08C0095

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15900 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 138 280 52 116 180 308), lower := (rows 193 35 69 138 280 32 64 128 256), losses := [] }

theorem u15900 : Upper (D 8) (R 8) [192,33,65,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15901 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 138 304 60 124 188 316), lower := (rows 193 35 69 138 304 32 64 128 256), losses := [] }

theorem u15901 : Upper (D 8) (R 8) [192,33,65,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15902 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 140 274 56 120 184 312), lower := (rows 193 35 69 140 274 32 64 128 256), losses := [] }

theorem u15902 : Upper (D 8) (R 8) [192,33,65,132,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15903 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 140 280 50 114 178 306), lower := (rows 193 35 69 140 280 32 64 128 256), losses := [] }

theorem u15903 : Upper (D 8) (R 8) [192,33,65,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15904 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 140 304 58 122 186 314), lower := (rows 193 35 69 140 304 32 64 128 256), losses := [] }

theorem u15904 : Upper (D 8) (R 8) [192,33,65,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15905 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 152 274 44 108 172 300), lower := (rows 193 35 69 152 274 32 64 128 256), losses := [] }

theorem u15905 : Upper (D 8) (R 8) [192,33,65,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15905 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15906 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 152 276 42 106 170 298), lower := (rows 193 35 69 152 276 32 64 128 256), losses := [] }

theorem u15906 : Upper (D 8) (R 8) [192,33,65,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15907 : PairBound 9 := { available := 46, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 152 304 46 110 174 302), lower := (rows 193 35 69 152 304 32 64 128 256), losses := [] }

theorem u15907 : Upper (D 8) (R 8) [192,33,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15908 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 168 274 60 124 188 316), lower := (rows 193 35 69 168 274 32 64 128 256), losses := [] }

theorem u15908 : Upper (D 8) (R 8) [192,33,65,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15909 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 168 276 58 122 186 314), lower := (rows 193 35 69 168 276 32 64 128 256), losses := [] }

theorem u15909 : Upper (D 8) (R 8) [192,33,65,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15910 : PairBound 9 := { available := 54, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 168 280 54 118 182 310), lower := (rows 193 35 69 168 280 32 64 128 256), losses := [] }

theorem u15910 : Upper (D 8) (R 8) [192,33,65,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15911 : PairBound 9 := { available := 30, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 69 168 304 62 94 158 286), lower := (rows 193 35 69 168 304 32 64 128 256), losses := [] }

theorem u15911 : Upper (D 8) (R 8) [192,33,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15912 : Route 9 := (fun mask => (mask,id))

def c15912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15912 : Upper (D 8) (R 8) [192,33,66,132,257] 13 := by
  apply FastRouting.sound _ _ [192,33,66,132,257] 13 (by decide) (choices 1) [8,16] r15912 c15912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5647
  · exact u5648

def r15913 : Route 9 := (fun mask => (mask,id))

def c15913 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15913 : Upper (D 8) (R 8) [192,33,66,132,264] 13 := by
  apply FastRouting.sound _ _ [192,33,66,132,264] 13 (by decide) (choices 1) [1,16] r15913 c15913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5649
  · exact u5650

def r15914 : Route 9 := (fun mask => (mask,id))

def c15914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15914 : Upper (D 8) (R 8) [192,33,66,132,288] 13 := by
  apply FastRouting.sound _ _ [192,33,66,132,288] 13 (by decide) (choices 1) [1,8,16] r15914 c15914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5651
  · exact u5652
  · exact u5653

def r15915 : Route 9 := (fun mask => (mask,id))

def c15915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15915 : Upper (D 8) (R 8) [192,33,66,144,257] 13 := by
  apply FastRouting.sound _ _ [192,33,66,144,257] 13 (by decide) (choices 1) [4,8] r15915 c15915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5654
  · exact u5655

def r15916 : Route 9 := (fun mask => (mask,id))

def c15916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15916 : Upper (D 8) (R 8) [192,33,66,144,260] 13 := by
  apply FastRouting.sound _ _ [192,33,66,144,260] 13 (by decide) (choices 1) [1,8] r15916 c15916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5656
  · exact u5657

def b15917 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 38, targets := 128 }], pairs := [(1,7)], upper := (rows 193 35 70 152 280 37 101 165 293), lower := (rows 193 35 70 152 280 32 64 128 256), losses := [] }

theorem u15917 : Upper (D 8) (R 8) [192,33,66,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15918 : Route 9 := (fun mask => (mask,id))

def c15918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15918 : Upper (D 8) (R 8) [192,33,66,144,288] 13 := by
  apply FastRouting.sound _ _ [192,33,66,144,288] 13 (by decide) (choices 1) [1,4,8] r15918 c15918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5658
  · exact u5659
  · exact u5660

def r15919 : Route 9 := (fun mask => (mask,id))

def c15919 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15919 : Upper (D 8) (R 8) [192,33,66,160,257] 13 := by
  apply FastRouting.sound _ _ [192,33,66,160,257] 13 (by decide) (choices 1) [4,8,16] r15919 c15919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5661
  · exact u5662
  · exact u5663

def r15920 : Route 9 := (fun mask => (mask,id))

def c15920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15920 : Upper (D 8) (R 8) [192,33,66,160,260] 13 := by
  apply FastRouting.sound _ _ [192,33,66,160,260] 13 (by decide) (choices 1) [1,8,16] r15920 c15920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5664
  · exact u5665
  · exact u5666

def r15921 : Route 9 := (fun mask => (mask,id))

def c15921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15921 : Upper (D 8) (R 8) [192,33,66,160,264] 13 := by
  apply FastRouting.sound _ _ [192,33,66,160,264] 13 (by decide) (choices 1) [1,4,16] r15921 c15921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5667
  · exact u5668
  · exact u5669

def r15922 : Route 9 := (fun mask => (mask,id))

def c15922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15922 : Upper (D 8) (R 8) [192,33,66,160,288] 13 := by
  apply FastRouting.sound _ _ [192,33,66,160,288] 13 (by decide) (choices 1) [1,4,8,16] r15922 c15922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5670
  · exact u5671
  · exact u5672
  · exact u5673

def b15923 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 76 140 273 50 114 178 306), lower := (rows 193 35 76 140 273 32 64 128 256), losses := [] }

theorem u15923 : Upper (D 8) (R 8) [192,33,72,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15924 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 76 140 274 49 113 177 305), lower := (rows 193 35 76 140 274 32 64 128 256), losses := [] }

theorem u15924 : Upper (D 8) (R 8) [192,33,72,132,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15924 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15925 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 76 140 304 51 115 179 307), lower := (rows 193 35 76 140 304 32 64 128 256), losses := [] }

theorem u15925 : Upper (D 8) (R 8) [192,33,72,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15926 : Route 9 := (fun mask => (mask,id))

def c15926 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15926 : Upper (D 8) (R 8) [192,33,72,144,257] 13 := by
  apply FastRouting.sound _ _ [192,33,72,144,257] 13 (by decide) (choices 1) [2,4] r15926 c15926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5674
  · exact u5675

def r15927 : Route 9 := (fun mask => (mask,id))

def c15927 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15927 : Upper (D 8) (R 8) [192,33,72,144,258] 13 := by
  apply FastRouting.sound _ _ [192,33,72,144,258] 13 (by decide) (choices 1) [1,4] r15927 c15927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5676
  · exact u5677

def b15928 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 76 152 276 35 99 163 291), lower := (rows 193 35 76 152 276 32 64 128 256), losses := [] }

theorem u15928 : Upper (D 8) (R 8) [192,33,72,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15929 : Route 9 := (fun mask => (mask,id))

def c15929 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15929 : Upper (D 8) (R 8) [192,33,72,144,288] 13 := by
  apply FastRouting.sound _ _ [192,33,72,144,288] 13 (by decide) (choices 1) [1,2,4] r15929 c15929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5678
  · exact u5679
  · exact u5680

def r15930 : Route 9 := (fun mask => (mask,id))

def c15930 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15930 : Upper (D 8) (R 8) [192,33,72,160,257] 13 := by
  apply FastRouting.sound _ _ [192,33,72,160,257] 13 (by decide) (choices 1) [2,4,16] r15930 c15930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5681
  · exact u5682
  · exact u5683

def r15931 : Route 9 := (fun mask => (mask,id))

def c15931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15931 : Upper (D 8) (R 8) [192,33,72,160,258] 13 := by
  apply FastRouting.sound _ _ [192,33,72,160,258] 13 (by decide) (choices 1) [1,4,16] r15931 c15931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5684
  · exact u5685
  · exact u5686

def r15932 : Route 9 := (fun mask => (mask,id))

def c15932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15932 : Upper (D 8) (R 8) [192,33,72,160,260] 13 := by
  apply FastRouting.sound _ _ [192,33,72,160,260] 13 (by decide) (choices 1) [1,2,16] r15932 c15932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5687
  · exact u5688
  · exact u5689

def r15933 : Route 9 := (fun mask => (mask,id))

def c15933 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15933 : Upper (D 8) (R 8) [192,33,72,160,288] 13 := by
  apply FastRouting.sound _ _ [192,33,72,160,288] 13 (by decide) (choices 1) [1,2,4,16] r15933 c15933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5690
  · exact u5691
  · exact u5692
  · exact u5693

def r15934 : Route 9 := (fun mask => (mask,id))

def c15934 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15934 : Upper (D 8) (R 8) [192,33,72,257,160] 13 := by
  apply FastRouting.sound _ _ [192,33,72,257,160] 13 (by decide) (choices 1) [2,4,16] r15934 c15934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5694
  · exact u5695
  · exact u5696

def r15935 : Route 9 := (fun mask => (mask,id))

def c15935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15935 : Upper (D 8) (R 8) [192,33,72,258,160] 13 := by
  apply FastRouting.sound _ _ [192,33,72,258,160] 13 (by decide) (choices 1) [1,4,16] r15935 c15935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5697
  · exact u5698
  · exact u5699

def b15936 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 50, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 76 268 176 51 115 179 307), lower := (rows 193 35 76 268 176 32 64 128 256), losses := [] }

theorem u15936 : Upper (D 8) (R 8) [192,33,72,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15937 : Route 9 := (fun mask => (mask,id))

def c15937 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15937 : Upper (D 8) (R 8) [192,33,72,272,160] 13 := by
  apply FastRouting.sound _ _ [192,33,72,272,160] 13 (by decide) (choices 1) [1,2,4] r15937 c15937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5700
  · exact u5701
  · exact u5702

def r15938 : Route 9 := (fun mask => (mask,id))

def c15938 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15938 : Upper (D 8) (R 8) [192,33,72,288,160] 13 := by
  apply FastRouting.sound _ _ [192,33,72,288,160] 13 (by decide) (choices 1) [1,2,4,16] r15938 c15938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5703
  · exact u5704
  · exact u5705
  · exact u5706

theorem m15939_8 : Upper (D 8) (R 8) [192,33,96,160,257,8] 13 :=
  permutation_upper _ _ _ [192,33,96,160,257,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5708

def r15939 : Route 9 := (fun mask => (mask,id))

def c15939 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15939 : Upper (D 8) (R 8) [192,33,96,160,257] 13 := by
  apply FastRouting.sound _ _ [192,33,96,160,257] 13 (by decide) (choices 1) [2,4,8,16] r15939 c15939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5707
  · exact u5708
  · exact m15939_8
  · exact u5709

theorem m15940_8 : Upper (D 8) (R 8) [192,33,96,160,258,8] 13 :=
  permutation_upper _ _ _ [192,33,96,160,258,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5711

def r15940 : Route 9 := (fun mask => (mask,id))

def c15940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15940 : Upper (D 8) (R 8) [192,33,96,160,258] 13 := by
  apply FastRouting.sound _ _ [192,33,96,160,258] 13 (by decide) (choices 1) [1,4,8,16] r15940 c15940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5710
  · exact u5711
  · exact m15940_8
  · exact u5712

def r15941 : Route 9 := (fun mask => (mask,id))

def c15941 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15941 : Upper (D 8) (R 8) [192,33,96,160,260] 13 := by
  apply FastRouting.sound _ _ [192,33,96,160,260] 13 (by decide) (choices 1) [1,2,8,16] r15941 c15941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5713
  · exact u5714
  · exact u5715
  · exact u5716

def b15942 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 38 56 273 233 201 201 457), lower := (rows 193 38 38 56 273 32 64 128 256), losses := [] }

theorem u15942 : Upper (D 8) (R 8) [192,36,34,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15943 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 38 56 280 225 193 193 449), lower := (rows 193 38 38 56 280 32 64 128 256), losses := [] }

theorem u15943 : Upper (D 8) (R 8) [192,36,34,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15944 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 38 56 336 169 201 137 393), lower := (rows 193 38 38 56 336 32 64 128 256), losses := [] }

theorem u15944 : Upper (D 8) (R 8) [192,36,34,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15945 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 38 88 176 297 329 393 265), lower := (rows 193 38 38 88 176 32 64 128 256), losses := [] }

theorem u15945 : Upper (D 8) (R 8) [192,36,34,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15946 : PairBound 9 := { available := 169, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 38 88 273 169 233 169 425), lower := (rows 193 38 38 88 273 32 64 128 256), losses := [] }

theorem u15946 : Upper (D 8) (R 8) [192,36,34,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15947 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 38 88 304 169 201 137 393), lower := (rows 193 38 38 88 304 32 64 128 256), losses := [] }

theorem u15947 : Upper (D 8) (R 8) [192,36,34,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15948 : PairBound 9 := { available := 41, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 38 88 400 41 105 169 297), lower := (rows 193 38 38 88 400 32 64 128 256), losses := [] }

theorem u15948 : Upper (D 8) (R 8) [192,36,34,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15949 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 38 104 273 185 217 153 409), lower := (rows 193 38 38 104 273 32 64 128 256), losses := [] }

theorem u15949 : Upper (D 8) (R 8) [192,36,34,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15950 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 38 104 280 177 209 145 401), lower := (rows 193 38 38 104 280 32 64 128 256), losses := [] }

theorem u15950 : Upper (D 8) (R 8) [192,36,34,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15951 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 38 104 400 57 89 153 281), lower := (rows 193 38 38 104 400 32 64 128 256), losses := [] }

theorem u15951 : Upper (D 8) (R 8) [192,36,34,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15952 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 56 82 417 449 385 385), lower := (rows 193 38 44 56 82 32 64 128 256), losses := [] }

theorem u15952 : Upper (D 8) (R 8) [192,36,40,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15953 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 56 273 227 195 195 451), lower := (rows 193 38 44 56 273 32 64 128 256), losses := [] }

theorem u15953 : Upper (D 8) (R 8) [192,36,40,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15954 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 56 274 225 193 193 449), lower := (rows 193 38 44 56 274 32 64 128 256), losses := [] }

theorem u15954 : Upper (D 8) (R 8) [192,36,40,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15955 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 56 336 163 195 131 387), lower := (rows 193 38 44 56 336 32 64 128 256), losses := [] }

theorem u15955 : Upper (D 8) (R 8) [192,36,40,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15956 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 74 176 305 337 401 273), lower := (rows 193 38 44 74 176 32 64 128 256), losses := [] }

theorem u15956 : Upper (D 8) (R 8) [192,36,40,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15957 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 74 273 177 241 177 433), lower := (rows 193 38 44 74 273 32 64 128 256), losses := [] }

theorem u15957 : Upper (D 8) (R 8) [192,36,40,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15958 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 74 304 177 209 145 401), lower := (rows 193 38 44 74 304 32 64 128 256), losses := [] }

theorem u15958 : Upper (D 8) (R 8) [192,36,40,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15959 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 44 74 400 49 113 177 305), lower := (rows 193 38 44 74 400 32 64 128 256), losses := [] }

theorem u15959 : Upper (D 8) (R 8) [192,36,40,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15959
end Delivery.IrregularNine14.P08
