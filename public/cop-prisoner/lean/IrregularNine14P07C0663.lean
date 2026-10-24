import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0467
import IrregularNine14P07C0468
import IrregularNine14P07C0469

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39780 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 7 73 152 310 342 406 278), lower := (rows 97 162 7 73 152 32 64 128 256), losses := [] }

theorem u39780 : Upper (D 7) (R 7) [96,160,3,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39781 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 7 73 274 188 220 156 412), lower := (rows 97 162 7 73 274 32 64 128 256), losses := [] }

theorem u39781 : Upper (D 7) (R 7) [96,160,3,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39782 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 7 73 276 186 218 154 410), lower := (rows 97 162 7 73 276 32 64 128 256), losses := [] }

theorem u39782 : Upper (D 7) (R 7) [96,160,3,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39783 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 7 73 280 182 214 150 406), lower := (rows 97 162 7 73 280 32 64 128 256), losses := [] }

theorem u39783 : Upper (D 7) (R 7) [96,160,3,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39784 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 7 73 400 62 94 158 286), lower := (rows 97 162 7 73 400 32 64 128 256), losses := [] }

theorem u39784 : Upper (D 7) (R 7) [96,160,3,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m39785_16 : Upper (D 7) (R 7) [96,160,3,66,129,16] 13 :=
  permutation_upper _ _ _ [96,160,3,66,129,8] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28021

def r39785 : Route 9 := (fun mask => (mask,id))

def c39785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39785 : Upper (D 7) (R 7) [96,160,3,66,129] 13 := by
  apply FastRouting.sound _ _ [96,160,3,66,129] 13 (by decide) (choices 1) [4,8,16,256] r39785 c39785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28020
  · exact u28021
  · exact m39785_16
  · exact u28022

def r39786 : Route 9 := (fun mask => (mask,id))

def c39786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39786 : Upper (D 7) (R 7) [96,160,3,66,132] 13 := by
  apply FastRouting.sound _ _ [96,160,3,66,132] 13 (by decide) (choices 1) [1,8,16,256] r39786 c39786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28023
  · exact u28024
  · exact u28025
  · exact u28026

def r39787 : Route 9 := (fun mask => (mask,id))

def c39787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39787 : Upper (D 7) (R 7) [96,160,3,66,136] 13 := by
  apply FastRouting.sound _ _ [96,160,3,66,136] 13 (by decide) (choices 1) [1,4,16,256] r39787 c39787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28027
  · exact u28028
  · exact u28029
  · exact u28030

def r39788 : Route 9 := (fun mask => (mask,id))

def c39788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39788 : Upper (D 7) (R 7) [96,160,3,66,257] 13 := by
  apply FastRouting.sound _ _ [96,160,3,66,257] 13 (by decide) (choices 1) [4,8,16,128] r39788 c39788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28031
  · exact u28032
  · exact u28033
  · exact u28034

def r39789 : Route 9 := (fun mask => (mask,id))

def c39789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39789 : Upper (D 7) (R 7) [96,160,3,66,260] 13 := by
  apply FastRouting.sound _ _ [96,160,3,66,260] 13 (by decide) (choices 1) [1,8,16,128] r39789 c39789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28035
  · exact u28036
  · exact u28037
  · exact u28038

def r39790 : Route 9 := (fun mask => (mask,id))

def c39790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39790 : Upper (D 7) (R 7) [96,160,3,66,264] 13 := by
  apply FastRouting.sound _ _ [96,160,3,66,264] 13 (by decide) (choices 1) [1,4,16,128] r39790 c39790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28039
  · exact u28040
  · exact u28041
  · exact u28042

def r39791 : Route 9 := (fun mask => (mask,id))

def c39791 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39791 : Upper (D 7) (R 7) [96,160,3,66,384] 13 := by
  apply FastRouting.sound _ _ [96,160,3,66,384] 13 (by decide) (choices 1) [1,4,8,16] r39791 c39791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28043
  · exact u28044
  · exact u28045
  · exact u28046

def r39792 : Route 9 := (fun mask => (mask,id))

def c39792 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39792 : Upper (D 7) (R 7) [96,160,3,68,136] 13 := by
  apply FastRouting.sound _ _ [96,160,3,68,136] 13 (by decide) (choices 1) [1,2,16,256] r39792 c39792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28047
  · exact u28048
  · exact u28049
  · exact u28050

def r39793 : Route 9 := (fun mask => (mask,id))

def c39793 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39793 : Upper (D 7) (R 7) [96,160,3,68,257] 13 := by
  apply FastRouting.sound _ _ [96,160,3,68,257] 13 (by decide) (choices 1) [2,8,16,128] r39793 c39793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28051
  · exact u28052
  · exact u28053
  · exact u28054

def r39794 : Route 9 := (fun mask => (mask,id))

def c39794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39794 : Upper (D 7) (R 7) [96,160,3,68,258] 13 := by
  apply FastRouting.sound _ _ [96,160,3,68,258] 13 (by decide) (choices 1) [1,8,16,128] r39794 c39794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28055
  · exact u28056
  · exact u28057
  · exact u28058

def r39795 : Route 9 := (fun mask => (mask,id))

def c39795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39795 : Upper (D 7) (R 7) [96,160,3,68,264] 13 := by
  apply FastRouting.sound _ _ [96,160,3,68,264] 13 (by decide) (choices 1) [1,2,16,128] r39795 c39795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28059
  · exact u28060
  · exact u28061
  · exact u28062

def r39796 : Route 9 := (fun mask => (mask,id))

def c39796 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39796 : Upper (D 7) (R 7) [96,160,3,68,384] 13 := by
  apply FastRouting.sound _ _ [96,160,3,68,384] 13 (by decide) (choices 1) [1,2,8,16] r39796 c39796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28063
  · exact u28064
  · exact u28065
  · exact u28066

def b39797 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(2,7)], upper := (rows 97 162 7 88 152 295 327 391 263), lower := (rows 97 162 7 88 152 32 64 128 256), losses := [] }

theorem u39797 : Upper (D 7) (R 7) [96,160,3,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39798 : Route 9 := (fun mask => (mask,id))

def c39798 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39798 : Upper (D 7) (R 7) [96,160,3,80,257] 13 := by
  apply FastRouting.sound _ _ [96,160,3,80,257] 13 (by decide) (choices 1) [2,4,8,128] r39798 c39798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28067
  · exact u28068
  · exact u28069
  · exact u28070

def r39799 : Route 9 := (fun mask => (mask,id))

def c39799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39799 : Upper (D 7) (R 7) [96,160,3,80,258] 13 := by
  apply FastRouting.sound _ _ [96,160,3,80,258] 13 (by decide) (choices 1) [1,4,8,128] r39799 c39799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28071
  · exact u28072
  · exact u28073
  · exact u28074

def r39800 : Route 9 := (fun mask => (mask,id))

def c39800 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39800 : Upper (D 7) (R 7) [96,160,3,80,260] 13 := by
  apply FastRouting.sound _ _ [96,160,3,80,260] 13 (by decide) (choices 1) [1,2,8,128] r39800 c39800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28075
  · exact u28076
  · exact u28077
  · exact u28078

def b39801 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 134, targets := 64 },{ cop := 2, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 162 7 88 280 167 199 135 391), lower := (rows 97 162 7 88 280 32 64 128 256), losses := [] }

theorem u39801 : Upper (D 7) (R 7) [96,160,3,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39802 : Route 9 := (fun mask => (mask,id))

def c39802 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39802 : Upper (D 7) (R 7) [96,160,3,80,384] 13 := by
  apply FastRouting.sound _ _ [96,160,3,80,384] 13 (by decide) (choices 1) [1,2,4,8] r39802 c39802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28079
  · exact u28080
  · exact u28081
  · exact u28082

def r39803 : Route 9 := (fun mask => (mask,id))

def c39803 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39803 : Upper (D 7) (R 7) [96,160,3,192,257] 13 := by
  apply FastRouting.sound _ _ [96,160,3,192,257] 13 (by decide) (choices 1) [2,4,8,16] r39803 c39803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28083
  · exact u28084
  · exact u28085
  · exact u28086

theorem m39804_2 : Upper (D 7) (R 7) [96,160,3,192,260,2] 13 :=
  permutation_upper _ _ _ [96,160,3,192,260,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28087

def r39804 : Route 9 := (fun mask => (mask,id))

def c39804 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39804 : Upper (D 7) (R 7) [96,160,3,192,260] 13 := by
  apply FastRouting.sound _ _ [96,160,3,192,260] 13 (by decide) (choices 1) [1,2,8,16] r39804 c39804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28087
  · exact m39804_2
  · exact u28088
  · exact u28089

theorem m39805_2 : Upper (D 7) (R 7) [96,160,3,192,264,2] 13 :=
  permutation_upper _ _ _ [96,160,3,192,264,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28090

def r39805 : Route 9 := (fun mask => (mask,id))

def c39805 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39805 : Upper (D 7) (R 7) [96,160,3,192,264] 13 := by
  apply FastRouting.sound _ _ [96,160,3,192,264] 13 (by decide) (choices 1) [1,2,4,16] r39805 c39805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28090
  · exact m39805_2
  · exact u28091
  · exact u28092

def b39806 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 13 82 434 466 402 402), lower := (rows 97 162 13 13 82 32 64 128 256), losses := [] }

theorem u39806 : Upper (D 7) (R 7) [96,160,9,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39807 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 13 208 306 338 402 274), lower := (rows 97 162 13 13 208 32 64 128 256), losses := [] }

theorem u39807 : Upper (D 7) (R 7) [96,160,9,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39808 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 13 274 242 210 210 466), lower := (rows 97 162 13 13 274 32 64 128 256), losses := [] }

theorem u39808 : Upper (D 7) (R 7) [96,160,9,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39809 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 13 336 178 210 146 402), lower := (rows 97 162 13 13 336 32 64 128 256), losses := [] }

theorem u39809 : Upper (D 7) (R 7) [96,160,9,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39810 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 13 400 114 82 210 338), lower := (rows 97 162 13 13 400 32 64 128 256), losses := [] }

theorem u39810 : Upper (D 7) (R 7) [96,160,9,5,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39811 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 162 13 14 81 434 466 402 402), lower := (rows 97 162 13 14 81 32 64 128 256), losses := [] }

theorem u39811 : Upper (D 7) (R 7) [96,160,9,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39812 : Route 9 := (fun mask => (mask,id))

def c39812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u39812 : Upper (D 7) (R 7) [96,160,9,6,66] 13 := by
  apply FastRouting.sound _ _ [96,160,9,6,66] 13 (by decide) (choices 1) [1,16,128,256] r39812 c39812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28093
  · exact u28094
  · exact u28095
  · exact u28096

theorem m39813_2 : Upper (D 7) (R 7) [96,160,9,6,192,2] 13 :=
  permutation_upper _ _ _ [96,160,9,6,192,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28097

def r39813 : Route 9 := (fun mask => (mask,id))

def c39813 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39813 : Upper (D 7) (R 7) [96,160,9,6,192] 13 := by
  apply FastRouting.sound _ _ [96,160,9,6,192] 13 (by decide) (choices 1) [1,2,16,256] r39813 c39813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28097
  · exact m39813_2
  · exact u28098
  · exact u28099

def r39814 : Route 9 := (fun mask => (mask,id))

def c39814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39814 : Upper (D 7) (R 7) [96,160,9,6,257] 13 := by
  apply FastRouting.sound _ _ [96,160,9,6,257] 13 (by decide) (choices 1) [2,16,64,128] r39814 c39814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28100
  · exact u28101
  · exact u28102
  · exact u28103

def r39815 : Route 9 := (fun mask => (mask,id))

def c39815 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39815 : Upper (D 7) (R 7) [96,160,9,6,320] 13 := by
  apply FastRouting.sound _ _ [96,160,9,6,320] 13 (by decide) (choices 1) [1,2,16,128] r39815 c39815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28104
  · exact u28105
  · exact u28106
  · exact u28107

def b39816 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 25 22 482 450 450 450), lower := (rows 97 162 13 25 22 32 64 128 256), losses := [] }

theorem u39816 : Upper (D 7) (R 7) [96,160,9,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39817 : PairBound 9 := { available := 390, camps := [{ cop := 3, region := 4, targets := 162 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 97 162 13 25 82 422 454 390 390), lower := (rows 97 162 13 25 82 32 64 128 256), losses := [] }

theorem u39817 : Upper (D 7) (R 7) [96,160,9,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39818 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 28, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 13 25 84 418 450 386 386), lower := (rows 97 162 13 25 84 32 64 128 256), losses := [] }

theorem u39818 : Upper (D 7) (R 7) [96,160,9,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39819 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 25 148 354 322 450 322), lower := (rows 97 162 13 25 148 32 64 128 256), losses := [] }

theorem u39819 : Upper (D 7) (R 7) [96,160,9,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39820 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 4, targets := 162 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 97 162 13 25 208 294 326 390 262), lower := (rows 97 162 13 25 208 32 64 128 256), losses := [] }

theorem u39820 : Upper (D 7) (R 7) [96,160,9,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39821 : PairBound 9 := { available := 198, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 25 274 230 198 198 454), lower := (rows 97 162 13 25 274 32 64 128 256), losses := [] }

theorem u39821 : Upper (D 7) (R 7) [96,160,9,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39822 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 25 276 226 194 194 450), lower := (rows 97 162 13 25 276 32 64 128 256), losses := [] }

theorem u39822 : Upper (D 7) (R 7) [96,160,9,17,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39823 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 4, targets := 162 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 97 162 13 25 336 166 198 134 390), lower := (rows 97 162 13 25 336 32 64 128 256), losses := [] }

theorem u39823 : Upper (D 7) (R 7) [96,160,9,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39824 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 25 400 102 70 198 326), lower := (rows 97 162 13 25 400 32 64 128 256), losses := [] }

theorem u39824 : Upper (D 7) (R 7) [96,160,9,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39825 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 162 13 26 81 422 454 390 390), lower := (rows 97 162 13 26 81 32 64 128 256), losses := [] }

theorem u39825 : Upper (D 7) (R 7) [96,160,9,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39826 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 162 13 26 82 421 453 389 389), lower := (rows 97 162 13 26 82 32 64 128 256), losses := [] }

theorem u39826 : Upper (D 7) (R 7) [96,160,9,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39827 : Route 9 := (fun mask => (mask,id))

def c39827 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u39827 : Upper (D 7) (R 7) [96,160,9,18,68] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,68] 13 (by decide) (choices 1) [1,2,128,256] r39827 c39827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28108
  · exact u28109
  · exact u28110
  · exact u28111

def r39828 : Route 9 := (fun mask => (mask,id))

def c39828 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39828 : Upper (D 7) (R 7) [96,160,9,18,129] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,129] 13 (by decide) (choices 1) [2,4,64,256] r39828 c39828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28112
  · exact u28113
  · exact u28114
  · exact u28115

def b39829 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 97 162 13 26 146 357 325 453 325), lower := (rows 97 162 13 26 146 32 64 128 256), losses := [] }

theorem u39829 : Upper (D 7) (R 7) [96,160,9,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39830 : Route 9 := (fun mask => (mask,id))

def c39830 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39830 : Upper (D 7) (R 7) [96,160,9,18,132] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,132] 13 (by decide) (choices 1) [1,2,64,256] r39830 c39830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28116
  · exact u28117
  · exact u28118
  · exact u28119

def r39831 : Route 9 := (fun mask => (mask,id))

def c39831 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39831 : Upper (D 7) (R 7) [96,160,9,18,192] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,192] 13 (by decide) (choices 1) [1,2,4,256] r39831 c39831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28120
  · exact u28121
  · exact u28122
  · exact u28123

def r39832 : Route 9 := (fun mask => (mask,id))

def c39832 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39832 : Upper (D 7) (R 7) [96,160,9,18,257] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,257] 13 (by decide) (choices 1) [2,4,64,128] r39832 c39832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28124
  · exact u28125
  · exact u28126
  · exact u28127

def b39833 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 162 13 26 274 229 197 197 453), lower := (rows 97 162 13 26 274 32 64 128 256), losses := [] }

theorem u39833 : Upper (D 7) (R 7) [96,160,9,18,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39834 : Route 9 := (fun mask => (mask,id))

def c39834 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39834 : Upper (D 7) (R 7) [96,160,9,18,260] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,260] 13 (by decide) (choices 1) [1,2,64,128] r39834 c39834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28128
  · exact u28129
  · exact u28130
  · exact u28131

def r39835 : Route 9 := (fun mask => (mask,id))

def c39835 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39835 : Upper (D 7) (R 7) [96,160,9,18,320] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,320] 13 (by decide) (choices 1) [1,2,4,128] r39835 c39835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28132
  · exact u28133
  · exact u28134
  · exact u28135

def r39836 : Route 9 := (fun mask => (mask,id))

def c39836 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39836 : Upper (D 7) (R 7) [96,160,9,18,384] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,384] 13 (by decide) (choices 1) [1,2,4,64] r39836 c39836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28136
  · exact u28137
  · exact u28138
  · exact u28139

def b39837 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 28, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 13 28 81 418 450 386 386), lower := (rows 97 162 13 28 81 32 64 128 256), losses := [] }

theorem u39837 : Upper (D 7) (R 7) [96,160,9,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39838 : Route 9 := (fun mask => (mask,id))

def c39838 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u39838 : Upper (D 7) (R 7) [96,160,9,20,66] 13 := by
  apply FastRouting.sound _ _ [96,160,9,20,66] 13 (by decide) (choices 1) [1,2,128,256] r39838 c39838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28140
  · exact u28141
  · exact u28142
  · exact u28143

def b39839 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 28 145 354 322 450 322), lower := (rows 97 162 13 28 145 32 64 128 256), losses := [] }

theorem u39839 : Upper (D 7) (R 7) [96,160,9,20,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u39839
end Delivery.IrregularNine14.P07
