import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0140

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26820 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 134 292 73 82 48 71 135 263), lower := (rows 41 134 292 73 82 48 64 128 256), losses := [] }

theorem u26820 : Upper (D 6) (R 6) [40,132,288,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26820 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26821 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 134 292 73 84 33 82 146 274), lower := (rows 41 134 292 73 84 33 64 128 256), losses := [] }

theorem u26821 : Upper (D 6) (R 6) [40,132,288,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26822 : Route 9 := (fun mask => (mask,id))

def c26822 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26822 : Upper (D 6) (R 6) [40,132,288,65,68,2] 13 := by
  apply FastRouting.sound _ _ [40,132,288,65,68,2] 13 (by decide) (choices 1) [1,2,16] r26822 c26822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8420
  · exact u8421
  · exact u8422

def b26823 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 134 292 73 84 48 67 131 259), lower := (rows 41 134 292 73 84 48 64 128 256), losses := [] }

theorem u26823 : Upper (D 6) (R 6) [40,132,288,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26823 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26824 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 134 292 74 19 33 84 212 340), lower := (rows 41 134 292 74 19 33 64 128 256), losses := [] }

theorem u26824 : Upper (D 6) (R 6) [40,132,288,66,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26825 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 134 292 74 19 36 81 209 337), lower := (rows 41 134 292 74 19 36 64 128 256), losses := [] }

theorem u26825 : Upper (D 6) (R 6) [40,132,288,66,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26826 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 134 292 74 19 48 69 197 325), lower := (rows 41 134 292 74 19 48 64 128 256), losses := [] }

theorem u26826 : Upper (D 6) (R 6) [40,132,288,66,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26826 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26827 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 292 74 19 96 85 149 277), lower := (rows 41 134 292 74 19 96 64 128 256), losses := [] }

theorem u26827 : Upper (D 6) (R 6) [40,132,288,66,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26828 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 41 134 292 74 21 33 82 210 338), lower := (rows 41 134 292 74 21 33 64 128 256), losses := [] }

theorem u26828 : Upper (D 6) (R 6) [40,132,288,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26829 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 134 292 74 21 34 81 209 337), lower := (rows 41 134 292 74 21 34 64 128 256), losses := [] }

theorem u26829 : Upper (D 6) (R 6) [40,132,288,66,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26830 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 41 134 292 74 21 48 67 195 323), lower := (rows 41 134 292 74 21 48 64 128 256), losses := [] }

theorem u26830 : Upper (D 6) (R 6) [40,132,288,66,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26830 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26831 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 292 74 21 96 83 147 275), lower := (rows 41 134 292 74 21 96 64 128 256), losses := [] }

theorem u26831 : Upper (D 6) (R 6) [40,132,288,66,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26832 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 134 292 74 81 33 86 150 278), lower := (rows 41 134 292 74 81 33 64 128 256), losses := [] }

theorem u26832 : Upper (D 6) (R 6) [40,132,288,66,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26833 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 134 292 74 81 34 85 149 277), lower := (rows 41 134 292 74 81 34 64 128 256), losses := [] }

theorem u26833 : Upper (D 6) (R 6) [40,132,288,66,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26834 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 134 292 74 81 36 83 147 275), lower := (rows 41 134 292 74 81 36 64 128 256), losses := [] }

theorem u26834 : Upper (D 6) (R 6) [40,132,288,66,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26835 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 134 292 74 81 48 71 135 263), lower := (rows 41 134 292 74 81 48 64 128 256), losses := [] }

theorem u26835 : Upper (D 6) (R 6) [40,132,288,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26835 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26836 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 292 74 84 33 83 147 275), lower := (rows 41 134 292 74 84 33 64 128 256), losses := [] }

theorem u26836 : Upper (D 6) (R 6) [40,132,288,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26837 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 134 292 74 84 34 81 145 273), lower := (rows 41 134 292 74 84 34 64 128 256), losses := [] }

theorem u26837 : Upper (D 6) (R 6) [40,132,288,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26838 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 41 134 292 74 84 48 67 131 259), lower := (rows 41 134 292 74 84 48 64 128 256), losses := [] }

theorem u26838 : Upper (D 6) (R 6) [40,132,288,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26838 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26839 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 292 76 19 33 82 210 338), lower := (rows 41 134 292 76 19 33 64 128 256), losses := [] }

theorem u26839 : Upper (D 6) (R 6) [40,132,288,68,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26840 : Route 9 := (fun mask => (mask,id))

def c26840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26840 : Upper (D 6) (R 6) [40,132,288,68,3,2] 13 := by
  apply FastRouting.sound _ _ [40,132,288,68,3,2] 13 (by decide) (choices 1) [1,16] r26840 c26840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8423
  · exact u8424

def r26841 : Route 9 := (fun mask => (mask,id))

def c26841 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26841 : Upper (D 6) (R 6) [40,132,288,68,3,16] 13 := by
  apply FastRouting.sound _ _ [40,132,288,68,3,16] 13 (by decide) (choices 1) [1,2] r26841 c26841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8425
  · exact u8426

def b26842 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 292 76 19 96 83 147 275), lower := (rows 41 134 292 76 19 96 64 128 256), losses := [] }

theorem u26842 : Upper (D 6) (R 6) [40,132,288,68,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26843 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 134 292 76 81 33 82 146 274), lower := (rows 41 134 292 76 81 33 64 128 256), losses := [] }

theorem u26843 : Upper (D 6) (R 6) [40,132,288,68,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26844 : Route 9 := (fun mask => (mask,id))

def c26844 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26844 : Upper (D 6) (R 6) [40,132,288,68,65,2] 13 := by
  apply FastRouting.sound _ _ [40,132,288,68,65,2] 13 (by decide) (choices 1) [1,2,16] r26844 c26844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8427
  · exact u8428
  · exact u8429

def b26845 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 134 292 76 81 48 67 131 259), lower := (rows 41 134 292 76 81 48 64 128 256), losses := [] }

theorem u26845 : Upper (D 6) (R 6) [40,132,288,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26845 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26846 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 292 76 82 33 83 147 275), lower := (rows 41 134 292 76 82 33 64 128 256), losses := [] }

theorem u26846 : Upper (D 6) (R 6) [40,132,288,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26847 : Route 9 := (fun mask => (mask,id))

def c26847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26847 : Upper (D 6) (R 6) [40,132,288,68,66,2] 13 := by
  apply FastRouting.sound _ _ [40,132,288,68,66,2] 13 (by decide) (choices 1) [1,16] r26847 c26847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8430
  · exact u8431

def b26848 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 41 134 292 76 82 48 67 131 259), lower := (rows 41 134 292 76 82 48 64 128 256), losses := [] }

theorem u26848 : Upper (D 6) (R 6) [40,132,288,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26848 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26849 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 292 88 19 33 70 198 326), lower := (rows 41 134 292 88 19 33 64 128 256), losses := [] }

theorem u26849 : Upper (D 6) (R 6) [40,132,288,80,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26850 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 41 134 292 88 19 34 69 197 325), lower := (rows 41 134 292 88 19 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 24 16 32 81 145 273), good := (rows 493 132 292 472 477 32 64 128 256) },{ target := 2, region := (rows 9 2 0 8 16 50 64 128 256), good := (rows 41 162 288 121 51 34 64 128 256) }] }

theorem u26850 : Upper (D 6) (R 6) [40,132,288,80,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26851 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 134 292 88 19 36 67 195 323), lower := (rows 41 134 292 88 19 36 64 128 256), losses := [] }

theorem u26851 : Upper (D 6) (R 6) [40,132,288,80,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26852 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 292 88 19 96 71 135 263), lower := (rows 41 134 292 88 19 96 64 128 256), losses := [] }

theorem u26852 : Upper (D 6) (R 6) [40,132,288,80,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26853 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 41 134 292 88 21 33 66 194 322), lower := (rows 41 134 292 88 21 33 64 128 256), losses := [] }

theorem u26853 : Upper (D 6) (R 6) [40,132,288,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26854 : Route 9 := (fun mask => (mask,id))

def c26854 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26854 : Upper (D 6) (R 6) [40,132,288,80,5,2] 13 := by
  apply FastRouting.sound _ _ [40,132,288,80,5,2] 13 (by decide) (choices 1) [1,2] r26854 c26854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8432
  · exact u8433

def b26855 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 292 88 21 96 67 131 259), lower := (rows 41 134 292 88 21 96 64 128 256), losses := [] }

theorem u26855 : Upper (D 6) (R 6) [40,132,288,80,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26856 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 324 11 21 34 112 240 368), lower := (rows 41 134 324 11 21 34 64 128 256), losses := [] }

theorem u26856 : Upper (D 6) (R 6) [40,132,320,3,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26857 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 41 134 324 11 21 48 98 226 354), lower := (rows 41 134 324 11 21 48 64 128 256), losses := [] }

theorem u26857 : Upper (D 6) (R 6) [40,132,320,3,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26857 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26858 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 41 134 324 11 21 96 114 178 306), lower := (rows 41 134 324 11 21 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 10 16 100 64 128 256), good := (rows 41 171 352 11 49 96 96 128 256) }] }

theorem u26858 : Upper (D 6) (R 6) [40,132,320,3,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26859 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 134 324 11 52 33 82 210 338), lower := (rows 41 134 324 11 52 33 64 128 256), losses := [] }

theorem u26859 : Upper (D 6) (R 6) [40,132,320,3,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26860 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 324 11 52 34 81 209 337), lower := (rows 41 134 324 11 52 34 64 128 256), losses := [] }

theorem u26860 : Upper (D 6) (R 6) [40,132,320,3,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26861 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 134 324 11 52 48 67 195 323), lower := (rows 41 134 324 11 52 48 64 128 256), losses := [] }

theorem u26861 : Upper (D 6) (R 6) [40,132,320,3,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26861 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26862 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 41 134 324 11 52 96 83 147 275), lower := (rows 41 134 324 11 52 96 64 128 256), losses := [] }

theorem u26862 : Upper (D 6) (R 6) [40,132,320,3,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26863 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 324 11 81 34 116 180 308), lower := (rows 41 134 324 11 81 34 64 128 256), losses := [] }

theorem u26863 : Upper (D 6) (R 6) [40,132,320,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26864 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 4, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 41 134 324 11 81 36 114 178 306), lower := (rows 41 134 324 11 81 36 64 128 256), losses := [] }

theorem u26864 : Upper (D 6) (R 6) [40,132,320,3,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26865 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 454, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 134 324 11 81 48 102 166 294), lower := (rows 41 134 324 11 81 48 64 128 256), losses := [] }

theorem u26865 : Upper (D 6) (R 6) [40,132,320,3,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26865 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26866 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 324 11 82 33 116 180 308), lower := (rows 41 134 324 11 82 33 64 128 256), losses := [] }

theorem u26866 : Upper (D 6) (R 6) [40,132,320,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26867 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 41, targets := 64 }], pairs := [(0,1),(0,6),(3,6)], upper := (rows 41 134 324 11 82 36 113 177 305), lower := (rows 41 134 324 11 82 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 38 64 128 256), good := (rows 41 164 356 41 112 36 64 128 256) }] }

theorem u26867 : Upper (D 6) (R 6) [40,132,320,3,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26868 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 134 324 11 82 48 101 165 293), lower := (rows 41 134 324 11 82 48 64 128 256), losses := [] }

theorem u26868 : Upper (D 6) (R 6) [40,132,320,3,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26868 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26869 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 324 11 112 33 86 150 278), lower := (rows 41 134 324 11 112 33 64 128 256), losses := [] }

theorem u26869 : Upper (D 6) (R 6) [40,132,320,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26870 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 324 11 112 34 85 149 277), lower := (rows 41 134 324 11 112 34 64 128 256), losses := [] }

theorem u26870 : Upper (D 6) (R 6) [40,132,320,3,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26871 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 2, region := 48, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 41 134 324 11 112 36 83 147 275), lower := (rows 41 134 324 11 112 36 64 128 256), losses := [] }

theorem u26871 : Upper (D 6) (R 6) [40,132,320,3,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26872 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 134 324 11 112 48 71 135 263), lower := (rows 41 134 324 11 112 48 64 128 256), losses := [] }

theorem u26872 : Upper (D 6) (R 6) [40,132,320,3,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26872 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26873 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 134 324 13 19 34 112 240 368), lower := (rows 41 134 324 13 19 34 64 128 256), losses := [] }

theorem u26873 : Upper (D 6) (R 6) [40,132,320,5,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26874 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 41 134 324 13 19 48 98 226 354), lower := (rows 41 134 324 13 19 48 64 128 256), losses := [] }

theorem u26874 : Upper (D 6) (R 6) [40,132,320,5,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26874 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26875 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 41, targets := 2 },{ cop := 4, region := 486, targets := 1 }], pairs := [(0,1),(1,0),(3,1)], upper := (rows 41 134 324 13 19 96 114 178 306), lower := (rows 41 134 324 13 19 96 64 128 256), losses := [] }

theorem u26875 : Upper (D 6) (R 6) [40,132,320,5,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26876 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 134 324 13 50 33 82 210 338), lower := (rows 41 134 324 13 50 33 64 128 256), losses := [] }

theorem u26876 : Upper (D 6) (R 6) [40,132,320,5,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26877 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 134 324 13 50 34 81 209 337), lower := (rows 41 134 324 13 50 34 64 128 256), losses := [] }

theorem u26877 : Upper (D 6) (R 6) [40,132,320,5,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26878 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 134 324 13 50 48 67 195 323), lower := (rows 41 134 324 13 50 48 64 128 256), losses := [] }

theorem u26878 : Upper (D 6) (R 6) [40,132,320,5,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26878 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26879 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 41, targets := 2 }], pairs := [(0,1),(3,1),(4,0)], upper := (rows 41 134 324 13 50 96 83 147 275), lower := (rows 41 134 324 13 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 100 64 128 256), good := (rows 40 182 356 44 50 96 96 128 256) }] }

theorem u26879 : Upper (D 6) (R 6) [40,132,320,5,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u26879
end Delivery.IrregularNine14.P06
