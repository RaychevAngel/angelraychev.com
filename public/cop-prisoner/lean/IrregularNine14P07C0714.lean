import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0616
import IrregularNine14P07C0617
import IrregularNine14P07C0618
import IrregularNine14P07C0619

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b42840 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 38 280 211 227 195 195 451), lower := (rows 37 74 38 280 16 32 64 128 256), losses := [] }

theorem u42840 : Upper (D 7) (R 7) [36,72,34,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42841 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 38 392 211 243 211 211 467), lower := (rows 37 74 38 392 16 32 64 128 256), losses := [] }

theorem u42841 : Upper (D 7) (R 7) [36,72,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42842 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 52 137 467 483 451 451 451), lower := (rows 37 74 52 137 16 32 64 128 256), losses := [] }

theorem u42842 : Upper (D 7) (R 7) [36,72,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42843 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 52 138 467 483 451 451 451), lower := (rows 37 74 52 138 16 32 64 128 256), losses := [] }

theorem u42843 : Upper (D 7) (R 7) [36,72,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42844 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 52 265 211 227 195 195 451), lower := (rows 37 74 52 265 16 32 64 128 256), losses := [] }

theorem u42844 : Upper (D 7) (R 7) [36,72,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42845 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 52 266 211 227 195 195 451), lower := (rows 37 74 52 266 16 32 64 128 256), losses := [] }

theorem u42845 : Upper (D 7) (R 7) [36,72,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42846 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 52 392 211 227 195 195 451), lower := (rows 37 74 52 392 16 32 64 128 256), losses := [] }

theorem u42846 : Upper (D 7) (R 7) [36,72,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42847 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 74 69 41 402 434 466 402 402), lower := (rows 37 74 69 41 16 32 64 128 256), losses := [] }

theorem u42847 : Upper (D 7) (R 7) [36,72,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42848 : PairBound 9 := { available := 403, camps := [], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 69 42 403 435 467 403 403), lower := (rows 37 74 69 42 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 9 16 32 64 128 256), good := (rows 46 74 78 42 16 32 64 128 256) },{ target := 1, region := (rows 9 0 6 8 16 32 64 128 256), good := (rows 37 77 69 45 16 32 64 128 256) }] }

theorem u42848 : Upper (D 7) (R 7) [36,72,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42849 : Route 9 := (fun mask => (mask,id))

def c42849 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42849 : Upper (D 7) (R 7) [36,72,65,48] 13 := by
  apply FastRouting.sound _ _ [36,72,65,48] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42849 c42849
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36966
  · exact u36967
  · exact u36968
  · exact u36969
  · exact u36970
  · exact u36971

def r42850 : Route 9 := (fun mask => (mask,id))

def c42850 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42850 : Upper (D 7) (R 7) [36,72,65,129] 13 := by
  apply FastRouting.sound _ _ [36,72,65,129] 13 (by decide) (choices 2) [34,130,160,258,288,384] r42850 c42850
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36972
  · exact u36973
  · exact u36974
  · exact u36975
  · exact u36976
  · exact u36977

def r42851 : Route 9 := (fun mask => (mask,id))

def c42851 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42851 : Upper (D 7) (R 7) [36,72,65,130] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r42851 c42851
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36978
  · exact u36979
  · exact u36980
  · exact u36981
  · exact u36982
  · exact u36983
  · exact u36984
  · exact u36985
  · exact u36986
  · exact u36987

def r42852 : Route 9 := (fun mask => (mask,id))

def c42852 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42852 : Upper (D 7) (R 7) [36,72,65,144] 13 := by
  apply FastRouting.sound _ _ [36,72,65,144] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r42852 c42852
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36988
  · exact u36989
  · exact u36990
  · exact u36991
  · exact u36992
  · exact u36993
  · exact u36994
  · exact u36995
  · exact u36996
  · exact u36997

def r42853 : Route 9 := (fun mask => (mask,id))

def c42853 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42853 : Upper (D 7) (R 7) [36,72,65,160] 13 := by
  apply FastRouting.sound _ _ [36,72,65,160] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42853 c42853
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36998
  · exact u36999
  · exact u37000
  · exact u37001
  · exact u37002
  · exact u37003

def r42854 : Route 9 := (fun mask => (mask,id))

def c42854 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42854 : Upper (D 7) (R 7) [36,72,65,257] 13 := by
  apply FastRouting.sound _ _ [36,72,65,257] 13 (by decide) (choices 2) [34,130,160] r42854 c42854
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37004
  · exact u37005
  · exact u37006

def r42855 : Route 9 := (fun mask => (mask,id))

def c42855 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42855 : Upper (D 7) (R 7) [36,72,65,258] 13 := by
  apply FastRouting.sound _ _ [36,72,65,258] 13 (by decide) (choices 2) [3,33,34,129,130,160] r42855 c42855
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37007
  · exact u37008
  · exact u37009
  · exact u37010
  · exact u37011
  · exact u37012

def r42856 : Route 9 := (fun mask => (mask,id))

def c42856 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42856 : Upper (D 7) (R 7) [36,72,65,272] 13 := by
  apply FastRouting.sound _ _ [36,72,65,272] 13 (by decide) (choices 2) [3,33,34,129,130,160] r42856 c42856
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37013
  · exact u37014
  · exact u37015
  · exact u37016
  · exact u37017
  · exact u37018

def r42857 : Route 9 := (fun mask => (mask,id))

def c42857 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42857 : Upper (D 7) (R 7) [36,72,65,288] 13 := by
  apply FastRouting.sound _ _ [36,72,65,288] 13 (by decide) (choices 2) [3,129,130] r42857 c42857
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37019
  · exact u37020
  · exact u37021

def r42858 : Route 9 := (fun mask => (mask,id))

def c42858 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42858 : Upper (D 7) (R 7) [36,72,65,384] 13 := by
  apply FastRouting.sound _ _ [36,72,65,384] 13 (by decide) (choices 2) [3,33,34,129,130,160] r42858 c42858
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37022
  · exact u37023
  · exact u37024
  · exact u37025
  · exact u37026
  · exact u37027

def b42859 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 37 74 70 56 403 419 451 387 387), lower := (rows 37 74 70 56 16 32 64 128 256), losses := [] }

theorem u42859 : Upper (D 7) (R 7) [36,72,66,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42860 : PairBound 9 := { available := 435, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 37 74 70 137 435 435 499 435 435), lower := (rows 37 74 70 137 16 32 64 128 256), losses := [] }

theorem u42860 : Upper (D 7) (R 7) [36,72,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42861 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 37 74 70 138 433 433 497 433 433), lower := (rows 37 74 70 138 16 32 64 128 256), losses := [] }

theorem u42861 : Upper (D 7) (R 7) [36,72,66,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42862 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 37 74 70 152 435 419 483 419 419), lower := (rows 37 74 70 152 16 32 64 128 256), losses := [] }

theorem u42862 : Upper (D 7) (R 7) [36,72,66,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42863 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 37 74 70 168 403 435 467 403 403), lower := (rows 37 74 70 168 16 32 64 128 256), losses := [] }

theorem u42863 : Upper (D 7) (R 7) [36,72,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42864 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 37 74 70 265 179 179 243 179 435), lower := (rows 37 74 70 265 16 32 64 128 256), losses := [] }

theorem u42864 : Upper (D 7) (R 7) [36,72,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42865 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 37 74 70 266 177 177 241 177 433), lower := (rows 37 74 70 266 16 32 64 128 256), losses := [] }

theorem u42865 : Upper (D 7) (R 7) [36,72,66,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42866 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 37 74 70 280 179 163 227 163 419), lower := (rows 37 74 70 280 16 32 64 128 256), losses := [] }

theorem u42866 : Upper (D 7) (R 7) [36,72,66,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42867 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 37 74 70 296 147 179 211 147 403), lower := (rows 37 74 70 296 16 32 64 128 256), losses := [] }

theorem u42867 : Upper (D 7) (R 7) [36,72,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42868 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 37 74 70 392 179 179 243 179 435), lower := (rows 37 74 70 392 16 32 64 128 256), losses := [] }

theorem u42868 : Upper (D 7) (R 7) [36,72,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42869 : Route 9 := (fun mask => (mask,id))

def c42869 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42869 : Upper (D 7) (R 7) [36,72,80,129] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r42869 c42869
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37028
  · exact u37029
  · exact u37030
  · exact u37031
  · exact u37032
  · exact u37033
  · exact u37034
  · exact u37035
  · exact u37036
  · exact u37037

def r42870 : Route 9 := (fun mask => (mask,id))

def c42870 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42870 : Upper (D 7) (R 7) [36,72,80,130] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r42870 c42870
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37038
  · exact u37039
  · exact u37040
  · exact u37041
  · exact u37042
  · exact u37043
  · exact u37044
  · exact u37045
  · exact u37046
  · exact u37047

def r42871 : Route 9 := (fun mask => (mask,id))

def c42871 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42871 : Upper (D 7) (R 7) [36,72,80,160] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42871 c42871
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37048
  · exact u37049
  · exact u37050
  · exact u37051
  · exact u37052
  · exact u37053

def r42872 : Route 9 := (fun mask => (mask,id))

def c42872 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42872 : Upper (D 7) (R 7) [36,72,80,257] 13 := by
  apply FastRouting.sound _ _ [36,72,80,257] 13 (by decide) (choices 2) [3,33,34,129,130,160] r42872 c42872
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37054
  · exact u37055
  · exact u37056
  · exact u37057
  · exact u37058
  · exact u37059

def r42873 : Route 9 := (fun mask => (mask,id))

def c42873 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42873 : Upper (D 7) (R 7) [36,72,80,258] 13 := by
  apply FastRouting.sound _ _ [36,72,80,258] 13 (by decide) (choices 2) [3,33,34,129,130,160] r42873 c42873
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37060
  · exact u37061
  · exact u37062
  · exact u37063
  · exact u37064
  · exact u37065

def r42874 : Route 9 := (fun mask => (mask,id))

def c42874 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42874 : Upper (D 7) (R 7) [36,72,80,288] 13 := by
  apply FastRouting.sound _ _ [36,72,80,288] 13 (by decide) (choices 2) [3,129,130] r42874 c42874
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37066
  · exact u37067
  · exact u37068

def r42875 : Route 9 := (fun mask => (mask,id))

def c42875 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42875 : Upper (D 7) (R 7) [36,72,80,384] 13 := by
  apply FastRouting.sound _ _ [36,72,80,384] 13 (by decide) (choices 2) [3,33,34,129,130,160] r42875 c42875
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37069
  · exact u37070
  · exact u37071
  · exact u37072
  · exact u37073
  · exact u37074

def b42876 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 100 137 403 435 467 403 403), lower := (rows 37 74 100 137 16 32 64 128 256), losses := [] }

theorem u42876 : Upper (D 7) (R 7) [36,72,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42877 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 100 138 403 435 467 403 403), lower := (rows 37 74 100 138 16 32 64 128 256), losses := [] }

theorem u42877 : Upper (D 7) (R 7) [36,72,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42878 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 100 152 403 419 451 387 387), lower := (rows 37 74 100 152 16 32 64 128 256), losses := [] }

theorem u42878 : Upper (D 7) (R 7) [36,72,96,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42879 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 100 265 147 179 211 147 403), lower := (rows 37 74 100 265 16 32 64 128 256), losses := [] }

theorem u42879 : Upper (D 7) (R 7) [36,72,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42880 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 100 266 147 179 211 147 403), lower := (rows 37 74 100 266 16 32 64 128 256), losses := [] }

theorem u42880 : Upper (D 7) (R 7) [36,72,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42881 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 100 280 147 163 195 131 387), lower := (rows 37 74 100 280 16 32 64 128 256), losses := [] }

theorem u42881 : Upper (D 7) (R 7) [36,72,96,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42882 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 100 392 147 179 211 147 403), lower := (rows 37 74 100 392 16 32 64 128 256), losses := [] }

theorem u42882 : Upper (D 7) (R 7) [36,72,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42883 : PairBound 9 := { available := 370, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 37 74 133 137 370 370 370 498 370), lower := (rows 37 74 133 137 16 32 64 128 256), losses := [] }

theorem u42883 : Upper (D 7) (R 7) [36,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42884_65 : Upper (D 7) (R 7) [36,72,129,130,65] 13 :=
  permutation_upper _ _ _ [36,72,129,130,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37077

theorem m42884_66 : Upper (D 7) (R 7) [36,72,129,130,66] 13 :=
  permutation_upper _ _ _ [36,72,129,130,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37076

theorem m42884_258 : Upper (D 7) (R 7) [36,72,129,130,258] 13 :=
  permutation_upper _ _ _ [36,72,129,130,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37079

theorem m42884_320 : Upper (D 7) (R 7) [36,72,129,130,320] 13 :=
  permutation_upper _ _ _ [36,72,129,130,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37080

def r42884 : Route 9 := (fun mask => (mask,id))

def c42884 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42884 : Upper (D 7) (R 7) [36,72,129,130] 13 := by
  apply FastRouting.sound _ _ [36,72,129,130] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r42884 c42884
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37075
  · exact u37076
  · exact u37077
  · exact m42884_65
  · exact m42884_66
  · exact u37078
  · exact u37079
  · exact m42884_258
  · exact u37080
  · exact m42884_320

def r42885 : Route 9 := (fun mask => (mask,id))

def c42885 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42885 : Upper (D 7) (R 7) [36,72,129,144] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r42885 c42885
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37081
  · exact u37082
  · exact u37083
  · exact u37084
  · exact u37085
  · exact u37086
  · exact u37087
  · exact u37088
  · exact u37089
  · exact u37090

def b42886 : PairBound 9 := { available := 339, camps := [{ cop := 3, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 168 339 371 339 467 339), lower := (rows 37 74 133 168 16 32 64 128 256), losses := [] }

theorem u42886 : Upper (D 7) (R 7) [36,72,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42887 : PairBound 9 := { available := 307, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 133 200 307 307 371 435 307), lower := (rows 37 74 133 200 16 32 64 128 256), losses := [] }

theorem u42887 : Upper (D 7) (R 7) [36,72,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42888 : Route 9 := (fun mask => (mask,id))

def c42888 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42888 : Upper (D 7) (R 7) [36,72,129,257] 13 := by
  apply FastRouting.sound _ _ [36,72,129,257] 13 (by decide) (choices 2) [34,66,96,130,160,192] r42888 c42888
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37091
  · exact u37092
  · exact u37093
  · exact u37094
  · exact u37095
  · exact u37096

def r42889 : Route 9 := (fun mask => (mask,id))

def c42889 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42889 : Upper (D 7) (R 7) [36,72,129,258] 13 := by
  apply FastRouting.sound _ _ [36,72,129,258] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42889 c42889
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37097
  · exact u37098
  · exact u37099
  · exact u37100
  · exact u37101
  · exact u37102
  · exact u37103
  · exact u37104
  · exact u37105
  · exact u37106

def r42890 : Route 9 := (fun mask => (mask,id))

def c42890 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42890 : Upper (D 7) (R 7) [36,72,129,272] 13 := by
  apply FastRouting.sound _ _ [36,72,129,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42890 c42890
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37107
  · exact u37108
  · exact u37109
  · exact u37110
  · exact u37111
  · exact u37112
  · exact u37113
  · exact u37114
  · exact u37115
  · exact u37116

def r42891 : Route 9 := (fun mask => (mask,id))

def c42891 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42891 : Upper (D 7) (R 7) [36,72,129,288] 13 := by
  apply FastRouting.sound _ _ [36,72,129,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42891 c42891
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37117
  · exact u37118
  · exact u37119
  · exact u37120
  · exact u37121
  · exact u37122

def b42892 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 181, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 133 328 179 179 243 179 435), lower := (rows 37 74 133 328 16 32 64 128 256), losses := [] }

theorem u42892 : Upper (D 7) (R 7) [36,72,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42893 : Route 9 := (fun mask => (mask,id))

def c42893 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42893 : Upper (D 7) (R 7) [36,72,129,384] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384] 13 (by decide) (choices 2) [3,33,34,65,66,96] r42893 c42893
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37123
  · exact u37124
  · exact u37125
  · exact u37126
  · exact u37127
  · exact u37128

theorem m42894_65 : Upper (D 7) (R 7) [36,72,130,129,65] 13 :=
  permutation_upper _ _ _ [36,72,130,129,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37131

theorem m42894_66 : Upper (D 7) (R 7) [36,72,130,129,66] 13 :=
  permutation_upper _ _ _ [36,72,130,129,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37130

theorem m42894_258 : Upper (D 7) (R 7) [36,72,130,129,258] 13 :=
  permutation_upper _ _ _ [36,72,130,129,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37133

theorem m42894_320 : Upper (D 7) (R 7) [36,72,130,129,320] 13 :=
  permutation_upper _ _ _ [36,72,130,129,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37134

def r42894 : Route 9 := (fun mask => (mask,id))

def c42894 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42894 : Upper (D 7) (R 7) [36,72,130,129] 13 := by
  apply FastRouting.sound _ _ [36,72,130,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r42894 c42894
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37129
  · exact u37130
  · exact u37131
  · exact m42894_65
  · exact m42894_66
  · exact u37132
  · exact u37133
  · exact m42894_258
  · exact u37134
  · exact m42894_320

def r42895 : Route 9 := (fun mask => (mask,id))

def c42895 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42895 : Upper (D 7) (R 7) [36,72,130,144] 13 := by
  apply FastRouting.sound _ _ [36,72,130,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r42895 c42895
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37135
  · exact u37136
  · exact u37137
  · exact u37138
  · exact u37139
  · exact u37140
  · exact u37141
  · exact u37142
  · exact u37143
  · exact u37144

def r42896 : Route 9 := (fun mask => (mask,id))

def c42896 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 2 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42896 : Upper (D 7) (R 7) [36,72,130,160] 13 := by
  apply FastRouting.sound _ _ [36,72,130,160] 13 (by decide) (choices 2) [3,65,66,257,258,320] r42896 c42896
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37145
  · exact u37146
  · exact u37147
  · exact u37148
  · exact u37149
  · exact u37150

def b42897 : PairBound 9 := { available := 307, camps := [{ cop := 3, region := 6, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 74 134 200 307 307 371 435 307), lower := (rows 37 74 134 200 16 32 64 128 256), losses := [] }

theorem u42897 : Upper (D 7) (R 7) [36,72,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42898 : Route 9 := (fun mask => (mask,id))

def c42898 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42898 : Upper (D 7) (R 7) [36,72,130,257] 13 := by
  apply FastRouting.sound _ _ [36,72,130,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42898 c42898
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37151
  · exact u37152
  · exact u37153
  · exact u37154
  · exact u37155
  · exact u37156
  · exact u37157
  · exact u37158
  · exact u37159
  · exact u37160

def r42899 : Route 9 := (fun mask => (mask,id))

def c42899 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42899 : Upper (D 7) (R 7) [36,72,130,258] 13 := by
  apply FastRouting.sound _ _ [36,72,130,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42899 c42899
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37161
  · exact u37162
  · exact u37163
  · exact u37164
  · exact u37165
  · exact u37166

#print axioms u42899
end Delivery.IrregularNine14.P07
