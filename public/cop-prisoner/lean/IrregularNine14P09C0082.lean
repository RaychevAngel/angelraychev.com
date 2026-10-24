import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0027
import IrregularNine14P09C0028

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r4920 : Route 9 := (fun mask => (mask,id))

def c4920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4920 : Upper (D 9) (R 9) [34,68,384,129,288,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,288,1] 13 (by decide) (choices 1) [8,16] r4920 c4920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1666
  · exact u1667

def r4921 : Route 9 := (fun mask => (mask,id))

def c4921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4921 : Upper (D 9) (R 9) [34,68,384,129,288,8] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,288,8] 13 (by decide) (choices 1) [1,16] r4921 c4921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1668
  · exact u1669

def b4922 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 388 137 304 48 73 201 329), lower := (rows 35 70 388 137 304 48 64 128 256), losses := [] }

theorem u4922 : Upper (D 9) (R 9) [34,68,384,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4922 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4923 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 137 304 96 89 153 281), lower := (rows 35 70 388 137 304 96 64 128 256), losses := [] }

theorem u4923 : Upper (D 9) (R 9) [34,68,384,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4923 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4924 : Route 9 := (fun mask => (mask,id))

def c4924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4924 : Upper (D 9) (R 9) [34,68,384,129,320,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,320,1] 13 (by decide) (choices 1) [8,16,32] r4924 c4924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1670
  · exact u1671
  · exact u1672

def r4925 : Route 9 := (fun mask => (mask,id))

def c4925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4925 : Upper (D 9) (R 9) [34,68,384,129,320,8] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,320,8] 13 (by decide) (choices 1) [1,16,32] r4925 c4925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1673
  · exact u1674
  · exact u1675

def b4926 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 0, region := 136, targets := 256 },{ cop := 3, region := 368, targets := 128 }], pairs := [(2,6),(3,6),(3,8),(4,7)], upper := (rows 35 70 388 137 336 48 105 169 297), lower := (rows 35 70 388 137 336 48 64 128 256), losses := [] }

theorem u4926 : Upper (D 9) (R 9) [34,68,384,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4926 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4927 : Route 9 := (fun mask => (mask,id))

def c4927 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4927 : Upper (D 9) (R 9) [34,68,384,144,288,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144,288,1] 13 (by decide) (choices 1) [1,8] r4927 c4927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1676
  · exact u1677

def b4928 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 35 70 388 152 304 40 65 193 321), lower := (rows 35 70 388 152 304 40 64 128 256), losses := [] }

theorem u4928 : Upper (D 9) (R 9) [34,68,384,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4928 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4929 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 152 304 96 73 137 265), lower := (rows 35 70 388 152 304 96 64 128 256), losses := [] }

theorem u4929 : Upper (D 9) (R 9) [34,68,384,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4929 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4930 : Route 9 := (fun mask => (mask,id))

def c4930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4930 : Upper (D 9) (R 9) [34,68,384,144,320,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144,320,1] 13 (by decide) (choices 1) [1,8,32] r4930 c4930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1678
  · exact u1679
  · exact u1680

def r4931 : Route 9 := (fun mask => (mask,id))

def c4931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4931 : Upper (D 9) (R 9) [34,68,384,144,320,8] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144,320,8] 13 (by decide) (choices 1) [1,32] r4931 c4931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1681
  · exact u1682

def r4932 : Route 9 := (fun mask => (mask,id))

def c4932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4932 : Upper (D 9) (R 9) [34,68,384,160,320,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,160,320,1] 13 (by decide) (choices 1) [1,8,16] r4932 c4932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1683
  · exact u1684
  · exact u1685

def b4933 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 35 70 388 168 336 40 81 145 273), lower := (rows 35 70 388 168 336 40 64 128 256), losses := [] }

theorem u4933 : Upper (D 9) (R 9) [34,68,384,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4933 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4934 : Route 9 := (fun mask => (mask,id))

def c4934 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4934 : Upper (D 9) (R 9) [34,68,384,160,320,16] 13 := by
  apply FastRouting.sound _ _ [34,68,384,160,320,16] 13 (by decide) (choices 1) [1,8] r4934 c4934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1686
  · exact u1687

def b4935 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 61, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,7)], upper := (rows 35 194 13 28 112 33 448 384 384), lower := (rows 35 194 13 28 112 33 64 128 256), losses := [] }

theorem u4935 : Upper (D 9) (R 9) [34,192,9,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4935 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4936 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 61, targets := 256 },{ cop := 0, region := 348, targets := 128 }], pairs := [(0,8),(2,7),(2,8),(3,8),(4,8)], upper := (rows 35 194 13 28 112 160 321 385 257), lower := (rows 35 194 13 28 112 160 64 128 256), losses := [] }

theorem u4936 : Upper (D 9) (R 9) [34,192,9,20,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4936 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4937 : Route 9 := (fun mask => (mask,id))

def c4937 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4937 : Upper (D 9) (R 9) [34,192,9,20,96,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20,96,256] 13 (by decide) (choices 1) [1,128,256] r4937 c4937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1688
  · exact u1689
  · exact u1690

def b4938 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(1,0),(4,0)], upper := (rows 35 194 13 28 304 33 448 448 448), lower := (rows 35 194 13 28 304 33 64 128 256), losses := [] }

theorem u4938 : Upper (D 9) (R 9) [34,192,9,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4938 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4939 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 28 304 96 449 385 385), lower := (rows 35 194 13 28 304 96 64 128 256), losses := [] }

theorem u4939 : Upper (D 9) (R 9) [34,192,9,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4939 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4940 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 13 28 304 288 193 193 449), lower := (rows 35 194 13 28 304 288 64 128 256), losses := [] }

theorem u4940 : Upper (D 9) (R 9) [34,192,9,20,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4940 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4941 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 1, region := 33, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,0),(4,0)], upper := (rows 35 194 13 28 336 33 480 416 416), lower := (rows 35 194 13 28 336 33 64 128 256), losses := [] }

theorem u4941 : Upper (D 9) (R 9) [34,192,9,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4941 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4942 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 256 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 28 336 160 353 417 289), lower := (rows 35 194 13 28 336 160 64 128 256), losses := [] }

theorem u4942 : Upper (D 9) (R 9) [34,192,9,20,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4942 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4943 : Route 9 := (fun mask => (mask,id))

def c4943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4943 : Upper (D 9) (R 9) [34,192,9,20,320,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20,320,256] 13 (by decide) (choices 1) [1,32,128] r4943 c4943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1691
  · exact u1692
  · exact u1693

def b4944 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 61, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,7)], upper := (rows 35 194 13 56 84 33 448 384 384), lower := (rows 35 194 13 56 84 33 64 128 256), losses := [] }

theorem u4944 : Upper (D 9) (R 9) [34,192,9,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4944 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4945 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 61, targets := 256 },{ cop := 0, region := 348, targets := 128 }], pairs := [(0,8),(2,7),(2,8),(3,8),(4,8)], upper := (rows 35 194 13 56 84 160 321 385 257), lower := (rows 35 194 13 56 84 160 64 128 256), losses := [] }

theorem u4945 : Upper (D 9) (R 9) [34,192,9,48,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4945 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4946 : Route 9 := (fun mask => (mask,id))

def c4946 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4946 : Upper (D 9) (R 9) [34,192,9,48,68,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,68,256] 13 (by decide) (choices 1) [1,128,256] r4946 c4946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1694
  · exact u1695
  · exact u1696

def b4947 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 44, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6)], upper := (rows 35 194 13 56 273 36 448 448 448), lower := (rows 35 194 13 56 273 36 64 128 256), losses := [] }

theorem u4947 : Upper (D 9) (R 9) [34,192,9,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4947 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4948 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 56 273 96 452 388 388), lower := (rows 35 194 13 56 273 96 64 128 256), losses := [] }

theorem u4948 : Upper (D 9) (R 9) [34,192,9,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4948 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4949 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 44, targets := 192 },{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 56 273 288 196 196 452), lower := (rows 35 194 13 56 273 288 64 128 256), losses := [] }

theorem u4949 : Upper (D 9) (R 9) [34,192,9,48,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4949 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4950 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 56 276 33 448 448 448), lower := (rows 35 194 13 56 276 33 64 128 256), losses := [] }

theorem u4950 : Upper (D 9) (R 9) [34,192,9,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4950 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4951 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 56 276 96 449 385 385), lower := (rows 35 194 13 56 276 96 64 128 256), losses := [] }

theorem u4951 : Upper (D 9) (R 9) [34,192,9,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4951 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4952 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 35 194 13 56 276 288 193 193 449), lower := (rows 35 194 13 56 276 288 64 128 256), losses := [] }

theorem u4952 : Upper (D 9) (R 9) [34,192,9,48,260,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4952 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4953 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 56 336 33 452 388 388), lower := (rows 35 194 13 56 336 33 64 128 256), losses := [] }

theorem u4953 : Upper (D 9) (R 9) [34,192,9,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4953 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4954 : Route 9 := (fun mask => (mask,id))

def c4954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4954 : Upper (D 9) (R 9) [34,192,9,48,320,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,320,4] 13 (by decide) (choices 1) [1,128,256] r4954 c4954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1697
  · exact u1698
  · exact u1699

def b4955 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 56 336 160 325 389 261), lower := (rows 35 194 13 56 336 160 64 128 256), losses := [] }

theorem u4955 : Upper (D 9) (R 9) [34,192,9,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4955 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4956 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 35 194 13 56 336 288 197 133 389), lower := (rows 35 194 13 56 336 288 64 128 256), losses := [] }

theorem u4956 : Upper (D 9) (R 9) [34,192,9,48,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4956 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4957 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 61, targets := 256 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 13 76 176 33 336 400 272), lower := (rows 35 194 13 76 176 33 64 128 256), losses := [] }

theorem u4957 : Upper (D 9) (R 9) [34,192,9,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4957 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4958 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 61, targets := 256 }], pairs := [(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 13 76 176 48 321 385 257), lower := (rows 35 194 13 76 176 48 64 128 256), losses := [] }

theorem u4958 : Upper (D 9) (R 9) [34,192,9,68,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4958 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4959 : Route 9 := (fun mask => (mask,id))

def c4959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4959 : Upper (D 9) (R 9) [34,192,9,68,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,160,256] 13 (by decide) (choices 1) [1,16,256] r4959 c4959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1700
  · exact u1701
  · exact u1702

def b4960 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,6)], upper := (rows 35 194 13 76 273 48 480 416 416), lower := (rows 35 194 13 76 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 55 4 12 16 48 113 177 305), good := (rows 482 194 462 78 498 498 64 128 256) }] }

theorem u4960 : Upper (D 9) (R 9) [34,192,9,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4960 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4961 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 45, targets := 256 }], pairs := [(0,8),(2,7),(2,8),(3,7),(4,7)], upper := (rows 35 194 13 76 273 160 368 432 304), lower := (rows 35 194 13 76 273 160 64 128 256), losses := [] }

theorem u4961 : Upper (D 9) (R 9) [34,192,9,68,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4961 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4962 : Route 9 := (fun mask => (mask,id))

def c4962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4962 : Upper (D 9) (R 9) [34,192,9,68,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,257,256] 13 (by decide) (choices 1) [16,32,128] r4962 c4962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1703
  · exact u1704
  · exact u1705

def b4963 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 45, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,7)], upper := (rows 35 194 13 76 304 33 464 400 400), lower := (rows 35 194 13 76 304 33 64 128 256), losses := [] }

theorem u4963 : Upper (D 9) (R 9) [34,192,9,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4963 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4964 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 194 13 76 304 48 449 385 385), lower := (rows 35 194 13 76 304 48 64 128 256), losses := [] }

theorem u4964 : Upper (D 9) (R 9) [34,192,9,68,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4964 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4965 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 45, targets := 256 }], pairs := [(0,8),(2,7),(2,8),(3,7),(4,7)], upper := (rows 35 194 13 76 304 160 337 401 273), lower := (rows 35 194 13 76 304 160 64 128 256), losses := [] }

theorem u4965 : Upper (D 9) (R 9) [34,192,9,68,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4965 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4966 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 13 76 304 288 209 145 401), lower := (rows 35 194 13 76 304 288 64 128 256), losses := [] }

theorem u4966 : Upper (D 9) (R 9) [34,192,9,68,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4966 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4967 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 45, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,7)], upper := (rows 35 194 13 76 400 33 368 432 304), lower := (rows 35 194 13 76 400 33 64 128 256), losses := [] }

theorem u4967 : Upper (D 9) (R 9) [34,192,9,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4967 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4968 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,6)], upper := (rows 35 194 13 76 400 48 353 417 289), lower := (rows 35 194 13 76 400 48 64 128 256), losses := [] }

theorem u4968 : Upper (D 9) (R 9) [34,192,9,68,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4968 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4969 : Route 9 := (fun mask => (mask,id))

def c4969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4969 : Upper (D 9) (R 9) [34,192,9,68,384,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,384,256] 13 (by decide) (choices 1) [1,16,32] r4969 c4969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1706
  · exact u1707
  · exact u1708

def b4970 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 61, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,7)], upper := (rows 35 194 13 88 52 33 448 384 384), lower := (rows 35 194 13 88 52 33 64 128 256), losses := [] }

theorem u4970 : Upper (D 9) (R 9) [34,192,9,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4970 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4971 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 61, targets := 256 },{ cop := 0, region := 348, targets := 128 }], pairs := [(0,8),(2,7),(2,8),(3,8),(4,8)], upper := (rows 35 194 13 88 52 160 321 385 257), lower := (rows 35 194 13 88 52 160 64 128 256), losses := [] }

theorem u4971 : Upper (D 9) (R 9) [34,192,9,80,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4971 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4972 : Route 9 := (fun mask => (mask,id))

def c4972 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4972 : Upper (D 9) (R 9) [34,192,9,80,36,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,36,256] 13 (by decide) (choices 1) [1,128,256] r4972 c4972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1709
  · exact u1710
  · exact u1711

def b4973 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 61, targets := 256 }], pairs := [(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 13 88 145 36 352 416 288), lower := (rows 35 194 13 88 145 36 64 128 256), losses := [] }

theorem u4973 : Upper (D 9) (R 9) [34,192,9,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4973 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4974 : Route 9 := (fun mask => (mask,id))

def c4974 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4974 : Upper (D 9) (R 9) [34,192,9,80,129,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,129,256] 13 (by decide) (choices 1) [4,32,256] r4974 c4974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1712
  · exact u1713
  · exact u1714

def b4975 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 61, targets := 256 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,8),(1,0),(2,8),(3,8),(4,8)], upper := (rows 35 194 13 88 148 33 352 416 288), lower := (rows 35 194 13 88 148 33 64 128 256), losses := [] }

theorem u4975 : Upper (D 9) (R 9) [34,192,9,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4975 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4976 : Route 9 := (fun mask => (mask,id))

def c4976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4976 : Upper (D 9) (R 9) [34,192,9,80,132,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,132,256] 13 (by decide) (choices 1) [1,32,256] r4976 c4976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1715
  · exact u1716
  · exact u1717

def b4977 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 61, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 13 88 176 33 324 388 260), lower := (rows 35 194 13 88 176 33 64 128 256), losses := [] }

theorem u4977 : Upper (D 9) (R 9) [34,192,9,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4977 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4978 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 61, targets := 256 }], pairs := [(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 13 88 176 36 321 385 257), lower := (rows 35 194 13 88 176 36 64 128 256), losses := [] }

theorem u4978 : Upper (D 9) (R 9) [34,192,9,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4978 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4979 : Route 9 := (fun mask => (mask,id))

def c4979 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4979 : Upper (D 9) (R 9) [34,192,9,80,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,160,256] 13 (by decide) (choices 1) [1,4,256] r4979 c4979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1718
  · exact u1719
  · exact u1720

#print axioms u4979
end Delivery.IrregularNine14.P09
