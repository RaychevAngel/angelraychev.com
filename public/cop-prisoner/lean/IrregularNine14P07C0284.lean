import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0067
import IrregularNine14P07C0068

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17040 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 456, targets := 32 }], pairs := [(0,5),(1,7),(3,5),(4,7)], upper := (rows 13 98 52 392 19 160 67 195 323), lower := (rows 13 98 52 392 19 160 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 28 16 0 80 144 272), good := (rows 13 66 477 392 475 128 64 128 256) },{ target := 7, region := (rows 1 6 4 8 17 32 81 0 273), good := (rows 351 98 374 264 339 32 64 0 256) }] }

theorem u17040 : Upper (D 7) (R 7) [12,96,48,384,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17041 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 392, targets := 33 },{ cop := 4, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(3,0),(3,5)], upper := (rows 13 98 52 392 81 33 194 130 386), lower := (rows 13 98 52 392 81 33 64 128 256), losses := [] }

theorem u17041 : Upper (D 7) (R 7) [12,96,48,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17042 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 392 81 34 195 131 387), lower := (rows 13 98 52 392 81 34 64 128 256), losses := [] }

theorem u17042 : Upper (D 7) (R 7) [12,96,48,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17043 : Route 9 := (fun mask => (mask,id))

def c17043 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17043 : Upper (D 7) (R 7) [12,96,48,384,65,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,384,65,128] 13 (by decide) (choices 1) [1,2] r17043 c17043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4053
  · exact u4054

def b17044 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 52 392 145 33 66 194 322), lower := (rows 13 98 52 392 145 33 64 128 256), losses := [] }

theorem u17044 : Upper (D 7) (R 7) [12,96,48,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17045 : Route 9 := (fun mask => (mask,id))

def c17045 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17045 : Upper (D 7) (R 7) [12,96,48,384,129,2] 13 := by
  apply FastRouting.sound _ _ [12,96,48,384,129,2] 13 (by decide) (choices 1) [1,2] r17045 c17045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4055
  · exact u4056

def b17046 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 392 145 96 67 131 259), lower := (rows 13 98 52 392 145 96 64 128 256), losses := [] }

theorem u17046 : Upper (D 7) (R 7) [12,96,48,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17047 : Route 9 := (fun mask => (mask,id))

def c17047 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17047 : Upper (D 7) (R 7) [12,96,48,384,130,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,384,130,1] 13 (by decide) (choices 1) [1,2] r17047 c17047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4057
  · exact u4058

def b17048 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 52 392 146 34 65 193 321), lower := (rows 13 98 52 392 146 34 64 128 256), losses := [] }

theorem u17048 : Upper (D 7) (R 7) [12,96,48,384,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17049 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 392 146 96 67 131 259), lower := (rows 13 98 52 392 146 96 64 128 256), losses := [] }

theorem u17049 : Upper (D 7) (R 7) [12,96,48,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17050 : Route 9 := (fun mask => (mask,id))

def c17050 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17050 : Upper (D 7) (R 7) [12,96,48,384,192,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,384,192,1] 13 (by decide) (choices 1) [1,2] r17050 c17050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4059
  · exact u4060

def b17051 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 392 208 34 67 131 259), lower := (rows 13 98 52 392 208 34 64 128 256), losses := [] }

theorem u17051 : Upper (D 7) (R 7) [12,96,48,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17052 : Route 9 := (fun mask => (mask,id))

def c17052 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17052 : Upper (D 7) (R 7) [12,96,129,257,130,2] 13 := by
  apply FastRouting.sound _ _ [12,96,129,257,130,2] 13 (by decide) (choices 1) [16,32] r17052 c17052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4061
  · exact u4062

def b17053 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 4, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 133 265 146 48 98 226 354), lower := (rows 13 98 133 265 146 48 64 128 256), losses := [] }

theorem u17053 : Upper (D 7) (R 7) [12,96,129,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17053 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17054 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 265 146 96 114 178 306), lower := (rows 13 98 133 265 146 96 64 128 256), losses := [] }

theorem u17054 : Upper (D 7) (R 7) [12,96,129,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17055 : Route 9 := (fun mask => (mask,id))

def c17055 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17055 : Upper (D 7) (R 7) [12,96,129,257,160,2] 13 := by
  apply FastRouting.sound _ _ [12,96,129,257,160,2] 13 (by decide) (choices 1) [2,16] r17055 c17055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4063
  · exact u4064

def b17056 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 133 265 176 48 66 194 322), lower := (rows 13 98 133 265 176 48 64 128 256), losses := [] }

theorem u17056 : Upper (D 7) (R 7) [12,96,129,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17056 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17057 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 265 176 96 82 146 274), lower := (rows 13 98 133 265 176 96 64 128 256), losses := [] }

theorem u17057 : Upper (D 7) (R 7) [12,96,129,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17058 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 13 98 133 266 19 48 224 224 480), lower := (rows 13 98 133 266 19 48 64 128 256), losses := [] }

theorem u17058 : Upper (D 7) (R 7) [12,96,129,258,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17058 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17059 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 266 19 96 240 176 432), lower := (rows 13 98 133 266 19 96 64 128 256), losses := [] }

theorem u17059 : Upper (D 7) (R 7) [12,96,129,258,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17060_16 : Upper (D 7) (R 7) [12,96,129,258,3,128,16] 13 :=
  permutation_upper _ _ _ [12,96,129,258,3,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4065

theorem m17060_32 : Upper (D 7) (R 7) [12,96,129,258,3,128,32] 13 :=
  permutation_upper _ _ _ [12,96,129,258,3,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4066

def r17060 : Route 9 := (fun mask => (mask,id))

def c17060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17060 : Upper (D 7) (R 7) [12,96,129,258,3,128] 13 := by
  apply FastRouting.sound _ _ [12,96,129,258,3,128] 13 (by decide) (choices 1) [16,32] r17060 c17060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17060_16
  · exact m17060_32

def b17061 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 4, region := 196, targets := 34 }], pairs := [(1,0),(2,1),(2,5),(3,0)], upper := (rows 13 98 133 266 49 34 208 208 464), lower := (rows 13 98 133 266 49 34 64 128 256), losses := [] }

theorem u17061 : Upper (D 7) (R 7) [12,96,129,258,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17062 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 13 98 133 266 49 48 194 194 450), lower := (rows 13 98 133 266 49 48 64 128 256), losses := [] }

theorem u17062 : Upper (D 7) (R 7) [12,96,129,258,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17062 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17063 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 266 49 96 210 146 402), lower := (rows 13 98 133 266 49 96 64 128 256), losses := [] }

theorem u17063 : Upper (D 7) (R 7) [12,96,129,258,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17064 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 330, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,6)], upper := (rows 13 98 133 266 49 160 82 210 338), lower := (rows 13 98 133 266 49 160 64 128 256), losses := [] }

theorem u17064 : Upper (D 7) (R 7) [12,96,129,258,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17065 : Route 9 := (fun mask => (mask,id))

def c17065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17065 : Upper (D 7) (R 7) [12,96,129,258,130,1] 13 := by
  apply FastRouting.sound _ _ [12,96,129,258,130,1] 13 (by decide) (choices 1) [16,32] r17065 c17065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4067
  · exact u4068

theorem m17066_1 : Upper (D 7) (R 7) [12,96,129,258,130,16,1] 13 :=
  permutation_upper _ _ _ [12,96,129,258,130,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4067

def r17066 : Route 9 := (fun mask => (mask,id))

def c17066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17066 : Upper (D 7) (R 7) [12,96,129,258,130,16] 13 := by
  apply FastRouting.sound _ _ [12,96,129,258,130,16] 13 (by decide) (choices 1) [1,32] r17066 c17066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17066_1
  · exact u4069

def b17067 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 266 146 96 113 177 305), lower := (rows 13 98 133 266 146 96 64 128 256), losses := [] }

theorem u17067 : Upper (D 7) (R 7) [12,96,129,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17068 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 48, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 13 98 133 266 176 33 82 210 338), lower := (rows 13 98 133 266 176 33 64 128 256), losses := [] }

theorem u17068 : Upper (D 7) (R 7) [12,96,129,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17069 : Route 9 := (fun mask => (mask,id))

def c17069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17069 : Upper (D 7) (R 7) [12,96,129,258,160,2] 13 := by
  apply FastRouting.sound _ _ [12,96,129,258,160,2] 13 (by decide) (choices 1) [1,16] r17069 c17069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4070
  · exact u4071

def b17070 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 133 266 176 48 67 195 323), lower := (rows 13 98 133 266 176 48 64 128 256), losses := [] }

theorem u17070 : Upper (D 7) (R 7) [12,96,129,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17070 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17071 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 266 176 96 83 147 275), lower := (rows 13 98 133 266 176 96 64 128 256), losses := [] }

theorem u17071 : Upper (D 7) (R 7) [12,96,129,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17072 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 13 98 133 280 19 34 224 224 480), lower := (rows 13 98 133 280 19 34 64 128 256), losses := [{ target := 1, region := (rows 25 0 20 24 16 32 98 162 290), good := (rows 13 480 133 285 477 480 64 128 256) }] }

theorem u17072 : Upper (D 7) (R 7) [12,96,129,272,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17073 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 280 19 96 226 162 418), lower := (rows 13 98 133 280 19 96 64 128 256), losses := [] }

theorem u17073 : Upper (D 7) (R 7) [12,96,129,272,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17074 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 5, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 13 98 133 280 19 160 98 226 354), lower := (rows 13 98 133 280 19 160 64 128 256), losses := [{ target := 7, region := (rows 1 34 4 24 16 32 98 0 290), good := (rows 13 354 5 280 347 354 64 0 256) }] }

theorem u17074 : Upper (D 7) (R 7) [12,96,129,272,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17075 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,5),(1,0),(1,7),(3,0)], upper := (rows 13 98 133 280 49 34 194 194 450), lower := (rows 13 98 133 280 49 34 64 128 256), losses := [{ target := 5, region := (rows 25 2 20 24 16 0 98 162 290), good := (rows 13 450 133 285 477 450 64 128 256) }] }

theorem u17075 : Upper (D 7) (R 7) [12,96,129,272,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17076 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 280 49 96 194 130 386), lower := (rows 13 98 133 280 49 96 64 128 256), losses := [] }

theorem u17076 : Upper (D 7) (R 7) [12,96,129,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17077 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 330, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,6)], upper := (rows 13 98 133 280 49 160 66 194 322), lower := (rows 13 98 133 280 49 160 64 128 256), losses := [] }

theorem u17077 : Upper (D 7) (R 7) [12,96,129,272,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17078 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 133 280 146 33 98 226 354), lower := (rows 13 98 133 280 146 33 64 128 256), losses := [] }

theorem u17078 : Upper (D 7) (R 7) [12,96,129,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17079_1 : Upper (D 7) (R 7) [12,96,129,272,130,2,1] 13 :=
  permutation_upper _ _ _ [12,96,129,272,130,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4072

def r17079 : Route 9 := (fun mask => (mask,id))

def c17079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17079 : Upper (D 7) (R 7) [12,96,129,272,130,2] 13 := by
  apply FastRouting.sound _ _ [12,96,129,272,130,2] 13 (by decide) (choices 1) [1,32] r17079 c17079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17079_1
  · exact u4073

def b17080 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 280 146 96 99 163 291), lower := (rows 13 98 133 280 146 96 64 128 256), losses := [] }

theorem u17080 : Upper (D 7) (R 7) [12,96,129,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17081 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 48, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 13 98 133 280 176 33 66 194 322), lower := (rows 13 98 133 280 176 33 64 128 256), losses := [] }

theorem u17081 : Upper (D 7) (R 7) [12,96,129,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17082 : Route 9 := (fun mask => (mask,id))

def c17082 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17082 : Upper (D 7) (R 7) [12,96,129,272,160,2] 13 := by
  apply FastRouting.sound _ _ [12,96,129,272,160,2] 13 (by decide) (choices 1) [1,2] r17082 c17082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4074
  · exact u4075

def b17083 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 280 176 96 67 131 259), lower := (rows 13 98 133 280 176 96 64 128 256), losses := [] }

theorem u17083 : Upper (D 7) (R 7) [12,96,129,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17084 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 196, targets := 34 }], pairs := [(1,0),(2,1),(2,5),(3,0)], upper := (rows 13 98 133 296 19 34 208 208 464), lower := (rows 13 98 133 296 19 34 64 128 256), losses := [] }

theorem u17084 : Upper (D 7) (R 7) [12,96,129,288,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17085 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,0),(2,5),(3,0)], upper := (rows 13 98 133 296 19 48 194 194 450), lower := (rows 13 98 133 296 19 48 64 128 256), losses := [] }

theorem u17085 : Upper (D 7) (R 7) [12,96,129,288,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17085 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17086 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 296 19 96 210 146 402), lower := (rows 13 98 133 296 19 96 64 128 256), losses := [] }

theorem u17086 : Upper (D 7) (R 7) [12,96,129,288,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17087 : Route 9 := (fun mask => (mask,id))

def c17087 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17087 : Upper (D 7) (R 7) [12,96,129,288,3,128] 13 := by
  apply FastRouting.sound _ _ [12,96,129,288,3,128] 13 (by decide) (choices 1) [2,16] r17087 c17087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4076
  · exact u4077

def r17088 : Route 9 := (fun mask => (mask,id))

def c17088 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17088 : Upper (D 7) (R 7) [12,96,129,288,65,2] 13 := by
  apply FastRouting.sound _ _ [12,96,129,288,65,2] 13 (by decide) (choices 1) [2,16,128] r17088 c17088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4078
  · exact u4079
  · exact u4080

def b17089 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 133 296 81 48 194 130 386), lower := (rows 13 98 133 296 81 48 64 128 256), losses := [] }

theorem u17089 : Upper (D 7) (R 7) [12,96,129,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17089 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17090 : Route 9 := (fun mask => (mask,id))

def c17090 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17090 : Upper (D 7) (R 7) [12,96,129,288,65,128] 13 := by
  apply FastRouting.sound _ _ [12,96,129,288,65,128] 13 (by decide) (choices 1) [2,16] r17090 c17090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4081
  · exact u4082

def b17091 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 133 296 146 33 82 210 338), lower := (rows 13 98 133 296 146 33 64 128 256), losses := [] }

theorem u17091 : Upper (D 7) (R 7) [12,96,129,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17092 : Route 9 := (fun mask => (mask,id))

def c17092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17092 : Upper (D 7) (R 7) [12,96,129,288,130,2] 13 := by
  apply FastRouting.sound _ _ [12,96,129,288,130,2] 13 (by decide) (choices 1) [1,16] r17092 c17092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4083
  · exact u4084

def r17093 : Route 9 := (fun mask => (mask,id))

def c17093 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17093 : Upper (D 7) (R 7) [12,96,129,288,130,16] 13 := by
  apply FastRouting.sound _ _ [12,96,129,288,130,16] 13 (by decide) (choices 1) [1,2] r17093 c17093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4085
  · exact u4086

def b17094 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 296 146 96 83 147 275), lower := (rows 13 98 133 296 146 96 64 128 256), losses := [] }

theorem u17094 : Upper (D 7) (R 7) [12,96,129,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17095 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 133 296 208 33 82 146 274), lower := (rows 13 98 133 296 208 33 64 128 256), losses := [] }

theorem u17095 : Upper (D 7) (R 7) [12,96,129,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17096 : Route 9 := (fun mask => (mask,id))

def c17096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17096 : Upper (D 7) (R 7) [12,96,129,288,192,2] 13 := by
  apply FastRouting.sound _ _ [12,96,129,288,192,2] 13 (by decide) (choices 1) [1,2,16] r17096 c17096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4087
  · exact u4088
  · exact u4089

def b17097 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 133 296 208 48 67 131 259), lower := (rows 13 98 133 296 208 48 64 128 256), losses := [] }

theorem u17097 : Upper (D 7) (R 7) [12,96,129,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17097 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17098 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 134 152 49 33 322 450 322), lower := (rows 13 98 134 152 49 33 64 128 256), losses := [] }

theorem u17098 : Upper (D 7) (R 7) [12,96,130,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17099 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 0, region := 354, targets := 128 }], pairs := [(0,6),(1,7),(3,6),(4,6)], upper := (rows 13 98 134 152 49 34 321 449 321), lower := (rows 13 98 134 152 49 34 64 128 256), losses := [] }

theorem u17099 : Upper (D 7) (R 7) [12,96,130,144,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17099
end Delivery.IrregularNine14.P07
