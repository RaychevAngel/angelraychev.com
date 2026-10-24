import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0135

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26040 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 266 81 48 69 133 261), lower := (rows 41 98 134 266 81 48 64 128 256), losses := [] }

theorem u26040 : Upper (D 6) (R 6) [40,96,130,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26040 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26041 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 266 84 33 85 149 277), lower := (rows 41 98 134 266 84 33 64 128 256), losses := [] }

theorem u26041 : Upper (D 6) (R 6) [40,96,130,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26042 : Route 9 := (fun mask => (mask,id))

def c26042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26042 : Upper (D 6) (R 6) [40,96,130,258,68,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,258,68,4] 13 (by decide) (choices 1) [1,16] r26042 c26042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8143
  · exact u8144

def b26043 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 266 84 48 69 133 261), lower := (rows 41 98 134 266 84 48 64 128 256), losses := [] }

theorem u26043 : Upper (D 6) (R 6) [40,96,130,258,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26043 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26044 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 98 134 268 19 33 84 212 340), lower := (rows 41 98 134 268 19 33 64 128 256), losses := [] }

theorem u26044 : Upper (D 6) (R 6) [40,96,130,260,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26045 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 134 268 19 36 81 209 337), lower := (rows 41 98 134 268 19 36 64 128 256), losses := [] }

theorem u26045 : Upper (D 6) (R 6) [40,96,130,260,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26046 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 41 98 134 268 19 48 69 197 325), lower := (rows 41 98 134 268 19 48 64 128 256), losses := [] }

theorem u26046 : Upper (D 6) (R 6) [40,96,130,260,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26046 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26047 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 268 19 96 85 149 277), lower := (rows 41 98 134 268 19 96 64 128 256), losses := [] }

theorem u26047 : Upper (D 6) (R 6) [40,96,130,260,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26048 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 98 134 268 21 33 82 210 338), lower := (rows 41 98 134 268 21 33 64 128 256), losses := [] }

theorem u26048 : Upper (D 6) (R 6) [40,96,130,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26049 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 328, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(3,1),(3,5)], upper := (rows 41 98 134 268 21 34 81 209 337), lower := (rows 41 98 134 268 21 34 64 128 256), losses := [] }

theorem u26049 : Upper (D 6) (R 6) [40,96,130,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26050 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 134 268 21 48 67 195 323), lower := (rows 41 98 134 268 21 48 64 128 256), losses := [] }

theorem u26050 : Upper (D 6) (R 6) [40,96,130,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26050 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26051 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 268 21 96 83 147 275), lower := (rows 41 98 134 268 21 96 64 128 256), losses := [] }

theorem u26051 : Upper (D 6) (R 6) [40,96,130,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26052 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 268 81 33 86 150 278), lower := (rows 41 98 134 268 81 33 64 128 256), losses := [] }

theorem u26052 : Upper (D 6) (R 6) [40,96,130,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26053 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 134 268 81 34 85 149 277), lower := (rows 41 98 134 268 81 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 118 64 128 256), good := (rows 41 98 162 297 115 34 98 128 256) }] }

theorem u26053 : Upper (D 6) (R 6) [40,96,130,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26054 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 134 268 81 36 83 147 275), lower := (rows 41 98 134 268 81 36 64 128 256), losses := [] }

theorem u26054 : Upper (D 6) (R 6) [40,96,130,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26055 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 268 81 48 71 135 263), lower := (rows 41 98 134 268 81 48 64 128 256), losses := [] }

theorem u26055 : Upper (D 6) (R 6) [40,96,130,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26055 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26056 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 268 84 33 83 147 275), lower := (rows 41 98 134 268 84 33 64 128 256), losses := [] }

theorem u26056 : Upper (D 6) (R 6) [40,96,130,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26057 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 134 268 84 34 81 145 273), lower := (rows 41 98 134 268 84 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 118 64 128 256), good := (rows 41 98 162 297 114 34 98 128 256) }] }

theorem u26057 : Upper (D 6) (R 6) [40,96,130,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26058 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 268 84 48 67 131 259), lower := (rows 41 98 134 268 84 48 64 128 256), losses := [] }

theorem u26058 : Upper (D 6) (R 6) [40,96,130,260,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26058 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26059 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 98 134 280 19 33 68 196 324), lower := (rows 41 98 134 280 19 33 64 128 256), losses := [] }

theorem u26059 : Upper (D 6) (R 6) [40,96,130,272,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26060 : Route 9 := (fun mask => (mask,id))

def c26060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26060 : Upper (D 6) (R 6) [40,96,130,272,3,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,272,3,4] 13 (by decide) (choices 1) [1,4] r26060 c26060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8145
  · exact u8146

def b26061 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 280 19 96 69 133 261), lower := (rows 41 98 134 280 19 96 64 128 256), losses := [] }

theorem u26061 : Upper (D 6) (R 6) [40,96,130,272,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26062 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 280 21 33 70 198 326), lower := (rows 41 98 134 280 21 33 64 128 256), losses := [] }

theorem u26062 : Upper (D 6) (R 6) [40,96,130,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26063 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 328, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(3,1),(3,5)], upper := (rows 41 98 134 280 21 34 69 197 325), lower := (rows 41 98 134 280 21 34 64 128 256), losses := [] }

theorem u26063 : Upper (D 6) (R 6) [40,96,130,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26064 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(0,1),(1,2),(3,2)], upper := (rows 41 98 134 280 21 36 67 195 323), lower := (rows 41 98 134 280 21 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 96 164 313 53 36 64 128 256) },{ target := 2, region := (rows 1 3 0 24 16 32 81 145 273), good := (rows 491 98 130 472 475 32 64 128 256) }] }

theorem u26064 : Upper (D 6) (R 6) [40,96,130,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26065 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 280 21 96 71 135 263), lower := (rows 41 98 134 280 21 96 64 128 256), losses := [] }

theorem u26065 : Upper (D 6) (R 6) [40,96,130,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26066 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 280 81 33 70 134 262), lower := (rows 41 98 134 280 81 33 64 128 256), losses := [] }

theorem u26066 : Upper (D 6) (R 6) [40,96,130,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26067 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 134 280 81 34 69 133 261), lower := (rows 41 98 134 280 81 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 126 64 128 256), good := (rows 41 98 162 315 115 34 98 128 256) }] }

theorem u26067 : Upper (D 6) (R 6) [40,96,130,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26068 : Route 9 := (fun mask => (mask,id))

def c26068 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26068 : Upper (D 6) (R 6) [40,96,130,272,65,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,272,65,4] 13 (by decide) (choices 1) [1,2,4] r26068 c26068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8147
  · exact u8148
  · exact u8149

def b26069 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 280 84 33 71 135 263), lower := (rows 41 98 134 280 84 33 64 128 256), losses := [] }

theorem u26069 : Upper (D 6) (R 6) [40,96,130,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26070 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 134 280 84 34 69 133 261), lower := (rows 41 98 134 280 84 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 126 64 128 256), good := (rows 41 98 162 315 114 34 98 128 256) }] }

theorem u26070 : Upper (D 6) (R 6) [40,96,130,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26071 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 66, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,2)], upper := (rows 41 98 134 280 84 36 67 131 259), lower := (rows 41 98 134 280 84 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 96 164 313 116 36 64 128 256) }] }

theorem u26071 : Upper (D 6) (R 6) [40,96,130,272,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26072 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 328 21 33 86 150 278), lower := (rows 41 98 134 328 21 33 64 128 256), losses := [] }

theorem u26072 : Upper (D 6) (R 6) [40,96,130,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26073 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 4, region := 328, targets := 2 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 41 98 134 328 21 34 85 149 277), lower := (rows 41 98 134 328 21 34 64 128 256), losses := [] }

theorem u26073 : Upper (D 6) (R 6) [40,96,130,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26074 : Route 9 := (fun mask => (mask,id))

def c26074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26074 : Upper (D 6) (R 6) [40,96,130,320,5,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,320,5,4] 13 (by decide) (choices 1) [1,2,16] r26074 c26074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8150
  · exact u8151
  · exact u8152

def r26075 : Route 9 := (fun mask => (mask,id))

def c26075 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26075 : Upper (D 6) (R 6) [40,96,130,320,5,16] 13 := by
  apply FastRouting.sound _ _ [40,96,130,320,5,16] 13 (by decide) (choices 1) [1,2,4] r26075 c26075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8153
  · exact u8154
  · exact u8155

def b26076 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 148 13 22 33 322 450 322), lower := (rows 41 98 148 13 22 33 64 128 256), losses := [] }

theorem u26076 : Upper (D 6) (R 6) [40,96,144,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26077 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 355, targets := 4 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 41 98 148 13 22 34 321 449 321), lower := (rows 41 98 148 13 22 34 64 128 256), losses := [] }

theorem u26077 : Upper (D 6) (R 6) [40,96,144,5,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26078 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 13 22 96 323 387 259), lower := (rows 41 98 148 13 22 96 64 128 256), losses := [] }

theorem u26078 : Upper (D 6) (R 6) [40,96,144,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26079 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 41 98 148 13 22 288 67 195 323), lower := (rows 41 98 148 13 22 288 64 128 256), losses := [] }

theorem u26079 : Upper (D 6) (R 6) [40,96,144,5,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26079 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26080 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 148 13 81 34 326 390 262), lower := (rows 41 98 148 13 81 34 64 128 256), losses := [] }

theorem u26080 : Upper (D 6) (R 6) [40,96,144,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26081 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 148 13 81 36 322 386 258), lower := (rows 41 98 148 13 81 36 64 128 256), losses := [] }

theorem u26081 : Upper (D 6) (R 6) [40,96,144,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26082 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 148 13 81 288 70 134 262), lower := (rows 41 98 148 13 81 288 64 128 256), losses := [] }

theorem u26082 : Upper (D 6) (R 6) [40,96,144,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26082 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26083 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 148 13 84 33 322 386 258), lower := (rows 41 98 148 13 84 33 64 128 256), losses := [] }

theorem u26083 : Upper (D 6) (R 6) [40,96,144,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26084 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 355, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 13 84 34 323 387 259), lower := (rows 41 98 148 13 84 34 64 128 256), losses := [] }

theorem u26084 : Upper (D 6) (R 6) [40,96,144,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26085 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 41 98 148 13 84 288 67 131 259), lower := (rows 41 98 148 13 84 288 64 128 256), losses := [] }

theorem u26085 : Upper (D 6) (R 6) [40,96,144,5,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26085 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26086 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 148 13 273 34 70 198 326), lower := (rows 41 98 148 13 273 34 64 128 256), losses := [] }

theorem u26086 : Upper (D 6) (R 6) [40,96,144,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26087 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 148 13 273 36 66 194 322), lower := (rows 41 98 148 13 273 36 64 128 256), losses := [] }

theorem u26087 : Upper (D 6) (R 6) [40,96,144,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26088 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 13 273 96 70 134 262), lower := (rows 41 98 148 13 273 96 64 128 256), losses := [] }

theorem u26088 : Upper (D 6) (R 6) [40,96,144,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26089 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 148 13 274 33 70 198 326), lower := (rows 41 98 148 13 274 33 64 128 256), losses := [] }

theorem u26089 : Upper (D 6) (R 6) [40,96,144,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26090 : PairBound 9 := { available := 69, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 41 98 148 13 274 34 69 197 325), lower := (rows 41 98 148 13 274 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 12 16 50 0 128 256), good := (rows 41 34 189 13 306 34 0 128 256) }] }

theorem u26090 : Upper (D 6) (R 6) [40,96,144,5,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26091 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 148 13 274 36 67 195 323), lower := (rows 41 98 148 13 274 36 64 128 256), losses := [] }

theorem u26091 : Upper (D 6) (R 6) [40,96,144,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26092 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 13 274 96 71 135 263), lower := (rows 41 98 148 13 274 96 64 128 256), losses := [] }

theorem u26092 : Upper (D 6) (R 6) [40,96,144,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26093 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 148 13 276 33 66 194 322), lower := (rows 41 98 148 13 276 33 64 128 256), losses := [] }

theorem u26093 : Upper (D 6) (R 6) [40,96,144,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26094 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 13 276 34 67 195 323), lower := (rows 41 98 148 13 276 34 64 128 256), losses := [] }

theorem u26094 : Upper (D 6) (R 6) [40,96,144,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26095 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 13 276 96 67 131 259), lower := (rows 41 98 148 13 276 96 64 128 256), losses := [] }

theorem u26095 : Upper (D 6) (R 6) [40,96,144,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26096 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 148 13 336 33 70 134 262), lower := (rows 41 98 148 13 336 33 64 128 256), losses := [] }

theorem u26096 : Upper (D 6) (R 6) [40,96,144,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26097 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 13 336 34 71 135 263), lower := (rows 41 98 148 13 336 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 118 64 128 256), good := (rows 41 98 178 41 370 34 98 128 256) }] }

theorem u26097 : Upper (D 6) (R 6) [40,96,144,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26098 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 148 13 336 36 67 131 259), lower := (rows 41 98 148 13 336 36 64 128 256), losses := [] }

theorem u26098 : Upper (D 6) (R 6) [40,96,144,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26099 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 98 148 14 21 33 322 450 322), lower := (rows 41 98 148 14 21 33 64 128 256), losses := [] }

theorem u26099 : Upper (D 6) (R 6) [40,96,144,6,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u26099
end Delivery.IrregularNine14.P06
