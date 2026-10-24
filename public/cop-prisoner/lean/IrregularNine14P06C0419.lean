import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0130

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25140 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 194 292 26 81 40 69 133 261), lower := (rows 35 194 292 26 81 40 64 128 256), losses := [] }

theorem u25140 : Upper (D 6) (R 6) [34,192,288,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25140 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25141 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 293, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 292 26 84 33 77 141 269), lower := (rows 35 194 292 26 84 33 64 128 256), losses := [] }

theorem u25141 : Upper (D 6) (R 6) [34,192,288,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25142 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 292 26 84 36 73 137 265), lower := (rows 35 194 292 26 84 36 64 128 256), losses := [] }

theorem u25142 : Upper (D 6) (R 6) [34,192,288,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25143 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 292 26 84 40 69 133 261), lower := (rows 35 194 292 26 84 40 64 128 256), losses := [] }

theorem u25143 : Upper (D 6) (R 6) [34,192,288,18,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25143 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25144 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 3, region := 194, targets := 1 }], pairs := [(0,2),(1,0),(4,2)], upper := (rows 35 194 292 28 81 33 78 142 270), lower := (rows 35 194 292 28 81 33 64 128 256), losses := [] }

theorem u25144 : Upper (D 6) (R 6) [34,192,288,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25145 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 292 28 81 34 77 141 269), lower := (rows 35 194 292 28 81 34 64 128 256), losses := [] }

theorem u25145 : Upper (D 6) (R 6) [34,192,288,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25146 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 292 28 81 36 75 139 267), lower := (rows 35 194 292 28 81 36 64 128 256), losses := [] }

theorem u25146 : Upper (D 6) (R 6) [34,192,288,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25147 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 260, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 292 28 81 40 71 135 263), lower := (rows 35 194 292 28 81 40 64 128 256), losses := [{ target := 6, region := (rows 1 2 21 24 16 56 0 129 257), good := (rows 423 130 292 60 445 40 0 128 256) }] }

theorem u25147 : Upper (D 6) (R 6) [34,192,288,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25147 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25148 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 292 28 88 33 71 135 263), lower := (rows 35 194 292 28 88 33 64 128 256), losses := [] }

theorem u25148 : Upper (D 6) (R 6) [34,192,288,20,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25149 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 292 28 88 34 69 133 261), lower := (rows 35 194 292 28 88 34 64 128 256), losses := [] }

theorem u25149 : Upper (D 6) (R 6) [34,192,288,20,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25150 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 292 28 88 36 67 131 259), lower := (rows 35 194 292 28 88 36 64 128 256), losses := [] }

theorem u25150 : Upper (D 6) (R 6) [34,192,288,20,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25151 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 194 324 13 22 33 120 184 312), lower := (rows 35 194 324 13 22 33 64 128 256), losses := [] }

theorem u25151 : Upper (D 6) (R 6) [34,192,320,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25152 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 194 324 13 22 40 113 177 305), lower := (rows 35 194 324 13 22 40 64 128 256), losses := [] }

theorem u25152 : Upper (D 6) (R 6) [34,192,320,5,6,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25152 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25153 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 324 13 22 48 105 169 297), lower := (rows 35 194 324 13 22 48 64 128 256), losses := [] }

theorem u25153 : Upper (D 6) (R 6) [34,192,320,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25153 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25154 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 194 324 13 26 33 116 180 308), lower := (rows 35 194 324 13 26 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 41 80 144 272), good := (rows 33 192 324 45 508 33 64 128 256) }] }

theorem u25154 : Upper (D 6) (R 6) [34,192,320,5,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25155 : Route 9 := (fun mask => (mask,id))

def c25155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25155 : Upper (D 6) (R 6) [34,192,320,5,10,4] 13 := by
  apply FastRouting.sound _ _ [34,192,320,5,10,4] 13 (by decide) (choices 1) [1,16,32] r25155 c25155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7811
  · exact u7812
  · exact u7813

def b25156 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 324 13 26 48 101 165 293), lower := (rows 35 194 324 13 26 48 64 128 256), losses := [] }

theorem u25156 : Upper (D 6) (R 6) [34,192,320,5,10,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25156 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25157 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 48, targets := 2 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 194 324 13 52 33 90 154 282), lower := (rows 35 194 324 13 52 33 64 128 256), losses := [] }

theorem u25157 : Upper (D 6) (R 6) [34,192,320,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25158 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 324 13 52 34 89 153 281), lower := (rows 35 194 324 13 52 34 64 128 256), losses := [] }

theorem u25158 : Upper (D 6) (R 6) [34,192,320,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25159 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 194 324 13 52 40 83 147 275), lower := (rows 35 194 324 13 52 40 64 128 256), losses := [] }

theorem u25159 : Upper (D 6) (R 6) [34,192,320,5,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25159 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25160 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 324 13 52 48 75 139 267), lower := (rows 35 194 324 13 52 48 64 128 256), losses := [] }

theorem u25160 : Upper (D 6) (R 6) [34,192,320,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25160 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25161 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 324 13 56 33 86 150 278), lower := (rows 35 194 324 13 56 33 64 128 256), losses := [] }

theorem u25161 : Upper (D 6) (R 6) [34,192,320,5,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25162 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 324 13 56 34 85 149 277), lower := (rows 35 194 324 13 56 34 64 128 256), losses := [] }

theorem u25162 : Upper (D 6) (R 6) [34,192,320,5,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25163 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 324 13 56 36 83 147 275), lower := (rows 35 194 324 13 56 36 64 128 256), losses := [] }

theorem u25163 : Upper (D 6) (R 6) [34,192,320,5,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25164 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 194 324 13 56 48 71 135 263), lower := (rows 35 194 324 13 56 48 64 128 256), losses := [] }

theorem u25164 : Upper (D 6) (R 6) [34,192,320,5,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25164 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25165 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 194 324 14 52 33 89 153 281), lower := (rows 35 194 324 14 52 33 64 128 256), losses := [] }

theorem u25165 : Upper (D 6) (R 6) [34,192,320,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25166 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 324 14 52 40 81 145 273), lower := (rows 35 194 324 14 52 40 64 128 256), losses := [] }

theorem u25166 : Upper (D 6) (R 6) [34,192,320,6,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25166 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25167 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 324 14 52 48 73 137 265), lower := (rows 35 194 324 14 52 48 64 128 256), losses := [] }

theorem u25167 : Upper (D 6) (R 6) [34,192,320,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25167 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25168 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 324 14 56 33 85 149 277), lower := (rows 35 194 324 14 56 33 64 128 256), losses := [] }

theorem u25168 : Upper (D 6) (R 6) [34,192,320,6,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25169 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 194 324 14 56 36 81 145 273), lower := (rows 35 194 324 14 56 36 64 128 256), losses := [] }

theorem u25169 : Upper (D 6) (R 6) [34,192,320,6,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25170 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 324 14 56 48 69 133 261), lower := (rows 35 194 324 14 56 48 64 128 256), losses := [] }

theorem u25170 : Upper (D 6) (R 6) [34,192,320,6,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25170 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25171 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 194 324 25 28 33 102 166 294), lower := (rows 35 194 324 25 28 33 64 128 256), losses := [] }

theorem u25171 : Upper (D 6) (R 6) [34,192,320,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25172 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 324 25 28 34 101 165 293), lower := (rows 35 194 324 25 28 34 64 128 256), losses := [] }

theorem u25172 : Upper (D 6) (R 6) [34,192,320,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25173 : Route 9 := (fun mask => (mask,id))

def c25173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25173 : Upper (D 6) (R 6) [34,192,320,17,12,4] 13 := by
  apply FastRouting.sound _ _ [34,192,320,17,12,4] 13 (by decide) (choices 1) [1,2,32] r25173 c25173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7814
  · exact u7815
  · exact u7816

def b25174 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 324 25 52 33 78 142 270), lower := (rows 35 194 324 25 52 33 64 128 256), losses := [] }

theorem u25174 : Upper (D 6) (R 6) [34,192,320,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25175 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 324 25 52 34 77 141 269), lower := (rows 35 194 324 25 52 34 64 128 256), losses := [] }

theorem u25175 : Upper (D 6) (R 6) [34,192,320,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25176 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 324 25 52 36 75 139 267), lower := (rows 35 194 324 25 52 36 64 128 256), losses := [] }

theorem u25176 : Upper (D 6) (R 6) [34,192,320,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25177 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 324 25 52 40 71 135 263), lower := (rows 35 194 324 25 52 40 64 128 256), losses := [] }

theorem u25177 : Upper (D 6) (R 6) [34,192,320,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25177 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25178 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 194 324 26 28 33 101 165 293), lower := (rows 35 194 324 26 28 33 64 128 256), losses := [] }

theorem u25178 : Upper (D 6) (R 6) [34,192,320,18,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25179 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 35 194 324 26 28 36 97 161 289), lower := (rows 35 194 324 26 28 36 64 128 256), losses := [] }

theorem u25179 : Upper (D 6) (R 6) [34,192,320,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25180 : Route 9 := (fun mask => (mask,id))

def c25180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25180 : Upper (D 6) (R 6) [34,192,320,18,36,1] 13 := by
  apply FastRouting.sound _ _ [34,192,320,18,36,1] 13 (by decide) (choices 1) [1,4,8] r25180 c25180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7817
  · exact u7818
  · exact u7819

def b25181 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 324 26 52 36 73 137 265), lower := (rows 35 194 324 26 52 36 64 128 256), losses := [] }

theorem u25181 : Upper (D 6) (R 6) [34,192,320,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25182 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 324 26 52 40 69 133 261), lower := (rows 35 194 324 26 52 40 64 128 256), losses := [] }

theorem u25182 : Upper (D 6) (R 6) [34,192,320,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25182 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25183 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 194 324 28 56 33 71 135 263), lower := (rows 35 194 324 28 56 33 64 128 256), losses := [] }

theorem u25183 : Upper (D 6) (R 6) [34,192,320,20,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25184 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 324 28 56 34 69 133 261), lower := (rows 35 194 324 28 56 34 64 128 256), losses := [] }

theorem u25184 : Upper (D 6) (R 6) [34,192,320,20,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25185 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 56, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 194 324 28 56 36 67 131 259), lower := (rows 35 194 324 28 56 36 64 128 256), losses := [] }

theorem u25185 : Upper (D 6) (R 6) [34,192,320,20,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25186 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 386 44 25 82 33 68 196 324), lower := (rows 35 386 44 25 82 33 64 128 256), losses := [] }

theorem u25186 : Upper (D 6) (R 6) [34,384,40,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25187 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 386 44 25 82 36 69 197 325), lower := (rows 35 386 44 25 82 36 64 128 256), losses := [] }

theorem u25187 : Upper (D 6) (R 6) [34,384,40,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25188 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 386 44 25 82 96 69 133 261), lower := (rows 35 386 44 25 82 96 64 128 256), losses := [] }

theorem u25188 : Upper (D 6) (R 6) [34,384,40,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25189 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 386 44 25 84 33 70 198 326), lower := (rows 35 386 44 25 84 33 64 128 256), losses := [] }

theorem u25189 : Upper (D 6) (R 6) [34,384,40,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25190 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 44 25 84 34 69 197 325), lower := (rows 35 386 44 25 84 34 64 128 256), losses := [] }

theorem u25190 : Upper (D 6) (R 6) [34,384,40,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25191 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 386 44 25 84 36 67 195 323), lower := (rows 35 386 44 25 84 36 64 128 256), losses := [] }

theorem u25191 : Upper (D 6) (R 6) [34,384,40,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25192 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 386 44 25 84 96 71 135 263), lower := (rows 35 386 44 25 84 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 386 44 60 116 96 96 128 256) }] }

theorem u25192 : Upper (D 6) (R 6) [34,384,40,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25193 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 450, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 386 44 26 81 33 68 196 324), lower := (rows 35 386 44 26 81 33 64 128 256), losses := [] }

theorem u25193 : Upper (D 6) (R 6) [34,384,40,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25194 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 386 44 26 81 36 69 197 325), lower := (rows 35 386 44 26 81 36 64 128 256), losses := [] }

theorem u25194 : Upper (D 6) (R 6) [34,384,40,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25195 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 386 44 26 81 96 69 133 261), lower := (rows 35 386 44 26 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 386 44 62 112 96 96 128 256) }] }

theorem u25195 : Upper (D 6) (R 6) [34,384,40,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25196 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 386 44 26 84 33 69 197 325), lower := (rows 35 386 44 26 84 33 64 128 256), losses := [] }

theorem u25196 : Upper (D 6) (R 6) [34,384,40,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25197 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 450, targets := 36 },{ cop := 3, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 386 44 26 84 36 65 193 321), lower := (rows 35 386 44 26 84 36 64 128 256), losses := [] }

theorem u25197 : Upper (D 6) (R 6) [34,384,40,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25198 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 386 44 26 84 96 69 133 261), lower := (rows 35 386 44 26 84 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 386 44 62 116 96 96 128 256) }] }

theorem u25198 : Upper (D 6) (R 6) [34,384,40,18,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25199 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 386 44 28 81 33 70 198 326), lower := (rows 35 386 44 28 81 33 64 128 256), losses := [] }

theorem u25199 : Upper (D 6) (R 6) [34,384,40,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25199
end Delivery.IrregularNine14.P06
