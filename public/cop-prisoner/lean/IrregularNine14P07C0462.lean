import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0170
import IrregularNine14P07C0171

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27720 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 134 11 176 48 73 201 329), lower := (rows 37 322 134 11 176 48 64 128 256), losses := [] }

theorem u27720 : Upper (D 7) (R 7) [36,320,130,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27720 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27721 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 240, targets := 2 }], pairs := [(0,1),(0,7),(4,0),(4,1)], upper := (rows 37 322 134 11 176 96 89 153 281), lower := (rows 37 322 134 11 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 98 64 128 256), good := (rows 52 354 182 42 176 96 96 128 256) },{ target := 1, region := (rows 5 0 4 8 28 106 72 136 264), good := (rows 53 352 181 505 176 96 96 128 256) },{ target := 7, region := (rows 5 2 4 12 16 98 64 0 256), good := (rows 45 354 47 43 48 96 96 0 256) }] }

theorem u27721 : Upper (D 7) (R 7) [36,320,130,3,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27722 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 322 134 11 208 33 120 184 312), lower := (rows 37 322 134 11 208 33 64 128 256), losses := [] }

theorem u27722 : Upper (D 7) (R 7) [36,320,130,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27723 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 322 134 11 208 40 113 177 305), lower := (rows 37 322 134 11 208 40 64 128 256), losses := [] }

theorem u27723 : Upper (D 7) (R 7) [36,320,130,3,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27723 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27724 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 240, targets := 2 }], pairs := [(1,7),(3,7),(4,1)], upper := (rows 37 322 134 11 208 48 105 169 297), lower := (rows 37 322 134 11 208 48 64 128 256), losses := [] }

theorem u27724 : Upper (D 7) (R 7) [36,320,130,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27724 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27725 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 322 134 25 26 33 224 224 480), lower := (rows 37 322 134 25 26 33 64 128 256), losses := [] }

theorem u27725 : Upper (D 7) (R 7) [36,320,130,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27726 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,7)], upper := (rows 37 322 134 25 26 96 225 161 417), lower := (rows 37 322 134 25 26 96 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 13 20 98 64 0 256), good := (rows 61 354 63 25 58 96 96 0 256) }] }

theorem u27726 : Upper (D 7) (R 7) [36,320,130,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27727 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 25 26 160 97 225 353), lower := (rows 37 322 134 25 26 160 64 128 256), losses := [] }

theorem u27727 : Upper (D 7) (R 7) [36,320,130,17,10,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27728 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 322 134 25 50 33 200 200 456), lower := (rows 37 322 134 25 50 33 64 128 256), losses := [] }

theorem u27728 : Upper (D 7) (R 7) [36,320,130,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27729 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 322 134 25 50 40 193 193 449), lower := (rows 37 322 134 25 50 40 64 128 256), losses := [] }

theorem u27729 : Upper (D 7) (R 7) [36,320,130,17,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27729 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27730 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 141, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 322 134 25 50 96 201 137 393), lower := (rows 37 322 134 25 50 96 64 128 256), losses := [] }

theorem u27730 : Upper (D 7) (R 7) [36,320,130,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27731 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 25 50 160 73 201 329), lower := (rows 37 322 134 25 50 160 64 128 256), losses := [] }

theorem u27731 : Upper (D 7) (R 7) [36,320,130,17,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27732 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(2,6)], upper := (rows 37 322 134 25 88 33 226 162 418), lower := (rows 37 322 134 25 88 33 64 128 256), losses := [] }

theorem u27732 : Upper (D 7) (R 7) [36,320,130,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27733 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 37 322 134 25 88 34 225 161 417), lower := (rows 37 322 134 25 88 34 64 128 256), losses := [] }

theorem u27733 : Upper (D 7) (R 7) [36,320,130,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27734 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 25 88 160 99 163 291), lower := (rows 37 322 134 25 88 160 64 128 256), losses := [] }

theorem u27734 : Upper (D 7) (R 7) [36,320,130,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27735 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 134 25 112 33 202 138 394), lower := (rows 37 322 134 25 112 33 64 128 256), losses := [] }

theorem u27735 : Upper (D 7) (R 7) [36,320,130,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27736 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 48, targets := 129 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 37 322 134 25 112 34 201 137 393), lower := (rows 37 322 134 25 112 34 64 128 256), losses := [] }

theorem u27736 : Upper (D 7) (R 7) [36,320,130,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27737 : Route 9 := (fun mask => (mask,id))

def c27737 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27737 : Upper (D 7) (R 7) [36,320,130,17,96,8] 13 := by
  apply FastRouting.sound _ _ [36,320,130,17,96,8] 13 (by decide) (choices 1) [1,2,128] r27737 c27737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10252
  · exact u10253
  · exact u10254

def b27738 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 25 112 160 75 139 267), lower := (rows 37 322 134 25 112 160 64 128 256), losses := [] }

theorem u27738 : Upper (D 7) (R 7) [36,320,130,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27739 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 322 134 25 152 33 98 226 354), lower := (rows 37 322 134 25 152 33 64 128 256), losses := [] }

theorem u27739 : Upper (D 7) (R 7) [36,320,130,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27740 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,6),(3,1),(3,6),(4,6)], upper := (rows 37 322 134 25 152 34 97 225 353), lower := (rows 37 322 134 25 152 34 64 128 256), losses := [] }

theorem u27740 : Upper (D 7) (R 7) [36,320,130,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27741 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(3,1)], upper := (rows 37 322 134 25 152 96 99 163 291), lower := (rows 37 322 134 25 152 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 13 20 98 64 128 256), good := (rows 61 352 189 25 152 96 96 128 256) }] }

theorem u27741 : Upper (D 7) (R 7) [36,320,130,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27742 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 322 134 25 176 33 74 202 330), lower := (rows 37 322 134 25 176 33 64 128 256), losses := [] }

theorem u27742 : Upper (D 7) (R 7) [36,320,130,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27743 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,6),(3,1),(3,6),(4,6)], upper := (rows 37 322 134 25 176 34 73 201 329), lower := (rows 37 322 134 25 176 34 64 128 256), losses := [] }

theorem u27743 : Upper (D 7) (R 7) [36,320,130,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27744 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 322 134 25 176 40 67 195 323), lower := (rows 37 322 134 25 176 40 64 128 256), losses := [] }

theorem u27744 : Upper (D 7) (R 7) [36,320,130,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27744 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27745 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 3, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,5),(4,0)], upper := (rows 37 322 134 25 176 96 75 139 267), lower := (rows 37 322 134 25 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 98 64 128 256), good := (rows 52 354 182 24 176 96 96 128 256) }] }

theorem u27745 : Upper (D 7) (R 7) [36,320,130,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27746 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 354, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 322 134 25 208 33 106 170 298), lower := (rows 37 322 134 25 208 33 64 128 256), losses := [] }

theorem u27746 : Upper (D 7) (R 7) [36,320,130,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27747 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 322 134 25 208 34 105 169 297), lower := (rows 37 322 134 25 208 34 64 128 256), losses := [] }

theorem u27747 : Upper (D 7) (R 7) [36,320,130,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27748 : Route 9 := (fun mask => (mask,id))

def c27748 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27748 : Upper (D 7) (R 7) [36,320,130,17,192,8] 13 := by
  apply FastRouting.sound _ _ [36,320,130,17,192,8] 13 (by decide) (choices 1) [1,2,32] r27748 c27748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10255
  · exact u10256
  · exact u10257

def b27749 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 322 134 26 56 33 193 193 449), lower := (rows 37 322 134 26 56 33 64 128 256), losses := [] }

theorem u27749 : Upper (D 7) (R 7) [36,320,130,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27750 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 37 322 134 26 56 96 193 129 385), lower := (rows 37 322 134 26 56 96 64 128 256), losses := [] }

theorem u27750 : Upper (D 7) (R 7) [36,320,130,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27751 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 26 56 160 65 193 321), lower := (rows 37 322 134 26 56 160 64 128 256), losses := [] }

theorem u27751 : Upper (D 7) (R 7) [36,320,130,18,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27752 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 322 134 26 81 33 232 168 424), lower := (rows 37 322 134 26 81 33 64 128 256), losses := [] }

theorem u27752 : Upper (D 7) (R 7) [36,320,130,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27753 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(2,6),(4,1)], upper := (rows 37 322 134 26 81 40 225 161 417), lower := (rows 37 322 134 26 81 40 64 128 256), losses := [] }

theorem u27753 : Upper (D 7) (R 7) [36,320,130,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27753 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27754 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 26 81 160 105 169 297), lower := (rows 37 322 134 26 81 160 64 128 256), losses := [] }

theorem u27754 : Upper (D 7) (R 7) [36,320,130,18,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27755 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 322 134 26 112 33 201 137 393), lower := (rows 37 322 134 26 112 33 64 128 256), losses := [] }

theorem u27755 : Upper (D 7) (R 7) [36,320,130,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27756 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 37 322 134 26 112 40 193 129 385), lower := (rows 37 322 134 26 112 40 64 128 256), losses := [] }

theorem u27756 : Upper (D 7) (R 7) [36,320,130,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27756 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27757 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 26 112 160 73 137 265), lower := (rows 37 322 134 26 112 160 64 128 256), losses := [] }

theorem u27757 : Upper (D 7) (R 7) [36,320,130,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27758 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(3,6),(4,6)], upper := (rows 37 322 134 26 145 33 104 232 360), lower := (rows 37 322 134 26 145 33 64 128 256), losses := [] }

theorem u27758 : Upper (D 7) (R 7) [36,320,130,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27759 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 322 134 26 145 40 97 225 353), lower := (rows 37 322 134 26 145 40 64 128 256), losses := [] }

theorem u27759 : Upper (D 7) (R 7) [36,320,130,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27759 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27760 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(0,1),(1,7),(3,7),(4,1)], upper := (rows 37 322 134 26 145 96 105 169 297), lower := (rows 37 322 134 26 145 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 20 98 64 128 256), good := (rows 53 352 181 56 145 96 96 128 256) }] }

theorem u27760 : Upper (D 7) (R 7) [36,320,130,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27761 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(3,6),(4,6)], upper := (rows 37 322 134 26 176 33 73 201 329), lower := (rows 37 322 134 26 176 33 64 128 256), losses := [] }

theorem u27761 : Upper (D 7) (R 7) [36,320,130,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27762 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 322 134 26 176 40 65 193 321), lower := (rows 37 322 134 26 176 40 64 128 256), losses := [] }

theorem u27762 : Upper (D 7) (R 7) [36,320,130,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27762 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27763 : PairBound 9 := { available := 9, camps := [], pairs := [(0,1),(3,0),(4,0),(4,1)], upper := (rows 37 322 134 26 176 96 73 137 265), lower := (rows 37 322 134 26 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 98 64 128 256), good := (rows 60 354 190 58 176 96 96 128 256) },{ target := 1, region := (rows 5 0 4 8 20 98 64 128 256), good := (rows 53 352 181 56 176 96 96 128 256) }] }

theorem u27763 : Upper (D 7) (R 7) [36,320,130,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27764 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 322 134 26 208 33 105 169 297), lower := (rows 37 322 134 26 208 33 64 128 256), losses := [] }

theorem u27764 : Upper (D 7) (R 7) [36,320,130,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27765 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(2,6),(4,1)], upper := (rows 37 322 134 26 208 40 97 161 289), lower := (rows 37 322 134 26 208 40 64 128 256), losses := [] }

theorem u27765 : Upper (D 7) (R 7) [36,320,130,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27765 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27766 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 322 134 42 81 33 216 152 408), lower := (rows 37 322 134 42 81 33 64 128 256), losses := [] }

theorem u27766 : Upper (D 7) (R 7) [36,320,130,34,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27767 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 322 134 42 81 40 209 145 401), lower := (rows 37 322 134 42 81 40 64 128 256), losses := [] }

theorem u27767 : Upper (D 7) (R 7) [36,320,130,34,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27767 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27768 : Route 9 := (fun mask => (mask,id))

def c27768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27768 : Upper (D 7) (R 7) [36,320,130,34,65,16] 13 := by
  apply FastRouting.sound _ _ [36,320,130,34,65,16] 13 (by decide) (choices 1) [1,8,128] r27768 c27768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10258
  · exact u10259
  · exact u10260

def b27769 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 42 81 160 89 153 281), lower := (rows 37 322 134 42 81 160 64 128 256), losses := [] }

theorem u27769 : Upper (D 7) (R 7) [36,320,130,34,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27770 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 322 134 42 88 33 209 145 401), lower := (rows 37 322 134 42 88 33 64 128 256), losses := [] }

theorem u27770 : Upper (D 7) (R 7) [36,320,130,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27771 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 37 322 134 42 88 48 193 129 385), lower := (rows 37 322 134 42 88 48 64 128 256), losses := [] }

theorem u27771 : Upper (D 7) (R 7) [36,320,130,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27771 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27772 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 42 88 160 81 145 273), lower := (rows 37 322 134 42 88 160 64 128 256), losses := [] }

theorem u27772 : Upper (D 7) (R 7) [36,320,130,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27773 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(3,6),(4,6)], upper := (rows 37 322 134 42 145 33 88 216 344), lower := (rows 37 322 134 42 145 33 64 128 256), losses := [] }

theorem u27773 : Upper (D 7) (R 7) [36,320,130,34,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27774 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 134 42 145 40 81 209 337), lower := (rows 37 322 134 42 145 40 64 128 256), losses := [] }

theorem u27774 : Upper (D 7) (R 7) [36,320,130,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27774 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27775 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 322 134 42 145 48 73 201 329), lower := (rows 37 322 134 42 145 48 64 128 256), losses := [] }

theorem u27775 : Upper (D 7) (R 7) [36,320,130,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27775 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27776 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 149, targets := 64 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(4,6)], upper := (rows 37 322 134 42 145 96 89 153 281), lower := (rows 37 322 134 42 145 96 64 128 256), losses := [] }

theorem u27776 : Upper (D 7) (R 7) [36,320,130,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27777 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,6),(4,6)], upper := (rows 37 322 134 42 152 33 81 209 337), lower := (rows 37 322 134 42 152 33 64 128 256), losses := [] }

theorem u27777 : Upper (D 7) (R 7) [36,320,130,34,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27778 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 322 134 42 152 48 65 193 321), lower := (rows 37 322 134 42 152 48 64 128 256), losses := [] }

theorem u27778 : Upper (D 7) (R 7) [36,320,130,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27778 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27779 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 149, targets := 64 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(4,6)], upper := (rows 37 322 134 42 152 96 81 145 273), lower := (rows 37 322 134 42 152 96 64 128 256), losses := [] }

theorem u27779 : Upper (D 7) (R 7) [36,320,130,34,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27779
end Delivery.IrregularNine14.P07
