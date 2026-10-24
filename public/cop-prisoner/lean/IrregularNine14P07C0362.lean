import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0107

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21720 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 322 13 168 81 48 198 134 390), lower := (rows 35 322 13 168 81 48 64 128 256), losses := [] }

theorem u21720 : Upper (D 7) (R 7) [34,320,9,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21720 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21721 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 322 13 168 81 160 86 150 278), lower := (rows 35 322 13 168 81 160 64 128 256), losses := [] }

theorem u21721 : Upper (D 7) (R 7) [34,320,9,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21722 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 13 168 84 33 210 146 402), lower := (rows 35 322 13 168 84 33 64 128 256), losses := [] }

theorem u21722 : Upper (D 7) (R 7) [34,320,9,160,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21723 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 168 84 34 209 145 401), lower := (rows 35 322 13 168 84 34 64 128 256), losses := [] }

theorem u21723 : Upper (D 7) (R 7) [34,320,9,160,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21724 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6)], upper := (rows 35 322 13 168 84 48 195 131 387), lower := (rows 35 322 13 168 84 48 64 128 256), losses := [] }

theorem u21724 : Upper (D 7) (R 7) [34,320,9,160,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21724 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21725 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 322 13 168 84 160 83 147 275), lower := (rows 35 322 13 168 84 160 64 128 256), losses := [] }

theorem u21725 : Upper (D 7) (R 7) [34,320,9,160,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21726 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 168 145 34 84 212 340), lower := (rows 35 322 13 168 145 34 64 128 256), losses := [] }

theorem u21726 : Upper (D 7) (R 7) [34,320,9,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21727 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 322 13 168 145 36 82 210 338), lower := (rows 35 322 13 168 145 36 64 128 256), losses := [] }

theorem u21727 : Upper (D 7) (R 7) [34,320,9,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21727 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21728 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 322 13 168 145 48 70 198 326), lower := (rows 35 322 13 168 145 48 64 128 256), losses := [] }

theorem u21728 : Upper (D 7) (R 7) [34,320,9,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21728 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21729 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 168 145 96 86 150 278), lower := (rows 35 322 13 168 145 96 64 128 256), losses := [] }

theorem u21729 : Upper (D 7) (R 7) [34,320,9,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21730 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 13 168 146 33 84 212 340), lower := (rows 35 322 13 168 146 33 64 128 256), losses := [] }

theorem u21730 : Upper (D 7) (R 7) [34,320,9,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21731 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 13 168 146 36 81 209 337), lower := (rows 35 322 13 168 146 36 64 128 256), losses := [] }

theorem u21731 : Upper (D 7) (R 7) [34,320,9,160,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21731 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21732 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 13 168 146 48 69 197 325), lower := (rows 35 322 13 168 146 48 64 128 256), losses := [] }

theorem u21732 : Upper (D 7) (R 7) [34,320,9,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21732 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21733 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 168 146 96 85 149 277), lower := (rows 35 322 13 168 146 96 64 128 256), losses := [] }

theorem u21733 : Upper (D 7) (R 7) [34,320,9,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21734 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 13 168 208 33 86 150 278), lower := (rows 35 322 13 168 208 33 64 128 256), losses := [] }

theorem u21734 : Upper (D 7) (R 7) [34,320,9,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21735 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 168 208 34 85 149 277), lower := (rows 35 322 13 168 208 34 64 128 256), losses := [] }

theorem u21735 : Upper (D 7) (R 7) [34,320,9,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21736 : Route 9 := (fun mask => (mask,id))

def c21736 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21736 : Upper (D 7) (R 7) [34,320,9,160,192,4] 13 := by
  apply FastRouting.sound _ _ [34,320,9,160,192,4] 13 (by decide) (choices 1) [1,2,16] r21736 c21736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6431
  · exact u6432
  · exact u6433

def b21737 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 13 168 208 48 71 135 263), lower := (rows 35 322 13 168 208 48 64 128 256), losses := [] }

theorem u21737 : Upper (D 7) (R 7) [34,320,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21737 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21738 : Route 9 := (fun mask => (mask,id))

def c21738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u21738 : Upper (D 7) (R 7) [34,320,9,192,6,1] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,6,1] 13 (by decide) (choices 1) [16,32,128] r21738 c21738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6434
  · exact u6435
  · exact u6436

def b21739 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 322 13 200 22 48 225 161 417), lower := (rows 35 322 13 200 22 48 64 128 256), losses := [] }

theorem u21739 : Upper (D 7) (R 7) [34,320,9,192,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21739 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21740 : Route 9 := (fun mask => (mask,id))

def c21740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21740 : Upper (D 7) (R 7) [34,320,9,192,6,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,6,128] 13 (by decide) (choices 1) [1,16,32] r21740 c21740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6437
  · exact u6438
  · exact u6439

def b21741 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 322 13 200 52 33 210 146 402), lower := (rows 35 322 13 200 52 33 64 128 256), losses := [] }

theorem u21741 : Upper (D 7) (R 7) [34,320,9,192,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21742 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 200 52 34 209 145 401), lower := (rows 35 322 13 200 52 34 64 128 256), losses := [] }

theorem u21742 : Upper (D 7) (R 7) [34,320,9,192,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21743 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 322 13 200 52 48 195 131 387), lower := (rows 35 322 13 200 52 48 64 128 256), losses := [] }

theorem u21743 : Upper (D 7) (R 7) [34,320,9,192,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21743 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21744 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,1)], upper := (rows 35 322 13 200 52 160 83 147 275), lower := (rows 35 322 13 200 52 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 34 322 60 232 52 160 64 160 256) },{ target := 1, region := (rows 1 0 4 8 20 168 64 128 256), good := (rows 33 320 61 232 52 160 64 160 256) }] }

theorem u21744 : Upper (D 7) (R 7) [34,320,9,192,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21745 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 200 145 34 116 180 308), lower := (rows 35 322 13 200 145 34 64 128 256), losses := [] }

theorem u21745 : Upper (D 7) (R 7) [34,320,9,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21746 : Route 9 := (fun mask => (mask,id))

def c21746 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21746 : Upper (D 7) (R 7) [34,320,9,192,129,4] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,129,4] 13 (by decide) (choices 1) [2,16,32] r21746 c21746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6440
  · exact u6441
  · exact u6442

def r21747 : Route 9 := (fun mask => (mask,id))

def c21747 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21747 : Upper (D 7) (R 7) [34,320,9,192,129,16] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,129,16] 13 (by decide) (choices 1) [2,4,32] r21747 c21747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6443
  · exact u6444
  · exact u6445

def r21748 : Route 9 := (fun mask => (mask,id))

def c21748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21748 : Upper (D 7) (R 7) [34,320,9,192,130,1] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,130,1] 13 (by decide) (choices 1) [4,16,32] r21748 c21748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6446
  · exact u6447
  · exact u6448

def r21749 : Route 9 := (fun mask => (mask,id))

def c21749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21749 : Upper (D 7) (R 7) [34,320,9,192,130,4] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,130,4] 13 (by decide) (choices 1) [1,16,32] r21749 c21749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6449
  · exact u6450
  · exact u6451

def b21750 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 322 13 200 146 48 101 165 293), lower := (rows 35 322 13 200 146 48 64 128 256), losses := [] }

theorem u21750 : Upper (D 7) (R 7) [34,320,9,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21750 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21751 : Route 9 := (fun mask => (mask,id))

def c21751 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21751 : Upper (D 7) (R 7) [34,320,9,192,132,1] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,132,1] 13 (by decide) (choices 1) [2,16,32] r21751 c21751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6452
  · exact u6453
  · exact u6454

def b21752 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 200 148 34 113 177 305), lower := (rows 35 322 13 200 148 34 64 128 256), losses := [] }

theorem u21752 : Upper (D 7) (R 7) [34,320,9,192,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21753 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,6)], upper := (rows 35 322 13 200 148 48 99 163 291), lower := (rows 35 322 13 200 148 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 20 52 0 129 257), good := (rows 419 258 445 136 180 48 0 128 256) }] }

theorem u21753 : Upper (D 7) (R 7) [34,320,9,192,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21753 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21754 : Route 9 := (fun mask => (mask,id))

def c21754 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21754 : Upper (D 7) (R 7) [34,320,9,192,160,1] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,160,1] 13 (by decide) (choices 1) [2,4,16] r21754 c21754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6455
  · exact u6456
  · exact u6457

def b21755 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 200 176 34 85 149 277), lower := (rows 35 322 13 200 176 34 64 128 256), losses := [] }

theorem u21755 : Upper (D 7) (R 7) [34,320,9,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21756 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 323, targets := 128 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,7),(1,7),(4,6)], upper := (rows 35 322 13 200 176 36 83 147 275), lower := (rows 35 322 13 200 176 36 64 128 256), losses := [] }

theorem u21756 : Upper (D 7) (R 7) [34,320,9,192,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21756 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21757 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 13 200 176 48 71 135 263), lower := (rows 35 322 13 200 176 48 64 128 256), losses := [] }

theorem u21757 : Upper (D 7) (R 7) [34,320,9,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21757 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21758 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 14 28 81 33 224 160 416), lower := (rows 35 322 14 28 81 33 64 128 256), losses := [] }

theorem u21758 : Upper (D 7) (R 7) [34,320,10,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21759 : Route 9 := (fun mask => (mask,id))

def c21759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21759 : Upper (D 7) (R 7) [34,320,10,20,65,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,20,65,128] 13 (by decide) (choices 1) [1,32,128] r21759 c21759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6458
  · exact u6459
  · exact u6460

def b21760 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 14 28 112 33 193 129 385), lower := (rows 35 322 14 28 112 33 64 128 256), losses := [] }

theorem u21760 : Upper (D 7) (R 7) [34,320,10,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21761 : Route 9 := (fun mask => (mask,id))

def c21761 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21761 : Upper (D 7) (R 7) [34,320,10,20,96,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,20,96,128] 13 (by decide) (choices 1) [1,128] r21761 c21761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6461
  · exact u6462

def b21762 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 450, targets := 1 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(1,0),(4,1)], upper := (rows 35 322 14 28 145 33 224 224 480), lower := (rows 35 322 14 28 145 33 64 128 256), losses := [] }

theorem u21762 : Upper (D 7) (R 7) [34,320,10,20,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21763 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 322 14 28 145 96 225 161 417), lower := (rows 35 322 14 28 145 96 64 128 256), losses := [] }

theorem u21763 : Upper (D 7) (R 7) [34,320,10,20,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21764 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(4,1)], upper := (rows 35 322 14 28 145 160 97 225 353), lower := (rows 35 322 14 28 145 160 64 128 256), losses := [{ target := 7, region := (rows 33 51 28 24 16 32 97 0 289), good := (rows 355 322 14 30 351 355 64 0 256) }] }

theorem u21764 : Upper (D 7) (R 7) [34,320,10,20,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21765 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,6),(0,7),(1,5),(4,1)], upper := (rows 35 322 14 28 176 33 193 193 449), lower := (rows 35 322 14 28 176 33 64 128 256), losses := [] }

theorem u21765 : Upper (D 7) (R 7) [34,320,10,20,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21766 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 322 14 28 176 96 193 129 385), lower := (rows 35 322 14 28 176 96 64 128 256), losses := [] }

theorem u21766 : Upper (D 7) (R 7) [34,320,10,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21767 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 14 28 176 160 65 193 321), lower := (rows 35 322 14 28 176 160 64 128 256), losses := [] }

theorem u21767 : Upper (D 7) (R 7) [34,320,10,20,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21768 : Route 9 := (fun mask => (mask,id))

def c21768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21768 : Upper (D 7) (R 7) [34,320,10,20,192,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,20,192,1] 13 (by decide) (choices 1) [1,32,128] r21768 c21768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6463
  · exact u6464
  · exact u6465

def b21769 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 322 14 28 208 160 97 161 289), lower := (rows 35 322 14 28 208 160 64 128 256), losses := [] }

theorem u21769 : Upper (D 7) (R 7) [34,320,10,20,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21770 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 14 56 81 33 196 132 388), lower := (rows 35 322 14 56 81 33 64 128 256), losses := [] }

theorem u21770 : Upper (D 7) (R 7) [34,320,10,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21771 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 322 14 56 81 36 193 129 385), lower := (rows 35 322 14 56 81 36 64 128 256), losses := [] }

theorem u21771 : Upper (D 7) (R 7) [34,320,10,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21771 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21772 : Route 9 := (fun mask => (mask,id))

def c21772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21772 : Upper (D 7) (R 7) [34,320,10,48,65,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,48,65,128] 13 (by decide) (choices 1) [1,4,128] r21772 c21772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6466
  · exact u6467
  · exact u6468

def b21773 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 14 56 84 33 193 129 385), lower := (rows 35 322 14 56 84 33 64 128 256), losses := [] }

theorem u21773 : Upper (D 7) (R 7) [34,320,10,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21774 : Route 9 := (fun mask => (mask,id))

def c21774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21774 : Upper (D 7) (R 7) [34,320,10,48,68,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,48,68,128] 13 (by decide) (choices 1) [1,128] r21774 c21774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6469
  · exact u6470

def b21775 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 322 14 56 145 33 196 196 452), lower := (rows 35 322 14 56 145 33 64 128 256), losses := [] }

theorem u21775 : Upper (D 7) (R 7) [34,320,10,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21776 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 322 14 56 145 36 193 193 449), lower := (rows 35 322 14 56 145 36 64 128 256), losses := [] }

theorem u21776 : Upper (D 7) (R 7) [34,320,10,48,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21776 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21777 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 14 56 145 96 197 133 389), lower := (rows 35 322 14 56 145 96 64 128 256), losses := [] }

theorem u21777 : Upper (D 7) (R 7) [34,320,10,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21778 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 322 14 56 145 160 69 197 325), lower := (rows 35 322 14 56 145 160 64 128 256), losses := [] }

theorem u21778 : Upper (D 7) (R 7) [34,320,10,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21779 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,6),(0,7),(1,5),(2,5)], upper := (rows 35 322 14 56 148 33 193 193 449), lower := (rows 35 322 14 56 148 33 64 128 256), losses := [{ target := 5, region := (rows 1 43 12 8 24 0 97 161 289), good := (rows 451 322 30 478 148 451 64 128 256) }] }

theorem u21779 : Upper (D 7) (R 7) [34,320,10,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u21779
end Delivery.IrregularNine14.P07
