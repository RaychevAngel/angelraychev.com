import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0011

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5700 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 76 280 176 33 102 166 294), lower := (rows 193 35 76 280 176 33 64 128 256), losses := [] }

theorem u5700 : Upper (D 8) (R 8) [192,33,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5701 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 193 35 76 280 176 34 101 165 293), lower := (rows 193 35 76 280 176 34 64 128 256), losses := [] }

theorem u5701 : Upper (D 8) (R 8) [192,33,72,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5701 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5702 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 35 76 280 176 36 99 163 291), lower := (rows 193 35 76 280 176 36 64 128 256), losses := [] }

theorem u5702 : Upper (D 8) (R 8) [192,33,72,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5702 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5703 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 76 296 176 33 86 150 278), lower := (rows 193 35 76 296 176 33 64 128 256), losses := [] }

theorem u5703 : Upper (D 8) (R 8) [192,33,72,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5704 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 193 35 76 296 176 34 85 149 277), lower := (rows 193 35 76 296 176 34 64 128 256), losses := [] }

theorem u5704 : Upper (D 8) (R 8) [192,33,72,288,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5704 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5705 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 193 35 76 296 176 36 83 147 275), lower := (rows 193 35 76 296 176 36 64 128 256), losses := [] }

theorem u5705 : Upper (D 8) (R 8) [192,33,72,288,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5705 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5706 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 193 35 76 296 176 48 71 135 263), lower := (rows 193 35 76 296 176 48 64 128 256), losses := [] }

theorem u5706 : Upper (D 8) (R 8) [192,33,72,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5706 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5707 : PairBound 9 := { available := 28, camps := [], pairs := [], upper := (rows 193 35 100 168 273 34 92 156 284), lower := (rows 193 35 100 168 273 34 64 128 256), losses := [] }

theorem u5707 : Upper (D 8) (R 8) [192,33,96,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5707 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5708 : PairBound 9 := { available := 26, camps := [], pairs := [], upper := (rows 193 35 100 168 273 36 90 154 282), lower := (rows 193 35 100 168 273 36 64 128 256), losses := [] }

theorem u5708 : Upper (D 8) (R 8) [192,33,96,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5708 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5709 : PairBound 9 := { available := 14, camps := [], pairs := [], upper := (rows 193 35 100 168 273 48 78 142 270), lower := (rows 193 35 100 168 273 48 64 128 256), losses := [] }

theorem u5709 : Upper (D 8) (R 8) [192,33,96,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5709 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5710 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 100 168 274 33 92 156 284), lower := (rows 193 35 100 168 274 33 64 128 256), losses := [] }

theorem u5710 : Upper (D 8) (R 8) [192,33,96,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5711 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 193 35 100 168 274 36 89 153 281), lower := (rows 193 35 100 168 274 36 64 128 256), losses := [] }

theorem u5711 : Upper (D 8) (R 8) [192,33,96,160,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5711 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5712 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 193 35 100 168 274 48 77 141 269), lower := (rows 193 35 100 168 274 48 64 128 256), losses := [] }

theorem u5712 : Upper (D 8) (R 8) [192,33,96,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5712 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5713 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 100 168 276 33 90 154 282), lower := (rows 193 35 100 168 276 33 64 128 256), losses := [] }

theorem u5713 : Upper (D 8) (R 8) [192,33,96,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5714 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 193 35 100 168 276 34 89 153 281), lower := (rows 193 35 100 168 276 34 64 128 256), losses := [] }

theorem u5714 : Upper (D 8) (R 8) [192,33,96,160,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5714 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5715 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 193 35 100 168 276 40 83 147 275), lower := (rows 193 35 100 168 276 40 64 128 256), losses := [] }

theorem u5715 : Upper (D 8) (R 8) [192,33,96,160,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5715 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5716 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 193 35 100 168 276 48 75 139 267), lower := (rows 193 35 100 168 276 48 64 128 256), losses := [] }

theorem u5716 : Upper (D 8) (R 8) [192,33,96,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5716 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5717 : PairBound 9 := { available := 289, camps := [], pairs := [(3,6)], upper := (rows 193 38 76 56 146 33 353 417 289), lower := (rows 193 38 76 56 146 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 10 18 33 0 161 289), good := (rows 417 446 12 440 154 417 0 128 256) }] }

theorem u5717 : Upper (D 8) (R 8) [192,36,72,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5718 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 76 56 146 288 97 161 289), lower := (rows 193 38 76 56 146 288 64 128 256), losses := [] }

theorem u5718 : Upper (D 8) (R 8) [192,36,72,48,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5718 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5719 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 76 56 273 33 226 162 418), lower := (rows 193 38 76 56 273 33 64 128 256), losses := [] }

theorem u5719 : Upper (D 8) (R 8) [192,36,72,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5720 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 38 76 56 273 34 225 161 417), lower := (rows 193 38 76 56 273 34 64 128 256), losses := [] }

theorem u5720 : Upper (D 8) (R 8) [192,36,72,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5720 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5721 : PairBound 9 := { available := 35, camps := [], pairs := [(3,0)], upper := (rows 193 38 76 56 273 160 99 163 291), lower := (rows 193 38 76 56 273 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 161 64 128 256), good := (rows 224 38 76 56 312 160 64 160 256) }] }

theorem u5721 : Upper (D 8) (R 8) [192,36,72,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5722 : PairBound 9 := { available := 161, camps := [], pairs := [(3,6)], upper := (rows 193 38 76 56 274 33 225 161 417), lower := (rows 193 38 76 56 274 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 10 18 33 0 161 289), good := (rows 417 446 12 440 282 417 0 128 256) }] }

theorem u5722 : Upper (D 8) (R 8) [192,36,72,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5723 : Route 9 := (fun mask => (mask,id))

def c5723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5723 : Upper (D 8) (R 8) [192,36,72,48,258,128] 13 := by
  apply FastRouting.sound _ _ [192,36,72,48,258,128] 13 (by decide) (choices 1) [1,32] r5723 c5723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u704
  · exact u705

def r5724 : Route 9 := (fun mask => (mask,id))

def c5724 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5724 : Upper (D 8) (R 8) [192,36,72,48,384,1] 13 := by
  apply FastRouting.sound _ _ [192,36,72,48,384,1] 13 (by decide) (choices 1) [1,2,32] r5724 c5724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u706
  · exact u707
  · exact u708

def b5725 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 76 56 400 34 97 161 289), lower := (rows 193 38 76 56 400 34 64 128 256), losses := [] }

theorem u5725 : Upper (D 8) (R 8) [192,36,72,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5725 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5726 : PairBound 9 := { available := 34, camps := [], pairs := [(1,7)], upper := (rows 193 38 76 152 273 33 98 162 290), lower := (rows 193 38 76 152 273 33 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 49 74 0 266), good := (rows 97 358 334 382 305 33 64 0 256) }] }

theorem u5726 : Upper (D 8) (R 8) [192,36,72,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5727 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 76 152 273 34 97 161 289), lower := (rows 193 38 76 152 273 34 64 128 256), losses := [] }

theorem u5727 : Upper (D 8) (R 8) [192,36,72,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5727 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5728 : PairBound 9 := { available := 33, camps := [], pairs := [(3,6)], upper := (rows 193 38 76 152 274 33 97 161 289), lower := (rows 193 38 76 152 274 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 10 18 33 0 161 289), good := (rows 417 446 12 152 282 417 0 128 256) }] }

theorem u5728 : Upper (D 8) (R 8) [192,36,72,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5729 : Route 9 := (fun mask => (mask,id))

def c5729 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5729 : Upper (D 8) (R 8) [192,36,72,144,288,1] 13 := by
  apply FastRouting.sound _ _ [192,36,72,144,288,1] 13 (by decide) (choices 1) [1,2,32] r5729 c5729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u709
  · exact u710
  · exact u711

def b5730 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 76 152 304 34 97 161 289), lower := (rows 193 38 76 152 304 34 64 128 256), losses := [] }

theorem u5730 : Upper (D 8) (R 8) [192,36,72,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5730 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5731 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 76 168 273 33 114 178 306), lower := (rows 193 38 76 168 273 33 64 128 256), losses := [] }

theorem u5731 : Upper (D 8) (R 8) [192,36,72,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5731 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5732 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 38 76 168 273 34 113 177 305), lower := (rows 193 38 76 168 273 34 64 128 256), losses := [] }

theorem u5732 : Upper (D 8) (R 8) [192,36,72,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5732 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5733 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 38 76 168 273 48 99 163 291), lower := (rows 193 38 76 168 273 48 64 128 256), losses := [] }

theorem u5733 : Upper (D 8) (R 8) [192,36,72,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5733 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5734 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 76 168 274 33 113 177 305), lower := (rows 193 38 76 168 274 33 64 128 256), losses := [] }

theorem u5734 : Upper (D 8) (R 8) [192,36,72,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5735 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 76 168 274 48 97 161 289), lower := (rows 193 38 76 168 274 48 64 128 256), losses := [] }

theorem u5735 : Upper (D 8) (R 8) [192,36,72,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5735 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5736 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 76 168 304 33 83 147 275), lower := (rows 193 38 76 168 304 33 64 128 256), losses := [] }

theorem u5736 : Upper (D 8) (R 8) [192,36,72,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5737 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 193 38 76 168 304 34 81 145 273), lower := (rows 193 38 76 168 304 34 64 128 256), losses := [] }

theorem u5737 : Upper (D 8) (R 8) [192,36,72,160,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5737 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5738 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 193 38 76 168 304 48 67 131 259), lower := (rows 193 38 76 168 304 48 64 128 256), losses := [] }

theorem u5738 : Upper (D 8) (R 8) [192,36,72,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5738 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5739 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 193 38 76 265 146 33 112 176 304), lower := (rows 193 38 76 265 146 33 64 128 256), losses := [] }

theorem u5739 : Upper (D 8) (R 8) [192,36,72,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5740 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 76 265 146 48 97 161 289), lower := (rows 193 38 76 265 146 48 64 128 256), losses := [] }

theorem u5740 : Upper (D 8) (R 8) [192,36,72,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5740 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5741 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 76 265 176 33 114 178 306), lower := (rows 193 38 76 265 176 33 64 128 256), losses := [] }

theorem u5741 : Upper (D 8) (R 8) [192,36,72,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5742 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 38 76 265 176 34 113 177 305), lower := (rows 193 38 76 265 176 34 64 128 256), losses := [] }

theorem u5742 : Upper (D 8) (R 8) [192,36,72,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5742 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5743 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 38 76 265 176 48 99 163 291), lower := (rows 193 38 76 265 176 48 64 128 256), losses := [] }

theorem u5743 : Upper (D 8) (R 8) [192,36,72,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5743 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5744 : PairBound 9 := { available := 33, camps := [], pairs := [(3,6)], upper := (rows 193 38 76 280 146 33 97 161 289), lower := (rows 193 38 76 280 146 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 10 18 33 0 161 289), good := (rows 417 446 12 280 154 417 0 128 256) }] }

theorem u5744 : Upper (D 8) (R 8) [192,36,72,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5745 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 76 280 176 33 99 163 291), lower := (rows 193 38 76 280 176 33 64 128 256), losses := [] }

theorem u5745 : Upper (D 8) (R 8) [192,36,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5746 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 76 280 176 34 97 161 289), lower := (rows 193 38 76 280 176 34 64 128 256), losses := [] }

theorem u5746 : Upper (D 8) (R 8) [192,36,72,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5746 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5747 : Route 9 := (fun mask => (mask,id))

def c5747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5747 : Upper (D 8) (R 8) [192,36,72,288,130,1] 13 := by
  apply FastRouting.sound _ _ [192,36,72,288,130,1] 13 (by decide) (choices 1) [1,16,32] r5747 c5747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u712
  · exact u713
  · exact u714

def b5748 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 76 296 146 48 97 161 289), lower := (rows 193 38 76 296 146 48 64 128 256), losses := [] }

theorem u5748 : Upper (D 8) (R 8) [192,36,72,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5748 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5749 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 76 296 176 33 83 147 275), lower := (rows 193 38 76 296 176 33 64 128 256), losses := [] }

theorem u5749 : Upper (D 8) (R 8) [192,36,72,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5750 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 193 38 76 296 176 34 81 145 273), lower := (rows 193 38 76 296 176 34 64 128 256), losses := [] }

theorem u5750 : Upper (D 8) (R 8) [192,36,72,288,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5750 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5751 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 193 38 76 296 176 48 67 131 259), lower := (rows 193 38 76 296 176 48 64 128 256), losses := [] }

theorem u5751 : Upper (D 8) (R 8) [192,36,72,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5751 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5752 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 261 74 152 33 112 176 304), lower := (rows 193 38 261 74 152 33 64 128 256), losses := [] }

theorem u5752 : Upper (D 8) (R 8) [192,36,257,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5753 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 261 74 152 48 97 161 289), lower := (rows 193 38 261 74 152 48 64 128 256), losses := [] }

theorem u5753 : Upper (D 8) (R 8) [192,36,257,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5753 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5754 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 261 74 176 33 120 184 312), lower := (rows 193 38 261 74 176 33 64 128 256), losses := [] }

theorem u5754 : Upper (D 8) (R 8) [192,36,257,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5755 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 38 261 74 176 40 113 177 305), lower := (rows 193 38 261 74 176 40 64 128 256), losses := [] }

theorem u5755 : Upper (D 8) (R 8) [192,36,257,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5755 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5756 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 193 38 261 74 176 48 105 169 297), lower := (rows 193 38 261 74 176 48 64 128 256), losses := [] }

theorem u5756 : Upper (D 8) (R 8) [192,36,257,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5756 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5757 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 261 88 176 33 106 170 298), lower := (rows 193 38 261 88 176 33 64 128 256), losses := [] }

theorem u5757 : Upper (D 8) (R 8) [192,36,257,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5758 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 193 38 261 88 176 34 105 169 297), lower := (rows 193 38 261 88 176 34 64 128 256), losses := [] }

theorem u5758 : Upper (D 8) (R 8) [192,36,257,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5758 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5759 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 38 261 88 176 40 99 163 291), lower := (rows 193 38 261 88 176 40 64 128 256), losses := [] }

theorem u5759 : Upper (D 8) (R 8) [192,36,257,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5759 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5759
end Delivery.IrregularNine14.P08
