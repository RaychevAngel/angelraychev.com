import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0116
import IrregularNine14P08C0117

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18720 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 134 88 152 33 97 161 289), lower := (rows 321 38 134 88 152 32 64 128 256), losses := [] }

theorem u18720 : Upper (D 8) (R 8) [320,36,130,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18721 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 134 88 176 41 105 169 297), lower := (rows 321 38 134 88 176 32 64 128 256), losses := [] }

theorem u18721 : Upper (D 8) (R 8) [320,36,130,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18722 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 134 104 145 57 121 185 313), lower := (rows 321 38 134 104 145 32 64 128 256), losses := [] }

theorem u18722 : Upper (D 8) (R 8) [320,36,130,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18723 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 134 104 152 49 113 177 305), lower := (rows 321 38 134 104 152 32 64 128 256), losses := [] }

theorem u18723 : Upper (D 8) (R 8) [320,36,130,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18724 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 134 104 176 57 89 153 281), lower := (rows 321 38 134 104 176 32 64 128 256), losses := [] }

theorem u18724 : Upper (D 8) (R 8) [320,36,130,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18725 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 56 146 97 97 225 353), lower := (rows 321 38 140 56 146 32 64 128 256), losses := [] }

theorem u18725 : Upper (D 8) (R 8) [320,36,136,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18726 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 140 56 176 99 67 195 323), lower := (rows 321 38 140 56 176 32 64 128 256), losses := [] }

theorem u18726 : Upper (D 8) (R 8) [320,36,136,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18727 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 56 208 35 99 163 291), lower := (rows 321 38 140 56 208 32 64 128 256), losses := [] }

theorem u18727 : Upper (D 8) (R 8) [320,36,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18728 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 140 73 145 50 114 178 306), lower := (rows 321 38 140 73 145 32 64 128 256), losses := [] }

theorem u18728 : Upper (D 8) (R 8) [320,36,136,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18729 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 140 73 176 51 115 179 307), lower := (rows 321 38 140 73 176 32 64 128 256), losses := [] }

theorem u18729 : Upper (D 8) (R 8) [320,36,136,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18730 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 38 140 74 145 49 113 177 305), lower := (rows 321 38 140 74 145 32 64 128 256), losses := [] }

theorem u18730 : Upper (D 8) (R 8) [320,36,136,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18731 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 38 140 74 176 49 113 177 305), lower := (rows 321 38 140 74 176 32 64 128 256), losses := [] }

theorem u18731 : Upper (D 8) (R 8) [320,36,136,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18731 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18732 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 88 145 35 99 163 291), lower := (rows 321 38 140 88 145 32 64 128 256), losses := [] }

theorem u18732 : Upper (D 8) (R 8) [320,36,136,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18733 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 88 146 33 97 161 289), lower := (rows 321 38 140 88 146 32 64 128 256), losses := [] }

theorem u18733 : Upper (D 8) (R 8) [320,36,136,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18734 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 88 176 35 99 163 291), lower := (rows 321 38 140 88 176 32 64 128 256), losses := [] }

theorem u18734 : Upper (D 8) (R 8) [320,36,136,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18735 : Route 9 := (fun mask => (mask,id))

def c18735 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18735 : Upper (D 8) (R 8) [320,36,136,96,129] 13 := by
  apply FastRouting.sound _ _ [320,36,136,96,129] 13 (by decide) (choices 1) [1,2,16] r18735 c18735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6983
  · exact u6984
  · exact u6985

def b18736 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 104 146 49 113 177 305), lower := (rows 321 38 140 104 146 32 64 128 256), losses := [] }

theorem u18736 : Upper (D 8) (R 8) [320,36,136,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18737 : Route 9 := (fun mask => (mask,id))

def c18737 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18737 : Upper (D 8) (R 8) [320,36,136,96,160] 13 := by
  apply FastRouting.sound _ _ [320,36,136,96,160] 13 (by decide) (choices 1) [1,2,16] r18737 c18737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6986
  · exact u6987
  · exact u6988

def b18738 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 137 82 49 113 177 305), lower := (rows 321 38 140 137 82 32 64 128 256), losses := [] }

theorem u18738 : Upper (D 8) (R 8) [320,36,136,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18739 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 137 112 51 115 179 307), lower := (rows 321 38 140 137 112 32 64 128 256), losses := [] }

theorem u18739 : Upper (D 8) (R 8) [320,36,136,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18740 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 138 112 49 113 177 305), lower := (rows 321 38 140 138 112 32 64 128 256), losses := [] }

theorem u18740 : Upper (D 8) (R 8) [320,36,136,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18741 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 152 82 33 97 161 289), lower := (rows 321 38 140 152 82 32 64 128 256), losses := [] }

theorem u18741 : Upper (D 8) (R 8) [320,36,136,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18742 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 152 112 35 99 163 291), lower := (rows 321 38 140 152 112 32 64 128 256), losses := [] }

theorem u18742 : Upper (D 8) (R 8) [320,36,136,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18743 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 140 168 82 49 113 177 305), lower := (rows 321 38 140 168 82 32 64 128 256), losses := [] }

theorem u18743 : Upper (D 8) (R 8) [320,36,136,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18744 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 140 168 112 51 83 147 275), lower := (rows 321 38 140 168 112 32 64 128 256), losses := [] }

theorem u18744 : Upper (D 8) (R 8) [320,36,136,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18745 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 56 208 43 75 139 267), lower := (rows 321 38 164 56 208 32 64 128 256), losses := [] }

theorem u18745 : Upper (D 8) (R 8) [320,36,160,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18746 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 74 145 57 121 185 313), lower := (rows 321 38 164 74 145 32 64 128 256), losses := [] }

theorem u18746 : Upper (D 8) (R 8) [320,36,160,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18747 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 74 152 49 113 177 305), lower := (rows 321 38 164 74 152 32 64 128 256), losses := [] }

theorem u18747 : Upper (D 8) (R 8) [320,36,160,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18748 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 74 176 57 89 153 281), lower := (rows 321 38 164 74 176 32 64 128 256), losses := [] }

theorem u18748 : Upper (D 8) (R 8) [320,36,160,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18749 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 88 145 43 107 171 299), lower := (rows 321 38 164 88 145 32 64 128 256), losses := [] }

theorem u18749 : Upper (D 8) (R 8) [320,36,160,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18750 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 88 146 41 105 169 297), lower := (rows 321 38 164 88 146 32 64 128 256), losses := [] }

theorem u18750 : Upper (D 8) (R 8) [320,36,160,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18751 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 88 176 43 75 139 267), lower := (rows 321 38 164 88 176 32 64 128 256), losses := [] }

theorem u18751 : Upper (D 8) (R 8) [320,36,160,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18752 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 104 145 59 91 155 283), lower := (rows 321 38 164 104 145 32 64 128 256), losses := [] }

theorem u18752 : Upper (D 8) (R 8) [320,36,160,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18753 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 104 146 57 89 153 281), lower := (rows 321 38 164 104 146 32 64 128 256), losses := [] }

theorem u18753 : Upper (D 8) (R 8) [320,36,160,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18754 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 104 152 51 83 147 275), lower := (rows 321 38 164 104 152 32 64 128 256), losses := [] }

theorem u18754 : Upper (D 8) (R 8) [320,36,160,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18755 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 52 41 496 480 480 480 480), lower := (rows 7 11 52 41 16 32 64 128 256), losses := [] }

theorem u18755 : Upper (D 8) (R 8) [6,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18756 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 52 73 496 480 480 480 480), lower := (rows 7 11 52 73 16 32 64 128 256), losses := [] }

theorem u18756 : Upper (D 8) (R 8) [6,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18757 : Route 9 := (fun mask => (mask,id))

def c18757 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18757 : Upper (D 8) (R 8) [6,9,48,96] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18757 c18757
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6989
  · exact u6990
  · exact u6991
  · exact u6992
  · exact u6993
  · exact u6994
  · exact u6995
  · exact u6996
  · exact u6997
  · exact u6998

def r18758 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18758 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18758 : Upper (D 8) (R 8) [6,9,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r18758 c18758
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6999
  · exact u7000
  · exact u7001
  · exact u7002
  · exact u7003
  · exact u7004
  · exact u7005

def b18759 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 52 265 240 224 224 224 480), lower := (rows 7 11 52 265 16 32 64 128 256), losses := [] }

theorem u18759 : Upper (D 8) (R 8) [6,9,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18759 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18760 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18760 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18760 : Upper (D 8) (R 8) [6,9,48,288] 13 := by
  apply FastRouting.sound _ _ [6,9,48,288] 13 (by decide) (choices 2) [33,65,96,192] r18760 c18760
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7006
  · exact u7007
  · exact u7008
  · exact u7009

def r18761 : Route 9 := (fun mask => (mask,id))

def c18761 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18761 : Upper (D 8) (R 8) [6,9,48,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18761 c18761
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7010
  · exact u7011
  · exact u7012
  · exact u7013
  · exact u7014
  · exact u7015

def b18762 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 84 41 496 480 480 480 480), lower := (rows 7 11 84 41 16 32 64 128 256), losses := [] }

theorem u18762 : Upper (D 8) (R 8) [6,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18762 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18763 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 11, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 84 73 432 416 480 416 416), lower := (rows 7 11 84 73 16 32 64 128 256), losses := [] }

theorem u18763 : Upper (D 8) (R 8) [6,9,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18764 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 84 104 433 417 481 417 417), lower := (rows 7 11 84 104 16 32 64 128 256), losses := [] }

theorem u18764 : Upper (D 8) (R 8) [6,9,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18765 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 84 137 496 480 480 480 480), lower := (rows 7 11 84 137 16 32 64 128 256), losses := [] }

theorem u18765 : Upper (D 8) (R 8) [6,9,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18766 : Route 9 := (fun mask => (mask,id))

def c18766 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18766 : Upper (D 8) (R 8) [6,9,80,160] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18766 c18766
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7016
  · exact u7017
  · exact u7018
  · exact u7019
  · exact u7020
  · exact u7021
  · exact u7022
  · exact u7023
  · exact u7024
  · exact u7025

def b18767 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 84 200 433 417 481 417 417), lower := (rows 7 11 84 200 16 32 64 128 256), losses := [] }

theorem u18767 : Upper (D 8) (R 8) [6,9,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18768 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 84 265 240 224 224 224 480), lower := (rows 7 11 84 265 16 32 64 128 256), losses := [] }

theorem u18768 : Upper (D 8) (R 8) [6,9,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18769 : Route 9 := (fun mask => (mask,id))

def c18769 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18769 : Upper (D 8) (R 8) [6,9,80,288] 13 := by
  apply FastRouting.sound _ _ [6,9,80,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18769 c18769
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7026
  · exact u7027
  · exact u7028
  · exact u7029
  · exact u7030
  · exact u7031

def b18770 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 84 328 177 161 225 161 417), lower := (rows 7 11 84 328 16 32 64 128 256), losses := [] }

theorem u18770 : Upper (D 8) (R 8) [6,9,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18771 : Route 9 := (fun mask => (mask,id))

def c18771 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18771 : Upper (D 8) (R 8) [6,9,80,384] 13 := by
  apply FastRouting.sound _ _ [6,9,80,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18771 c18771
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7032
  · exact u7033
  · exact u7034
  · exact u7035
  · exact u7036
  · exact u7037

def b18772 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 100 25 496 480 480 480 480), lower := (rows 7 11 100 25 16 32 64 128 256), losses := [] }

theorem u18772 : Upper (D 8) (R 8) [6,9,96,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18773 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 41 496 496 496 496 496), lower := (rows 7 11 100 41 16 32 64 128 256), losses := [] }

theorem u18773 : Upper (D 8) (R 8) [6,9,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18774 : Route 9 := (fun mask => (mask,id))

def c18774 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18774 : Upper (D 8) (R 8) [6,9,96,48] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18774 c18774
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7038
  · exact u7039
  · exact u7040
  · exact u7041
  · exact u7042
  · exact u7043
  · exact u7044
  · exact u7045
  · exact u7046
  · exact u7047

def b18775 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 11, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 100 73 432 432 496 432 432), lower := (rows 7 11 100 73 16 32 64 128 256), losses := [] }

theorem u18775 : Upper (D 8) (R 8) [6,9,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18776 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 100 88 433 417 481 417 417), lower := (rows 7 11 100 88 16 32 64 128 256), losses := [] }

theorem u18776 : Upper (D 8) (R 8) [6,9,96,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18777 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 11, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 104 433 433 497 433 433), lower := (rows 7 11 100 104 16 32 64 128 256), losses := [] }

theorem u18777 : Upper (D 8) (R 8) [6,9,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18778 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 100 137 496 496 496 496 496), lower := (rows 7 11 100 137 16 32 64 128 256), losses := [] }

theorem u18778 : Upper (D 8) (R 8) [6,9,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18778 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18779 : Route 9 := (fun mask => (mask,id))

def c18779 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18779 : Upper (D 8) (R 8) [6,9,96,144] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18779 c18779
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7048
  · exact u7049
  · exact u7050
  · exact u7051
  · exact u7052
  · exact u7053
  · exact u7054
  · exact u7055
  · exact u7056
  · exact u7057

#print axioms u18779
end Delivery.IrregularNine14.P08
