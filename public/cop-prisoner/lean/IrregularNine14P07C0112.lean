import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0008

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6720 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 37 42 69 200 145 288 80 130 258), lower := (rows 37 42 69 200 145 288 80 128 256), losses := [] }

theorem u6720 : Upper (D 7) (R 7) [36,40,65,192,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6720 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6721 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 37 42 69 200 146 288 65 146 274), lower := (rows 37 42 69 200 146 288 65 128 256), losses := [] }

theorem u6721 : Upper (D 7) (R 7) [36,40,65,192,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6721 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6722 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(2,7),(3,0)], upper := (rows 37 42 69 200 146 288 66 145 273), lower := (rows 37 42 69 200 146 288 66 128 256), losses := [] }

theorem u6722 : Upper (D 7) (R 7) [36,40,65,192,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6722 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6723 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 42 69 200 146 288 80 131 259), lower := (rows 37 42 69 200 146 288 80 128 256), losses := [] }

theorem u6723 : Upper (D 7) (R 7) [36,40,65,192,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6723 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6724 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 37 42 69 200 274 48 65 130 386), lower := (rows 37 42 69 200 274 48 65 128 256), losses := [] }

theorem u6724 : Upper (D 7) (R 7) [36,40,65,192,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6724 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6725 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 136, targets := 2 }], pairs := [(0,7),(2,7),(3,1)], upper := (rows 37 42 69 200 274 48 66 129 385), lower := (rows 37 42 69 200 274 48 66 128 256), losses := [] }

theorem u6725 : Upper (D 7) (R 7) [36,40,65,192,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6725 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6726 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 42 69 200 274 48 192 131 259), lower := (rows 37 42 69 200 274 48 192 128 256), losses := [] }

theorem u6726 : Upper (D 7) (R 7) [36,40,65,192,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6726 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6727 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 37 42 69 200 400 48 65 130 258), lower := (rows 37 42 69 200 400 48 65 128 256), losses := [] }

theorem u6727 : Upper (D 7) (R 7) [36,40,65,192,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6727 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6728 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 42 69 200 400 48 66 131 259), lower := (rows 37 42 69 200 400 48 66 128 256), losses := [] }

theorem u6728 : Upper (D 7) (R 7) [36,40,65,192,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6728 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6729 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 42 69 265 82 160 66 144 400), lower := (rows 37 42 69 265 82 160 66 128 256), losses := [] }

theorem u6729 : Upper (D 7) (R 7) [36,40,65,257,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6730 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 42 69 265 82 160 80 130 386), lower := (rows 37 42 69 265 82 160 80 128 256), losses := [] }

theorem u6730 : Upper (D 7) (R 7) [36,40,65,257,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6730 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6731 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 42 69 265 82 160 192 146 274), lower := (rows 37 42 69 265 82 160 192 128 256), losses := [] }

theorem u6731 : Upper (D 7) (R 7) [36,40,65,257,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6732 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 42 69 265 146 160 66 208 336), lower := (rows 37 42 69 265 146 160 66 128 256), losses := [] }

theorem u6732 : Upper (D 7) (R 7) [36,40,65,257,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6733 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 37 42 69 265 146 160 80 194 322), lower := (rows 37 42 69 265 146 160 80 128 256), losses := [] }

theorem u6733 : Upper (D 7) (R 7) [36,40,65,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6733 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6734 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 426, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 42 69 266 82 160 65 144 400), lower := (rows 37 42 69 266 82 160 65 128 256), losses := [] }

theorem u6734 : Upper (D 7) (R 7) [36,40,65,258,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6735 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 42 69 266 82 160 80 129 385), lower := (rows 37 42 69 266 82 160 80 128 256), losses := [] }

theorem u6735 : Upper (D 7) (R 7) [36,40,65,258,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6735 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6736 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(2,1),(2,5),(4,0)], upper := (rows 37 42 69 266 82 160 192 145 273), lower := (rows 37 42 69 266 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 122 100 282 114 224 224 224 256) },{ target := 5, region := (rows 1 2 5 8 18 0 224 128 256), good := (rows 69 90 69 282 82 192 192 192 256) }] }

theorem u6736 : Upper (D 7) (R 7) [36,40,65,258,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6737 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 181, targets := 2 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 42 69 266 145 160 66 208 336), lower := (rows 37 42 69 266 145 160 66 128 256), losses := [] }

theorem u6737 : Upper (D 7) (R 7) [36,40,65,258,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6738 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 42 69 266 145 160 80 194 322), lower := (rows 37 42 69 266 145 160 80 128 256), losses := [] }

theorem u6738 : Upper (D 7) (R 7) [36,40,65,258,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6738 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6739 : PairBound 9 := { available := 80, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 266 146 160 65 208 336), lower := (rows 37 42 69 266 146 160 65 128 256), losses := [] }

theorem u6739 : Upper (D 7) (R 7) [36,40,65,258,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6740 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(2,1)], upper := (rows 37 42 69 266 146 160 80 193 321), lower := (rows 37 42 69 266 146 160 80 128 256), losses := [{ target := 7, region := (rows 1 3 4 13 16 32 80 0 260), good := (rows 303 42 335 266 82 32 80 0 256) }] }

theorem u6740 : Upper (D 7) (R 7) [36,40,65,258,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6740 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6741 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 42 69 266 208 160 65 146 274), lower := (rows 37 42 69 266 208 160 65 128 256), losses := [] }

theorem u6741 : Upper (D 7) (R 7) [36,40,65,258,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6742 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 181, targets := 2 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 42 69 266 208 160 66 145 273), lower := (rows 37 42 69 266 208 160 66 128 256), losses := [] }

theorem u6742 : Upper (D 7) (R 7) [36,40,65,258,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6743 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 42 69 266 208 160 80 131 259), lower := (rows 37 42 69 266 208 160 80 128 256), losses := [] }

theorem u6743 : Upper (D 7) (R 7) [36,40,65,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6743 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6744 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 426, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 42 69 280 82 160 65 130 386), lower := (rows 37 42 69 280 82 160 65 128 256), losses := [] }

theorem u6744 : Upper (D 7) (R 7) [36,40,65,272,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6745 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 42 69 280 82 160 66 129 385), lower := (rows 37 42 69 280 82 160 66 128 256), losses := [] }

theorem u6745 : Upper (D 7) (R 7) [36,40,65,272,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6746 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(2,1),(2,5),(4,0)], upper := (rows 37 42 69 280 82 160 192 131 259), lower := (rows 37 42 69 280 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 122 100 280 114 224 224 224 256) },{ target := 5, region := (rows 1 2 5 8 18 0 224 128 256), good := (rows 69 90 69 280 82 192 192 192 256) }] }

theorem u6746 : Upper (D 7) (R 7) [36,40,65,272,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6747 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 42 69 280 208 34 65 130 386), lower := (rows 37 42 69 280 208 34 65 128 256), losses := [] }

theorem u6747 : Upper (D 7) (R 7) [36,40,65,272,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6748 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 69 280 208 34 66 129 385), lower := (rows 37 42 69 280 208 34 66 128 256), losses := [] }

theorem u6748 : Upper (D 7) (R 7) [36,40,65,272,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6749 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 42 69 280 208 34 192 131 259), lower := (rows 37 42 69 280 208 34 192 128 256), losses := [] }

theorem u6749 : Upper (D 7) (R 7) [36,40,65,272,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6750 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 42 69 328 145 160 66 146 274), lower := (rows 37 42 69 328 145 160 66 128 256), losses := [] }

theorem u6750 : Upper (D 7) (R 7) [36,40,65,320,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6751 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 42 69 328 145 160 80 130 258), lower := (rows 37 42 69 328 145 160 80 128 256), losses := [] }

theorem u6751 : Upper (D 7) (R 7) [36,40,65,320,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6751 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6752 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 178, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 37 42 69 328 146 48 65 130 386), lower := (rows 37 42 69 328 146 48 65 128 256), losses := [] }

theorem u6752 : Upper (D 7) (R 7) [36,40,65,320,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6752 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6753 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 392, targets := 2 }], pairs := [(0,7),(2,7),(3,1)], upper := (rows 37 42 69 328 146 48 66 129 385), lower := (rows 37 42 69 328 146 48 66 128 256), losses := [] }

theorem u6753 : Upper (D 7) (R 7) [36,40,65,320,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6753 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6754 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(2,1)], upper := (rows 37 42 69 328 146 48 192 131 259), lower := (rows 37 42 69 328 146 48 192 128 256), losses := [{ target := 7, region := (rows 1 3 4 12 16 48 64 0 261), good := (rows 303 42 335 328 50 48 64 0 256) }] }

theorem u6754 : Upper (D 7) (R 7) [36,40,65,320,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6754 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6755 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 178, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 42 69 328 146 160 65 146 274), lower := (rows 37 42 69 328 146 160 65 128 256), losses := [] }

theorem u6755 : Upper (D 7) (R 7) [36,40,65,320,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6756 : Route 9 := (fun mask => (mask,id))

def c6756 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6756 : Upper (D 7) (R 7) [36,40,65,320,130,128,2] 13 := by
  apply FastRouting.sound _ _ [36,40,65,320,130,128,2] 13 (by decide) (choices 1) [1,16] r6756 c6756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u492
  · exact u493

def b6757 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(2,1)], upper := (rows 37 42 69 328 146 160 80 131 259), lower := (rows 37 42 69 328 146 160 80 128 256), losses := [{ target := 7, region := (rows 1 3 4 12 16 32 80 0 261), good := (rows 303 42 335 328 82 32 80 0 256) }] }

theorem u6757 : Upper (D 7) (R 7) [36,40,65,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6757 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6758 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 42 69 392 208 34 65 146 274), lower := (rows 37 42 69 392 208 34 65 128 256), losses := [] }

theorem u6758 : Upper (D 7) (R 7) [36,40,65,384,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6759 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 69 392 208 34 66 145 273), lower := (rows 37 42 69 392 208 34 66 128 256), losses := [] }

theorem u6759 : Upper (D 7) (R 7) [36,40,65,384,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6760 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 42 69 392 208 34 80 131 259), lower := (rows 37 42 69 392 208 34 80 128 256), losses := [] }

theorem u6760 : Upper (D 7) (R 7) [36,40,65,384,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6760 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6761 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 42 70 88 145 288 65 130 386), lower := (rows 37 42 70 88 145 288 65 128 256), losses := [] }

theorem u6761 : Upper (D 7) (R 7) [36,40,66,80,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6761 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6762 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 42 70 88 145 288 66 129 385), lower := (rows 37 42 70 88 145 288 66 128 256), losses := [] }

theorem u6762 : Upper (D 7) (R 7) [36,40,66,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6762 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6763 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 42 70 88 145 288 192 131 259), lower := (rows 37 42 70 88 145 288 192 128 256), losses := [] }

theorem u6763 : Upper (D 7) (R 7) [36,40,66,80,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6763 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6764 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 72, targets := 162 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,1),(3,5),(3,7)], upper := (rows 37 42 70 88 273 160 65 130 386), lower := (rows 37 42 70 88 273 160 65 128 256), losses := [] }

theorem u6764 : Upper (D 7) (R 7) [36,40,66,80,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6765 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 37 42 70 88 273 160 66 129 385), lower := (rows 37 42 70 88 273 160 66 128 256), losses := [] }

theorem u6765 : Upper (D 7) (R 7) [36,40,66,80,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6766 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(4,6)], upper := (rows 37 42 70 88 273 160 192 131 259), lower := (rows 37 42 70 88 273 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 14 8 16 224 224 128 256), good := (rows 100 110 102 126 272 224 224 224 256) }] }

theorem u6766 : Upper (D 7) (R 7) [36,40,66,80,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6767 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 37 42 70 88 274 160 65 129 385), lower := (rows 37 42 70 88 274 160 65 128 256), losses := [] }

theorem u6767 : Upper (D 7) (R 7) [36,40,66,80,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6768 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(1,0),(4,6)], upper := (rows 37 42 70 88 274 160 192 129 257), lower := (rows 37 42 70 88 274 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 14 8 16 224 224 128 256), good := (rows 100 110 102 126 278 224 224 224 256) }] }

theorem u6768 : Upper (D 7) (R 7) [36,40,66,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6769 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 42 70 137 81 288 66 144 400), lower := (rows 37 42 70 137 81 288 66 128 256), losses := [] }

theorem u6769 : Upper (D 7) (R 7) [36,40,66,129,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6769 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6770 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 37 42 70 137 81 288 80 130 386), lower := (rows 37 42 70 137 81 288 80 128 256), losses := [] }

theorem u6770 : Upper (D 7) (R 7) [36,40,66,129,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6770 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6771 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 305, targets := 128 },{ cop := 3, region := 80, targets := 2 }], pairs := [(0,7),(4,1),(4,7)], upper := (rows 37 42 70 137 81 288 192 146 274), lower := (rows 37 42 70 137 81 288 192 128 256), losses := [] }

theorem u6771 : Upper (D 7) (R 7) [36,40,66,129,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6771 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6772 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 80, targets := 2 }], pairs := [(0,7),(2,7),(4,1)], upper := (rows 37 42 70 137 208 288 65 146 274), lower := (rows 37 42 70 137 208 288 65 128 256), losses := [] }

theorem u6772 : Upper (D 7) (R 7) [36,40,66,129,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6772 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6773 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 42 70 137 208 288 66 145 273), lower := (rows 37 42 70 137 208 288 66 128 256), losses := [] }

theorem u6773 : Upper (D 7) (R 7) [36,40,66,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6773 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6774 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 37 42 70 137 208 288 80 131 259), lower := (rows 37 42 70 137 208 288 80 128 256), losses := [] }

theorem u6774 : Upper (D 7) (R 7) [36,40,66,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6774 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6775 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 138, targets := 64 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 37 42 70 137 336 48 65 130 386), lower := (rows 37 42 70 137 336 48 65 128 256), losses := [] }

theorem u6775 : Upper (D 7) (R 7) [36,40,66,129,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6775 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6776 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 42 70 137 336 48 66 129 385), lower := (rows 37 42 70 137 336 48 66 128 256), losses := [] }

theorem u6776 : Upper (D 7) (R 7) [36,40,66,129,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6776 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6777 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 138, targets := 64 },{ cop := 2, region := 305, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 37 42 70 137 336 48 192 131 259), lower := (rows 37 42 70 137 336 48 192 128 256), losses := [] }

theorem u6777 : Upper (D 7) (R 7) [36,40,66,129,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6777 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6778 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 70 152 336 33 65 130 386), lower := (rows 37 42 70 152 336 33 65 128 256), losses := [] }

theorem u6778 : Upper (D 7) (R 7) [36,40,66,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6779 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 37 42 70 152 336 33 66 129 385), lower := (rows 37 42 70 152 336 33 66 128 256), losses := [] }

theorem u6779 : Upper (D 7) (R 7) [36,40,66,144,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6779
end Delivery.IrregularNine14.P07
