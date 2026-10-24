import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0013

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10860 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 259 44 200 148 34 66 145 273), lower := (rows 97 259 44 200 148 34 66 128 256), losses := [] }

theorem u10860 : Upper (D 7) (R 7) [96,257,40,192,132,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10861 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 259 44 200 148 34 80 131 259), lower := (rows 97 259 44 200 148 34 80 128 256), losses := [] }

theorem u10861 : Upper (D 7) (R 7) [96,257,40,192,132,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10861 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10862 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 262, targets := 128 },{ cop := 4, region := 105, targets := 2 }], pairs := [(0,1),(1,7),(2,7)], upper := (rows 97 262 7 25 146 40 192 224 352), lower := (rows 97 262 7 25 146 40 192 128 256), losses := [] }

theorem u10862 : Upper (D 7) (R 7) [96,260,3,17,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10862 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10863 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 25 146 96 192 168 296), lower := (rows 97 262 7 25 146 96 192 128 256), losses := [] }

theorem u10863 : Upper (D 7) (R 7) [96,260,3,17,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10864 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 262, targets := 128 },{ cop := 3, region := 225, targets := 2 }], pairs := [(0,1),(1,7),(2,7)], upper := (rows 97 262 7 26 145 40 192 224 352), lower := (rows 97 262 7 26 145 40 192 128 256), losses := [] }

theorem u10864 : Upper (D 7) (R 7) [96,260,3,18,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10864 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10865 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 26 145 96 192 168 296), lower := (rows 97 262 7 26 145 96 192 128 256), losses := [] }

theorem u10865 : Upper (D 7) (R 7) [96,260,3,18,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10866 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 97 262 7 26 176 33 72 192 448), lower := (rows 97 262 7 26 176 33 72 128 256), losses := [] }

theorem u10866 : Upper (D 7) (R 7) [96,260,3,18,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10866 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10867 : Route 9 := (fun mask => (mask,id))

def c10867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u10867 : Upper (D 7) (R 7) [96,260,3,18,160,1,128] 13 := by
  apply FastRouting.sound _ _ [96,260,3,18,160,1,128] 13 (by decide) (choices 1) [8,64] r10867 c10867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u807
  · exact u808

def b10868 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 3, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 97 262 7 42 88 160 65 144 400), lower := (rows 97 262 7 42 88 160 65 128 256), losses := [] }

theorem u10868 : Upper (D 7) (R 7) [96,260,3,34,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10869 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 7 42 88 160 80 129 385), lower := (rows 97 262 7 42 88 160 80 128 256), losses := [] }

theorem u10869 : Upper (D 7) (R 7) [96,260,3,34,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10869 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10870 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 262 7 42 88 160 192 145 273), lower := (rows 97 262 7 42 88 160 192 128 256), losses := [] }

theorem u10870 : Upper (D 7) (R 7) [96,260,3,34,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10871 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 262 7 42 145 48 72 192 448), lower := (rows 97 262 7 42 145 48 72 128 256), losses := [] }

theorem u10871 : Upper (D 7) (R 7) [96,260,3,34,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10871 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10872 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 7 42 145 48 192 200 328), lower := (rows 97 262 7 42 145 48 192 128 256), losses := [] }

theorem u10872 : Upper (D 7) (R 7) [96,260,3,34,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10872 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10873 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 7 42 145 160 72 208 336), lower := (rows 97 262 7 42 145 160 72 128 256), losses := [] }

theorem u10873 : Upper (D 7) (R 7) [96,260,3,34,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10873 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10874 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 7 42 145 160 80 200 328), lower := (rows 97 262 7 42 145 160 80 128 256), losses := [] }

theorem u10874 : Upper (D 7) (R 7) [96,260,3,34,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10874 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10875 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 209, targets := 2 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 97 262 7 42 152 160 65 208 336), lower := (rows 97 262 7 42 152 160 65 128 256), losses := [] }

theorem u10875 : Upper (D 7) (R 7) [96,260,3,34,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10876 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 7 42 152 160 80 193 321), lower := (rows 97 262 7 42 152 160 80 128 256), losses := [] }

theorem u10876 : Upper (D 7) (R 7) [96,260,3,34,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10876 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10877 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 209, targets := 2 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 97 262 7 42 208 160 65 152 280), lower := (rows 97 262 7 42 208 160 65 128 256), losses := [] }

theorem u10877 : Upper (D 7) (R 7) [96,260,3,34,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10878 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 7 42 208 160 72 145 273), lower := (rows 97 262 7 42 208 160 72 128 256), losses := [] }

theorem u10878 : Upper (D 7) (R 7) [96,260,3,34,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10878 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10879 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 270, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 7 42 208 160 80 137 265), lower := (rows 97 262 7 42 208 160 80 128 256), losses := [] }

theorem u10879 : Upper (D 7) (R 7) [96,260,3,34,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10879 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10880 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 7 56 145 34 72 192 448), lower := (rows 97 262 7 56 145 34 72 128 256), losses := [] }

theorem u10880 : Upper (D 7) (R 7) [96,260,3,48,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10880 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10881 : Route 9 := (fun mask => (mask,id))

def c10881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u10881 : Upper (D 7) (R 7) [96,260,3,48,129,2,128] 13 := by
  apply FastRouting.sound _ _ [96,260,3,48,129,2,128] 13 (by decide) (choices 1) [8,64] r10881 c10881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u809
  · exact u810

def b10882 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 7 56 146 33 72 192 448), lower := (rows 97 262 7 56 146 33 72 128 256), losses := [] }

theorem u10882 : Upper (D 7) (R 7) [96,260,3,48,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10882 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10883 : Route 9 := (fun mask => (mask,id))

def c10883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u10883 : Upper (D 7) (R 7) [96,260,3,48,130,1,128] 13 := by
  apply FastRouting.sound _ _ [96,260,3,48,130,1,128] 13 (by decide) (choices 1) [8,64] r10883 c10883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u811
  · exact u812

def b10884 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 97 262 7 56 208 34 65 136 392), lower := (rows 97 262 7 56 208 34 65 128 256), losses := [] }

theorem u10884 : Upper (D 7) (R 7) [96,260,3,48,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10885 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 7 56 208 34 72 129 385), lower := (rows 97 262 7 56 208 34 72 128 256), losses := [] }

theorem u10885 : Upper (D 7) (R 7) [96,260,3,48,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10885 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10886 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 262 7 56 208 34 192 137 265), lower := (rows 97 262 7 56 208 34 192 128 256), losses := [] }

theorem u10886 : Upper (D 7) (R 7) [96,260,3,48,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10887 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 262, targets := 128 }], pairs := [(1,7),(2,7)], upper := (rows 97 262 7 137 146 40 80 224 352), lower := (rows 97 262 7 137 146 40 80 128 256), losses := [] }

theorem u10887 : Upper (D 7) (R 7) [96,260,3,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10887 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10888 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 7 137 146 40 96 208 336), lower := (rows 97 262 7 137 146 40 96 128 256), losses := [] }

theorem u10888 : Upper (D 7) (R 7) [96,260,3,129,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10888 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10889 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 7 137 146 48 96 200 328), lower := (rows 97 262 7 137 146 48 96 128 256), losses := [] }

theorem u10889 : Upper (D 7) (R 7) [96,260,3,129,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10889 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10890 : PairBound 9 := { available := 80, camps := [{ cop := 5, region := 217, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 262 7 137 176 34 72 208 336), lower := (rows 97 262 7 137 176 34 72 128 256), losses := [] }

theorem u10890 : Upper (D 7) (R 7) [96,260,3,129,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10890 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10891 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 7 137 176 34 80 200 328), lower := (rows 97 262 7 137 176 34 80 128 256), losses := [] }

theorem u10891 : Upper (D 7) (R 7) [96,260,3,129,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10891 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10892 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 113, targets := 2 },{ cop := 3, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 262 7 138 176 33 72 208 336), lower := (rows 97 262 7 138 176 33 72 128 256), losses := [] }

theorem u10892 : Upper (D 7) (R 7) [96,260,3,130,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10892 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10893 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 7 138 176 33 80 200 328), lower := (rows 97 262 7 138 176 33 80 128 256), losses := [] }

theorem u10893 : Upper (D 7) (R 7) [96,260,3,130,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10893 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10894 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 185, targets := 2 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 97 262 7 168 208 33 66 152 280), lower := (rows 97 262 7 168 208 33 66 128 256), losses := [] }

theorem u10894 : Upper (D 7) (R 7) [96,260,3,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10895 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 7 168 208 33 72 146 274), lower := (rows 97 262 7 168 208 33 72 128 256), losses := [] }

theorem u10895 : Upper (D 7) (R 7) [96,260,3,160,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10895 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10896 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 7 168 208 33 80 138 266), lower := (rows 97 262 7 168 208 33 80 128 256), losses := [] }

theorem u10896 : Upper (D 7) (R 7) [96,260,3,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10896 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10897 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 7 168 208 34 72 145 273), lower := (rows 97 262 7 168 208 34 72 128 256), losses := [] }

theorem u10897 : Upper (D 7) (R 7) [96,260,3,160,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10897 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10898 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 7 168 208 34 80 137 265), lower := (rows 97 262 7 168 208 34 80 128 256), losses := [] }

theorem u10898 : Upper (D 7) (R 7) [96,260,3,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10898 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10899 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 13 26 145 34 96 192 448), lower := (rows 97 262 13 26 145 34 96 128 256), losses := [] }

theorem u10899 : Upper (D 7) (R 7) [96,260,9,18,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10900 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 209, targets := 2 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(4,1)], upper := (rows 97 262 13 26 145 34 192 224 352), lower := (rows 97 262 13 26 145 34 192 128 256), losses := [{ target := 7, region := (rows 1 22 20 24 16 62 64 0 257), good := (rows 353 294 303 62 319 34 64 0 256) }] }

theorem u10900 : Upper (D 7) (R 7) [96,260,9,18,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10901 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 26 145 96 192 162 290), lower := (rows 97 262 13 26 145 96 192 128 256), losses := [] }

theorem u10901 : Upper (D 7) (R 7) [96,260,9,18,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10902 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 97 262 13 42 82 160 65 144 400), lower := (rows 97 262 13 42 82 160 65 128 256), losses := [] }

theorem u10902 : Upper (D 7) (R 7) [96,260,9,34,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10903 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 13 42 82 160 80 129 385), lower := (rows 97 262 13 42 82 160 80 128 256), losses := [] }

theorem u10903 : Upper (D 7) (R 7) [96,260,9,34,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10903 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10904 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 262 13 42 82 160 192 145 273), lower := (rows 97 262 13 42 82 160 192 128 256), losses := [] }

theorem u10904 : Upper (D 7) (R 7) [96,260,9,34,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10905 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,7),(1,5),(2,7),(4,5)], upper := (rows 97 262 13 42 145 160 66 208 336), lower := (rows 97 262 13 42 145 160 66 128 256), losses := [] }

theorem u10905 : Upper (D 7) (R 7) [96,260,9,34,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10906 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 13 42 145 160 80 194 322), lower := (rows 97 262 13 42 145 160 80 128 256), losses := [] }

theorem u10906 : Upper (D 7) (R 7) [96,260,9,34,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10906 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10907 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 13 42 208 160 65 146 274), lower := (rows 97 262 13 42 208 160 65 128 256), losses := [] }

theorem u10907 : Upper (D 7) (R 7) [96,260,9,34,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10908 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,7),(1,5),(2,7),(4,5)], upper := (rows 97 262 13 42 208 160 66 145 273), lower := (rows 97 262 13 42 208 160 66 128 256), losses := [] }

theorem u10908 : Upper (D 7) (R 7) [96,260,9,34,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10909 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 13 42 208 160 80 131 259), lower := (rows 97 262 13 42 208 160 80 128 256), losses := [] }

theorem u10909 : Upper (D 7) (R 7) [96,260,9,34,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10909 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10910 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 97 262 13 56 145 34 66 192 448), lower := (rows 97 262 13 56 145 34 66 128 256), losses := [] }

theorem u10910 : Upper (D 7) (R 7) [96,260,9,48,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10911 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(0,1),(1,0),(1,5),(4,5)], upper := (rows 97 262 13 56 145 34 192 194 322), lower := (rows 97 262 13 56 145 34 192 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 32 208 128 256), good := (rows 97 260 13 125 209 32 192 192 256) }] }

theorem u10911 : Upper (D 7) (R 7) [96,260,9,48,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10912 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 13 56 208 34 65 130 386), lower := (rows 97 262 13 56 208 34 65 128 256), losses := [] }

theorem u10912 : Upper (D 7) (R 7) [96,260,9,48,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10913 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 386, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 97 262 13 56 208 34 66 129 385), lower := (rows 97 262 13 56 208 34 66 128 256), losses := [] }

theorem u10913 : Upper (D 7) (R 7) [96,260,9,48,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10914 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 262 13 56 208 34 192 131 259), lower := (rows 97 262 13 56 208 34 192 128 256), losses := [] }

theorem u10914 : Upper (D 7) (R 7) [96,260,9,48,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10915 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 232, targets := 1 },{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1),(1,0),(3,0)], upper := (rows 97 262 13 138 19 48 192 224 352), lower := (rows 97 262 13 138 19 48 192 128 256), losses := [{ target := 0, region := (rows 0 6 4 28 16 48 253 177 305), good := (rows 480 334 462 202 506 504 192 192 256) }] }

theorem u10915 : Upper (D 7) (R 7) [96,260,9,130,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10915 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10916 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 138 19 96 192 176 304), lower := (rows 97 262 13 138 19 96 192 128 256), losses := [] }

theorem u10916 : Upper (D 7) (R 7) [96,260,9,130,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10917 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1),(1,0),(4,1)], upper := (rows 97 262 13 138 145 34 80 224 352), lower := (rows 97 262 13 138 145 34 80 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 46 80 129 257), good := (rows 480 302 430 170 464 34 80 128 256) }] }

theorem u10917 : Upper (D 7) (R 7) [96,260,9,130,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10917 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10918 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 13 138 145 34 96 208 336), lower := (rows 97 262 13 138 145 34 96 128 256), losses := [] }

theorem u10918 : Upper (D 7) (R 7) [96,260,9,130,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10919 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 13 138 145 48 96 194 322), lower := (rows 97 262 13 138 145 48 96 128 256), losses := [] }

theorem u10919 : Upper (D 7) (R 7) [96,260,9,130,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10919 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10919
end Delivery.IrregularNine14.P07
