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

def b10920 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 97 262 13 138 176 33 66 208 336), lower := (rows 97 262 13 138 176 33 66 128 256), losses := [] }

theorem u10920 : Upper (D 7) (R 7) [96,260,9,130,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10921 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 13 138 176 33 80 194 322), lower := (rows 97 262 13 138 176 33 80 128 256), losses := [] }

theorem u10921 : Upper (D 7) (R 7) [96,260,9,130,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10921 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10922 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 482, targets := 1 },{ cop := 4, region := 232, targets := 1 },{ cop := 5, region := 193, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 97 262 13 152 19 34 192 224 352), lower := (rows 97 262 13 152 19 34 192 128 256), losses := [{ target := 1, region := (rows 33 0 20 24 16 32 253 161 289), good := (rows 481 324 461 220 477 481 192 192 256) }] }

theorem u10922 : Upper (D 7) (R 7) [96,260,9,144,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10923 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 152 19 96 192 162 290), lower := (rows 97 262 13 152 19 96 192 128 256), losses := [] }

theorem u10923 : Upper (D 7) (R 7) [96,260,9,144,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10924 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 140, targets := 2 },{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 97 262 13 168 19 34 80 192 448), lower := (rows 97 262 13 168 19 34 80 128 256), losses := [] }

theorem u10924 : Upper (D 7) (R 7) [96,260,9,160,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10924 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10925 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 3, region := 69, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(4,5)], upper := (rows 97 262 13 168 19 34 192 208 336), lower := (rows 97 262 13 168 19 34 192 128 256), losses := [] }

theorem u10925 : Upper (D 7) (R 7) [96,260,9,160,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10926 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 13 168 82 34 65 144 400), lower := (rows 97 262 13 168 82 34 65 128 256), losses := [] }

theorem u10926 : Upper (D 7) (R 7) [96,260,9,160,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10927 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 13 168 82 34 80 129 385), lower := (rows 97 262 13 168 82 34 80 128 256), losses := [] }

theorem u10927 : Upper (D 7) (R 7) [96,260,9,160,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10927 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10928 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 3, region := 69, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(4,5)], upper := (rows 97 262 13 168 82 34 192 145 273), lower := (rows 97 262 13 168 82 34 192 128 256), losses := [] }

theorem u10928 : Upper (D 7) (R 7) [96,260,9,160,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10929 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 97 262 13 168 145 34 66 208 336), lower := (rows 97 262 13 168 145 34 66 128 256), losses := [] }

theorem u10929 : Upper (D 7) (R 7) [96,260,9,160,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10930 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 262 13 168 145 34 80 194 322), lower := (rows 97 262 13 168 145 34 80 128 256), losses := [] }

theorem u10930 : Upper (D 7) (R 7) [96,260,9,160,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10930 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10931 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 85, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 97 262 13 168 208 34 65 146 274), lower := (rows 97 262 13 168 208 34 65 128 256), losses := [] }

theorem u10931 : Upper (D 7) (R 7) [96,260,9,160,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10932 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 97 262 13 168 208 34 66 145 273), lower := (rows 97 262 13 168 208 34 66 128 256), losses := [] }

theorem u10932 : Upper (D 7) (R 7) [96,260,9,160,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10933 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 13 168 208 34 80 131 259), lower := (rows 97 262 13 168 208 34 80 128 256), losses := [] }

theorem u10933 : Upper (D 7) (R 7) [96,260,9,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10933 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10934 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 169, targets := 2 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(1,6),(3,1)], upper := (rows 97 262 14 56 82 160 65 129 385), lower := (rows 97 262 14 56 82 160 65 128 256), losses := [{ target := 6, region := (rows 1 18 28 24 16 241 0 193 321), good := (rows 417 262 14 62 446 160 417 160 256) }] }

theorem u10934 : Upper (D 7) (R 7) [96,260,10,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10935 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 262 14 56 82 160 192 129 257), lower := (rows 97 262 14 56 82 160 192 128 256), losses := [] }

theorem u10935 : Upper (D 7) (R 7) [96,260,10,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10936 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(3,1)], upper := (rows 97 262 14 137 19 48 192 224 352), lower := (rows 97 262 14 137 19 48 192 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 48 249 177 305), good := (rows 480 262 78 462 498 496 192 192 256) }] }

theorem u10936 : Upper (D 7) (R 7) [96,260,10,129,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10936 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10937 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 137 19 96 192 176 304), lower := (rows 97 262 14 137 19 96 192 128 256), losses := [] }

theorem u10937 : Upper (D 7) (R 7) [96,260,10,129,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10938 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 105, targets := 2 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 262 14 137 146 33 80 224 352), lower := (rows 97 262 14 137 146 33 80 128 256), losses := [] }

theorem u10938 : Upper (D 7) (R 7) [96,260,10,129,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10938 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10939 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 14 137 146 33 96 208 336), lower := (rows 97 262 14 137 146 33 96 128 256), losses := [] }

theorem u10939 : Upper (D 7) (R 7) [96,260,10,129,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10940 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 233, targets := 2 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(3,1)], upper := (rows 97 262 14 152 19 33 192 224 352), lower := (rows 97 262 14 152 19 33 192 128 256), losses := [{ target := 0, region := (rows 0 18 28 24 16 32 249 161 289), good := (rows 480 262 78 222 478 480 192 192 256) }] }

theorem u10940 : Upper (D 7) (R 7) [96,260,10,144,3,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10941 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 152 19 96 192 161 289), lower := (rows 97 262 14 152 19 96 192 128 256), losses := [] }

theorem u10941 : Upper (D 7) (R 7) [96,260,10,144,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10942 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 262 14 168 19 33 80 192 448), lower := (rows 97 262 14 168 19 33 80 128 256), losses := [] }

theorem u10942 : Upper (D 7) (R 7) [96,260,10,160,3,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10942 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10943 : Route 9 := (fun mask => (mask,id))

def c10943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u10943 : Upper (D 7) (R 7) [96,260,10,160,3,1,128] 13 := by
  apply FastRouting.sound _ _ [96,260,10,160,3,1,128] 13 (by decide) (choices 1) [16,64] r10943 c10943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u813
  · exact u814

def b10944 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 262 14 168 19 48 65 192 448), lower := (rows 97 262 14 168 19 48 65 128 256), losses := [] }

theorem u10944 : Upper (D 7) (R 7) [96,260,10,160,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10944 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10945 : Route 9 := (fun mask => (mask,id))

def c10945 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u10945 : Upper (D 7) (R 7) [96,260,10,160,3,16,128] 13 := by
  apply FastRouting.sound _ _ [96,260,10,160,3,16,128] 13 (by decide) (choices 1) [1,64] r10945 c10945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u815
  · exact u816

def b10946 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 14 168 82 33 65 144 400), lower := (rows 97 262 14 168 82 33 65 128 256), losses := [] }

theorem u10946 : Upper (D 7) (R 7) [96,260,10,160,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10947 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 14 168 82 33 80 129 385), lower := (rows 97 262 14 168 82 33 80 128 256), losses := [] }

theorem u10947 : Upper (D 7) (R 7) [96,260,10,160,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10947 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10948 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 169, targets := 2 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,0)], upper := (rows 97 262 14 168 82 33 192 145 273), lower := (rows 97 262 14 168 82 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 32 200 128 256), good := (rows 96 278 94 232 82 32 192 192 256) }] }

theorem u10948 : Upper (D 7) (R 7) [96,260,10,160,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10949 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 14 168 146 33 65 208 336), lower := (rows 97 262 14 168 146 33 65 128 256), losses := [] }

theorem u10949 : Upper (D 7) (R 7) [96,260,10,160,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10950 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 105, targets := 2 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 262 14 168 146 33 80 193 321), lower := (rows 97 262 14 168 146 33 80 128 256), losses := [] }

theorem u10950 : Upper (D 7) (R 7) [96,260,10,160,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10950 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10951 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 14 168 208 33 65 146 274), lower := (rows 97 262 14 168 208 33 65 128 256), losses := [] }

theorem u10951 : Upper (D 7) (R 7) [96,260,10,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10952 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 185, targets := 2 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,1),(3,1),(4,1),(4,5)], upper := (rows 97 262 14 168 208 33 66 145 273), lower := (rows 97 262 14 168 208 33 66 128 256), losses := [] }

theorem u10952 : Upper (D 7) (R 7) [96,260,10,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10953 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 14 168 208 33 80 131 259), lower := (rows 97 262 14 168 208 33 80 128 256), losses := [] }

theorem u10953 : Upper (D 7) (R 7) [96,260,10,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10953 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10954 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 1, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 97 262 28 11 50 160 65 192 448), lower := (rows 97 262 28 11 50 160 65 128 256), losses := [] }

theorem u10954 : Upper (D 7) (R 7) [96,260,24,3,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10955 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 262 28 11 50 160 192 193 321), lower := (rows 97 262 28 11 50 160 192 128 256), losses := [] }

theorem u10955 : Upper (D 7) (R 7) [96,260,24,3,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10956 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 209, targets := 2 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 97 262 28 11 145 34 192 224 352), lower := (rows 97 262 28 11 145 34 192 128 256), losses := [{ target := 1, region := (rows 33 0 12 8 57 32 249 161 289), good := (rows 497 260 92 477 465 497 192 192 256) }] }

theorem u10956 : Upper (D 7) (R 7) [96,260,24,3,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10957 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 28 11 145 96 192 162 290), lower := (rows 97 262 28 11 145 96 192 128 256), losses := [] }

theorem u10957 : Upper (D 7) (R 7) [96,260,24,3,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10958 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 225, targets := 2 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(2,0)], upper := (rows 97 262 28 11 146 33 192 224 352), lower := (rows 97 262 28 11 146 33 192 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 24 32 249 161 289), good := (rows 480 262 94 478 210 480 192 192 256) }] }

theorem u10958 : Upper (D 7) (R 7) [96,260,24,3,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10959 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 28 11 146 96 192 161 289), lower := (rows 97 262 28 11 146 96 192 128 256), losses := [] }

theorem u10959 : Upper (D 7) (R 7) [96,260,24,3,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10960 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 1, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 97 262 28 42 82 33 192 129 385), lower := (rows 97 262 28 42 82 33 192 128 256), losses := [] }

theorem u10960 : Upper (D 7) (R 7) [96,260,24,34,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10961 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 262 28 42 82 160 192 129 257), lower := (rows 97 262 28 42 82 160 192 128 256), losses := [] }

theorem u10961 : Upper (D 7) (R 7) [96,260,24,34,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10962 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 81, targets := 2 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 97 262 28 42 145 160 65 194 322), lower := (rows 97 262 28 42 145 160 65 128 256), losses := [{ target := 1, region := (rows 189 0 12 8 176 176 255 128 256), good := (rows 113 325 125 125 241 241 65 241 256) }] }

theorem u10962 : Upper (D 7) (R 7) [96,260,24,34,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10963 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 177, targets := 2 },{ cop := 0, region := 144, targets := 32 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(4,1),(4,5)], upper := (rows 97 262 28 42 145 160 66 193 321), lower := (rows 97 262 28 42 145 160 66 128 256), losses := [] }

theorem u10963 : Upper (D 7) (R 7) [96,260,24,34,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10964 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 28 42 208 33 65 130 386), lower := (rows 97 262 28 42 208 33 65 128 256), losses := [] }

theorem u10964 : Upper (D 7) (R 7) [96,260,24,34,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10965 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 105, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,1)], upper := (rows 97 262 28 42 208 33 66 129 385), lower := (rows 97 262 28 42 208 33 66 128 256), losses := [] }

theorem u10965 : Upper (D 7) (R 7) [96,260,24,34,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10966 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 262 28 42 208 33 192 131 259), lower := (rows 97 262 28 42 208 33 192 128 256), losses := [] }

theorem u10966 : Upper (D 7) (R 7) [96,260,24,34,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10967 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 81, targets := 2 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 97 262 28 42 208 160 65 131 259), lower := (rows 97 262 28 42 208 160 65 128 256), losses := [{ target := 1, region := (rows 189 0 12 8 176 176 255 128 256), good := (rows 113 325 125 125 241 241 65 241 256) }] }

theorem u10967 : Upper (D 7) (R 7) [96,260,24,34,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10968 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 177, targets := 2 },{ cop := 0, region := 144, targets := 32 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(4,1),(4,5)], upper := (rows 97 262 28 42 208 160 66 129 257), lower := (rows 97 262 28 42 208 160 66 128 256), losses := [] }

theorem u10968 : Upper (D 7) (R 7) [96,260,24,34,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10969 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 169, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(3,1)], upper := (rows 97 262 28 137 146 33 66 224 352), lower := (rows 97 262 28 137 146 33 66 128 256), losses := [] }

theorem u10969 : Upper (D 7) (R 7) [96,260,24,129,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10970 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 28 137 146 33 96 194 322), lower := (rows 97 262 28 137 146 33 96 128 256), losses := [] }

theorem u10970 : Upper (D 7) (R 7) [96,260,24,129,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10971 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 262 28 137 176 34 65 194 322), lower := (rows 97 262 28 137 176 34 65 128 256), losses := [] }

theorem u10971 : Upper (D 7) (R 7) [96,260,24,129,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10972 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 262 28 137 176 34 66 193 321), lower := (rows 97 262 28 137 176 34 66 128 256), losses := [] }

theorem u10972 : Upper (D 7) (R 7) [96,260,24,129,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10973 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 28 138 176 33 65 194 322), lower := (rows 97 262 28 138 176 33 65 128 256), losses := [] }

theorem u10973 : Upper (D 7) (R 7) [96,260,24,130,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10974 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 262 28 138 176 33 66 193 321), lower := (rows 97 262 28 138 176 33 66 128 256), losses := [] }

theorem u10974 : Upper (D 7) (R 7) [96,260,24,130,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10975 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 262 28 168 208 33 66 131 259), lower := (rows 97 262 28 168 208 33 66 128 256), losses := [] }

theorem u10975 : Upper (D 7) (R 7) [96,260,24,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10976 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 262 28 168 208 34 66 129 257), lower := (rows 97 262 28 168 208 34 66 128 256), losses := [] }

theorem u10976 : Upper (D 7) (R 7) [96,260,24,160,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10977 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 262 38 11 88 160 65 144 400), lower := (rows 97 262 38 11 88 160 65 128 256), losses := [] }

theorem u10977 : Upper (D 7) (R 7) [96,260,34,3,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10978 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 38 11 88 160 80 129 385), lower := (rows 97 262 38 11 88 160 80 128 256), losses := [] }

theorem u10978 : Upper (D 7) (R 7) [96,260,34,3,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10978 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10979 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 262 38 11 88 160 192 145 273), lower := (rows 97 262 38 11 88 160 192 128 256), losses := [] }

theorem u10979 : Upper (D 7) (R 7) [96,260,34,3,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10979
end Delivery.IrregularNine14.P07
