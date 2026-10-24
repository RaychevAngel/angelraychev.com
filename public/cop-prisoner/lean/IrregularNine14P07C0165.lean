import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0012

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9900 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 290 76 138 82 33 80 129 385), lower := (rows 37 290 76 138 82 33 80 128 256), losses := [] }

theorem u9900 : Upper (D 7) (R 7) [36,288,72,130,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9900 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9901 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 76 138 82 33 192 145 273), lower := (rows 37 290 76 138 82 33 192 128 256), losses := [] }

theorem u9901 : Upper (D 7) (R 7) [36,288,72,130,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9902 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 290 76 138 82 48 65 129 385), lower := (rows 37 290 76 138 82 48 65 128 256), losses := [] }

theorem u9902 : Upper (D 7) (R 7) [36,288,72,130,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9902 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9903 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 290 76 138 82 48 192 129 257), lower := (rows 37 290 76 138 82 48 192 128 256), losses := [] }

theorem u9903 : Upper (D 7) (R 7) [36,288,72,130,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9903 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9904 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 290 76 138 145 48 65 194 322), lower := (rows 37 290 76 138 145 48 65 128 256), losses := [] }

theorem u9904 : Upper (D 7) (R 7) [36,288,72,130,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9904 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9905 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 290 76 138 145 48 66 193 321), lower := (rows 37 290 76 138 145 48 66 128 256), losses := [] }

theorem u9905 : Upper (D 7) (R 7) [36,288,72,130,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9905 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9906 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 117, targets := 2 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 290 76 138 208 33 65 146 274), lower := (rows 37 290 76 138 208 33 65 128 256), losses := [] }

theorem u9906 : Upper (D 7) (R 7) [36,288,72,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9907 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 76 138 208 33 66 145 273), lower := (rows 37 290 76 138 208 33 66 128 256), losses := [] }

theorem u9907 : Upper (D 7) (R 7) [36,288,72,130,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9908 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 290 76 138 208 33 80 131 259), lower := (rows 37 290 76 138 208 33 80 128 256), losses := [] }

theorem u9908 : Upper (D 7) (R 7) [36,288,72,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9908 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9909 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 132, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 37 290 196 11 82 40 65 144 400), lower := (rows 37 290 196 11 82 40 65 128 256), losses := [] }

theorem u9909 : Upper (D 7) (R 7) [36,288,192,3,66,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9909 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9910 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 37 290 196 11 82 40 80 129 385), lower := (rows 37 290 196 11 82 40 80 128 256), losses := [] }

theorem u9910 : Upper (D 7) (R 7) [36,288,192,3,66,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9910 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9911 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 290 196 11 82 40 192 145 273), lower := (rows 37 290 196 11 82 40 192 128 256), losses := [] }

theorem u9911 : Upper (D 7) (R 7) [36,288,192,3,66,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9911 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9912 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 418, targets := 65 },{ cop := 4, region := 132, targets := 1 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 37 290 196 25 82 40 65 130 386), lower := (rows 37 290 196 25 82 40 65 128 256), losses := [] }

theorem u9912 : Upper (D 7) (R 7) [36,288,192,17,66,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9912 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9913 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 37 290 196 25 82 40 66 129 385), lower := (rows 37 290 196 25 82 40 66 128 256), losses := [] }

theorem u9913 : Upper (D 7) (R 7) [36,288,192,17,66,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9913 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9914 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 290 196 25 82 40 192 131 259), lower := (rows 37 290 196 25 82 40 192 128 256), losses := [] }

theorem u9914 : Upper (D 7) (R 7) [36,288,192,17,66,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9914 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9915 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 37 290 196 26 81 40 65 130 386), lower := (rows 37 290 196 26 81 40 65 128 256), losses := [] }

theorem u9915 : Upper (D 7) (R 7) [36,288,192,18,65,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9915 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9916 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 132, targets := 34 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 37 290 196 26 81 40 66 129 385), lower := (rows 37 290 196 26 81 40 66 128 256), losses := [] }

theorem u9916 : Upper (D 7) (R 7) [36,288,192,18,65,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9916 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9917 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 290 196 26 81 40 192 131 259), lower := (rows 37 290 196 26 81 40 192 128 256), losses := [] }

theorem u9917 : Upper (D 7) (R 7) [36,288,192,18,65,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9917 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9918 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 148, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 196 74 146 33 65 152 280), lower := (rows 37 290 196 74 146 33 65 128 256), losses := [] }

theorem u9918 : Upper (D 7) (R 7) [36,288,192,66,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9919 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 290 196 74 146 33 72 145 273), lower := (rows 37 290 196 74 146 33 72 128 256), losses := [] }

theorem u9919 : Upper (D 7) (R 7) [36,288,192,66,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9919 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9920 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 290 196 74 146 33 80 137 265), lower := (rows 37 290 196 74 146 33 80 128 256), losses := [] }

theorem u9920 : Upper (D 7) (R 7) [36,288,192,66,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9920 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9921 : Route 9 := (fun mask => (mask,id))

def c9921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9921 : Upper (D 7) (R 7) [36,288,192,66,130,8,1] 13 := by
  apply FastRouting.sound _ _ [36,288,192,66,130,8,1] 13 (by decide) (choices 1) [1,16] r9921 c9921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u771
  · exact u772

def b9922 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 290 196 74 146 40 80 129 257), lower := (rows 37 290 196 74 146 40 80 128 256), losses := [] }

theorem u9922 : Upper (D 7) (R 7) [36,288,192,66,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9922 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9923 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 148, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 196 74 152 33 65 146 274), lower := (rows 37 290 196 74 152 33 65 128 256), losses := [] }

theorem u9923 : Upper (D 7) (R 7) [36,288,192,66,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9924 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 72, targets := 161 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,7)], upper := (rows 37 290 196 74 152 33 66 145 273), lower := (rows 37 290 196 74 152 33 66 128 256), losses := [] }

theorem u9924 : Upper (D 7) (R 7) [36,288,192,66,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9925 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 290 196 74 152 33 80 131 259), lower := (rows 37 290 196 74 152 33 80 128 256), losses := [] }

theorem u9925 : Upper (D 7) (R 7) [36,288,192,66,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9925 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9926 : Route 9 := (fun mask => (mask,id))

def c9926 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9926 : Upper (D 7) (R 7) [36,288,192,66,136,2,1] 13 := by
  apply FastRouting.sound _ _ [36,288,192,66,136,2,1] 13 (by decide) (choices 1) [1,16] r9926 c9926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u773
  · exact u774

def b9927 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 290 196 74 152 34 80 129 257), lower := (rows 37 290 196 74 152 34 80 128 256), losses := [] }

theorem u9927 : Upper (D 7) (R 7) [36,288,192,66,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9927 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9928 : PairBound 9 := { available := 160, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 7 25 208 40 66 160 416), lower := (rows 37 322 7 25 208 40 66 128 256), losses := [] }

theorem u9928 : Upper (D 7) (R 7) [36,320,3,17,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9928 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9929 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 322 7 25 208 40 96 130 386), lower := (rows 37 322 7 25 208 40 96 128 256), losses := [] }

theorem u9929 : Upper (D 7) (R 7) [36,320,3,17,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9929 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9930 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 7 25 208 40 192 162 290), lower := (rows 37 322 7 25 208 40 192 128 256), losses := [] }

theorem u9930 : Upper (D 7) (R 7) [36,320,3,17,192,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9930 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9931 : PairBound 9 := { available := 40, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 37 322 7 25 208 160 66 168 296), lower := (rows 37 322 7 25 208 160 66 128 256), losses := [] }

theorem u9931 : Upper (D 7) (R 7) [36,320,3,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9932 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 322 7 25 208 160 72 162 290), lower := (rows 37 322 7 25 208 160 72 128 256), losses := [] }

theorem u9932 : Upper (D 7) (R 7) [36,320,3,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9932 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9933 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 5, region := 80, targets := 2 }], pairs := [(1,0),(3,1),(4,0),(4,1)], upper := (rows 37 322 7 25 208 160 96 138 266), lower := (rows 37 322 7 25 208 160 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 176 176 249 128 256), good := (rows 125 320 77 121 240 240 112 240 256) }] }

theorem u9933 : Upper (D 7) (R 7) [36,320,3,17,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9934 : PairBound 9 := { available := 136, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 37 322 7 26 112 160 65 136 392), lower := (rows 37 322 7 26 112 160 65 128 256), losses := [] }

theorem u9934 : Upper (D 7) (R 7) [36,320,3,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9935 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(2,6)], upper := (rows 37 322 7 26 112 160 72 129 385), lower := (rows 37 322 7 26 112 160 72 128 256), losses := [] }

theorem u9935 : Upper (D 7) (R 7) [36,320,3,18,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9935 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9936 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 7 26 112 160 192 137 265), lower := (rows 37 322 7 26 112 160 192 128 256), losses := [] }

theorem u9936 : Upper (D 7) (R 7) [36,320,3,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9937 : PairBound 9 := { available := 40, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 322 7 26 208 160 65 168 296), lower := (rows 37 322 7 26 208 160 65 128 256), losses := [] }

theorem u9937 : Upper (D 7) (R 7) [36,320,3,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9938 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(2,6)], upper := (rows 37 322 7 26 208 160 72 161 289), lower := (rows 37 322 7 26 208 160 72 128 256), losses := [] }

theorem u9938 : Upper (D 7) (R 7) [36,320,3,18,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9938 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9939 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 37 322 7 26 208 160 96 137 265), lower := (rows 37 322 7 26 208 160 96 128 256), losses := [] }

theorem u9939 : Upper (D 7) (R 7) [36,320,3,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9940 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 2, region := 80, targets := 32 }], pairs := [(1,0),(1,5),(1,7),(4,5)], upper := (rows 37 322 7 56 81 160 66 136 392), lower := (rows 37 322 7 56 81 160 66 128 256), losses := [] }

theorem u9940 : Upper (D 7) (R 7) [36,320,3,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9941 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 322 7 56 81 160 72 130 386), lower := (rows 37 322 7 56 81 160 72 128 256), losses := [] }

theorem u9941 : Upper (D 7) (R 7) [36,320,3,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9941 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9942 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(3,1)], upper := (rows 37 322 7 56 81 160 192 138 266), lower := (rows 37 322 7 56 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 25 17 224 224 128 256), good := (rows 125 352 29 120 121 224 224 224 256) }] }

theorem u9942 : Upper (D 7) (R 7) [36,320,3,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9943 : PairBound 9 := { available := 160, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 7 73 152 48 66 160 416), lower := (rows 37 322 7 73 152 48 66 128 256), losses := [] }

theorem u9943 : Upper (D 7) (R 7) [36,320,3,65,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9943 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9944 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 7 73 152 48 96 130 386), lower := (rows 37 322 7 73 152 48 96 128 256), losses := [] }

theorem u9944 : Upper (D 7) (R 7) [36,320,3,65,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9944 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9945 : Route 9 := (fun mask => (mask,id))

def c9945 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9945 : Upper (D 7) (R 7) [36,320,3,65,136,16,128] 13 := by
  apply FastRouting.sound _ _ [36,320,3,65,136,16,128] 13 (by decide) (choices 1) [2,32] r9945 c9945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u775
  · exact u776

def b9946 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 2, region := 72, targets := 32 }], pairs := [(1,0),(1,5),(1,7),(3,5)], upper := (rows 37 322 7 73 152 160 66 176 304), lower := (rows 37 322 7 73 152 160 66 128 256), losses := [] }

theorem u9946 : Upper (D 7) (R 7) [36,320,3,65,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9947 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 3, region := 418, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 322 7 73 152 160 80 162 290), lower := (rows 37 322 7 73 152 160 80 128 256), losses := [] }

theorem u9947 : Upper (D 7) (R 7) [36,320,3,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9947 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9948 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 322 7 73 152 160 96 146 274), lower := (rows 37 322 7 73 152 160 96 128 256), losses := [] }

theorem u9948 : Upper (D 7) (R 7) [36,320,3,65,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9949 : PairBound 9 := { available := 160, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 7 88 145 40 66 160 416), lower := (rows 37 322 7 88 145 40 66 128 256), losses := [] }

theorem u9949 : Upper (D 7) (R 7) [36,320,3,80,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9949 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9950 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 144, targets := 96 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 37 322 7 88 145 40 96 130 386), lower := (rows 37 322 7 88 145 40 96 128 256), losses := [] }

theorem u9950 : Upper (D 7) (R 7) [36,320,3,80,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9950 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9951 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 7 88 145 40 192 162 290), lower := (rows 37 322 7 88 145 40 192 128 256), losses := [] }

theorem u9951 : Upper (D 7) (R 7) [36,320,3,80,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9951 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9952 : PairBound 9 := { available := 40, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 322 7 88 145 160 66 168 296), lower := (rows 37 322 7 88 145 160 66 128 256), losses := [] }

theorem u9952 : Upper (D 7) (R 7) [36,320,3,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9953 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 322 7 88 145 160 72 162 290), lower := (rows 37 322 7 88 145 160 72 128 256), losses := [] }

theorem u9953 : Upper (D 7) (R 7) [36,320,3,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9953 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9954 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 258, targets := 32 },{ cop := 3, region := 258, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 322 7 88 145 160 96 138 266), lower := (rows 37 322 7 88 145 160 96 128 256), losses := [] }

theorem u9954 : Upper (D 7) (R 7) [36,320,3,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9955 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 7 88 146 40 65 160 416), lower := (rows 37 322 7 88 146 40 65 128 256), losses := [] }

theorem u9955 : Upper (D 7) (R 7) [36,320,3,80,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9955 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9956 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 7 88 146 40 96 129 385), lower := (rows 37 322 7 88 146 40 96 128 256), losses := [] }

theorem u9956 : Upper (D 7) (R 7) [36,320,3,80,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9956 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9957 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 7 88 146 40 192 161 289), lower := (rows 37 322 7 88 146 40 192 128 256), losses := [] }

theorem u9957 : Upper (D 7) (R 7) [36,320,3,80,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9957 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9958 : PairBound 9 := { available := 40, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 322 7 88 146 160 65 168 296), lower := (rows 37 322 7 88 146 160 65 128 256), losses := [] }

theorem u9958 : Upper (D 7) (R 7) [36,320,3,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9959 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 322 7 88 146 160 72 161 289), lower := (rows 37 322 7 88 146 160 72 128 256), losses := [] }

theorem u9959 : Upper (D 7) (R 7) [36,320,3,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9959 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9959
end Delivery.IrregularNine14.P07
