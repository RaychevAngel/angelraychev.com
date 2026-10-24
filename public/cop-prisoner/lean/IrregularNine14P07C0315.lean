import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0086

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18900 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 35 70 14 168 208 288 81 145 273), lower := (rows 35 70 14 168 208 288 64 128 256), losses := [] }

theorem u18900 : Upper (D 7) (R 7) [34,68,10,160,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18900 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18901 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 168 273 33 208 208 464), lower := (rows 35 70 14 168 273 33 64 128 256), losses := [] }

theorem u18901 : Upper (D 7) (R 7) [34,68,10,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18902 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 35 70 14 168 273 48 193 193 449), lower := (rows 35 70 14 168 273 48 64 128 256), losses := [] }

theorem u18902 : Upper (D 7) (R 7) [34,68,10,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18902 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18903 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 168 273 96 209 145 401), lower := (rows 35 70 14 168 273 96 64 128 256), losses := [] }

theorem u18903 : Upper (D 7) (R 7) [34,68,10,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18904 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 70 14 168 273 160 81 209 337), lower := (rows 35 70 14 168 273 160 64 128 256), losses := [] }

theorem u18904 : Upper (D 7) (R 7) [34,68,10,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18905 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 168 336 33 209 145 401), lower := (rows 35 70 14 168 336 33 64 128 256), losses := [] }

theorem u18905 : Upper (D 7) (R 7) [34,68,10,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18906 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 14 168 336 48 193 129 385), lower := (rows 35 70 14 168 336 48 64 128 256), losses := [] }

theorem u18906 : Upper (D 7) (R 7) [34,68,10,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18906 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18907 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 70 14 168 336 160 81 145 273), lower := (rows 35 70 14 168 336 160 64 128 256), losses := [] }

theorem u18907 : Upper (D 7) (R 7) [34,68,10,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18908 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 168 400 33 81 209 337), lower := (rows 35 70 14 168 400 33 64 128 256), losses := [] }

theorem u18908 : Upper (D 7) (R 7) [34,68,10,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18909 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 14 168 400 48 65 193 321), lower := (rows 35 70 14 168 400 48 64 128 256), losses := [] }

theorem u18909 : Upper (D 7) (R 7) [34,68,10,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18909 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18910 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 168 400 96 81 145 273), lower := (rows 35 70 14 168 400 96 64 128 256), losses := [] }

theorem u18910 : Upper (D 7) (R 7) [34,68,10,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18911 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 14 265 81 48 224 160 416), lower := (rows 35 70 14 265 81 48 64 128 256), losses := [] }

theorem u18911 : Upper (D 7) (R 7) [34,68,10,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18911 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18912 : Route 9 := (fun mask => (mask,id))

def c18912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u18912 : Upper (D 7) (R 7) [34,68,10,257,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,10,257,65,128] 13 (by decide) (choices 1) [16,32,128] r18912 c18912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5186
  · exact u5187
  · exact u5188

def b18913 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 265 112 33 208 144 400), lower := (rows 35 70 14 265 112 33 64 128 256), losses := [] }

theorem u18913 : Upper (D 7) (R 7) [34,68,10,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18914 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 14 265 112 48 193 129 385), lower := (rows 35 70 14 265 112 48 64 128 256), losses := [] }

theorem u18914 : Upper (D 7) (R 7) [34,68,10,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18914 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18915 : Route 9 := (fun mask => (mask,id))

def c18915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18915 : Upper (D 7) (R 7) [34,68,10,257,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,10,257,96,128] 13 (by decide) (choices 1) [1,16,128] r18915 c18915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5189
  · exact u5190
  · exact u5191

def b18916 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 35 70 14 265 145 48 224 224 480), lower := (rows 35 70 14 265 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 48 113 177 305), good := (rows 482 70 14 462 496 496 64 128 256) }] }

theorem u18916 : Upper (D 7) (R 7) [34,68,10,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18916 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18917 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 265 145 96 240 176 432), lower := (rows 35 70 14 265 145 96 64 128 256), losses := [] }

theorem u18917 : Upper (D 7) (R 7) [34,68,10,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18918 : Route 9 := (fun mask => (mask,id))

def c18918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18918 : Upper (D 7) (R 7) [34,68,10,257,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,10,257,129,128] 13 (by decide) (choices 1) [16,32] r18918 c18918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5192
  · exact u5193

def b18919 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 265 176 33 208 208 464), lower := (rows 35 70 14 265 176 33 64 128 256), losses := [] }

theorem u18919 : Upper (D 7) (R 7) [34,68,10,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18920 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 14 265 176 48 193 193 449), lower := (rows 35 70 14 265 176 48 64 128 256), losses := [] }

theorem u18920 : Upper (D 7) (R 7) [34,68,10,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18920 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18921 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 265 176 96 209 145 401), lower := (rows 35 70 14 265 176 96 64 128 256), losses := [] }

theorem u18921 : Upper (D 7) (R 7) [34,68,10,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18922 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 14 265 176 160 81 209 337), lower := (rows 35 70 14 265 176 160 64 128 256), losses := [] }

theorem u18922 : Upper (D 7) (R 7) [34,68,10,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18923 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 265 208 33 240 176 432), lower := (rows 35 70 14 265 208 33 64 128 256), losses := [] }

theorem u18923 : Upper (D 7) (R 7) [34,68,10,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18924 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 14 265 208 48 225 161 417), lower := (rows 35 70 14 265 208 48 64 128 256), losses := [] }

theorem u18924 : Upper (D 7) (R 7) [34,68,10,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18924 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18925 : Route 9 := (fun mask => (mask,id))

def c18925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18925 : Upper (D 7) (R 7) [34,68,10,257,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,10,257,192,128] 13 (by decide) (choices 1) [1,16,32] r18925 c18925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5194
  · exact u5195
  · exact u5196

def b18926 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 280 112 33 193 129 385), lower := (rows 35 70 14 280 112 33 64 128 256), losses := [] }

theorem u18926 : Upper (D 7) (R 7) [34,68,10,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18927 : Route 9 := (fun mask => (mask,id))

def c18927 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18927 : Upper (D 7) (R 7) [34,68,10,272,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,10,272,96,128] 13 (by decide) (choices 1) [1,128] r18927 c18927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5197
  · exact u5198

def b18928 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 280 145 33 224 224 480), lower := (rows 35 70 14 280 145 33 64 128 256), losses := [] }

theorem u18928 : Upper (D 7) (R 7) [34,68,10,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18929 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 280 145 96 225 161 417), lower := (rows 35 70 14 280 145 96 64 128 256), losses := [] }

theorem u18929 : Upper (D 7) (R 7) [34,68,10,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18930 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(1,7),(2,7),(3,1),(4,1)], upper := (rows 35 70 14 280 145 160 97 225 353), lower := (rows 35 70 14 280 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 18 28 24 16 32 65 0 257), good := (rows 355 70 14 286 351 32 64 0 256) }] }

theorem u18930 : Upper (D 7) (R 7) [34,68,10,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18931 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 280 176 33 193 193 449), lower := (rows 35 70 14 280 176 33 64 128 256), losses := [] }

theorem u18931 : Upper (D 7) (R 7) [34,68,10,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18932 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 280 176 96 193 129 385), lower := (rows 35 70 14 280 176 96 64 128 256), losses := [] }

theorem u18932 : Upper (D 7) (R 7) [34,68,10,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18933 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 14 280 176 160 65 193 321), lower := (rows 35 70 14 280 176 160 64 128 256), losses := [] }

theorem u18933 : Upper (D 7) (R 7) [34,68,10,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18934 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 280 208 33 225 161 417), lower := (rows 35 70 14 280 208 33 64 128 256), losses := [] }

theorem u18934 : Upper (D 7) (R 7) [34,68,10,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18935 : Route 9 := (fun mask => (mask,id))

def c18935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18935 : Upper (D 7) (R 7) [34,68,10,272,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,10,272,192,128] 13 (by decide) (choices 1) [1,32] r18935 c18935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5199
  · exact u5200

def b18936 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 296 145 33 208 208 464), lower := (rows 35 70 14 296 145 33 64 128 256), losses := [] }

theorem u18936 : Upper (D 7) (R 7) [34,68,10,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18937 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 35 70 14 296 145 48 193 193 449), lower := (rows 35 70 14 296 145 48 64 128 256), losses := [] }

theorem u18937 : Upper (D 7) (R 7) [34,68,10,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18937 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18938 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 296 145 96 209 145 401), lower := (rows 35 70 14 296 145 96 64 128 256), losses := [] }

theorem u18938 : Upper (D 7) (R 7) [34,68,10,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18939 : Route 9 := (fun mask => (mask,id))

def c18939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18939 : Upper (D 7) (R 7) [34,68,10,288,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,10,288,129,128] 13 (by decide) (choices 1) [1,16] r18939 c18939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5201
  · exact u5202

def b18940 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 296 208 33 209 145 401), lower := (rows 35 70 14 296 208 33 64 128 256), losses := [] }

theorem u18940 : Upper (D 7) (R 7) [34,68,10,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18941 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 14 296 208 48 193 129 385), lower := (rows 35 70 14 296 208 48 64 128 256), losses := [] }

theorem u18941 : Upper (D 7) (R 7) [34,68,10,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18941 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18942 : Route 9 := (fun mask => (mask,id))

def c18942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18942 : Upper (D 7) (R 7) [34,68,10,288,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,10,288,192,128] 13 (by decide) (choices 1) [1,16] r18942 c18942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5203
  · exact u5204

def b18943 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 392 81 33 240 176 432), lower := (rows 35 70 14 392 81 33 64 128 256), losses := [] }

theorem u18943 : Upper (D 7) (R 7) [34,68,10,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18944 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 14 392 81 48 225 161 417), lower := (rows 35 70 14 392 81 48 64 128 256), losses := [] }

theorem u18944 : Upper (D 7) (R 7) [34,68,10,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18944 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18945 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 80, targets := 128 },{ cop := 4, region := 424, targets := 64 }], pairs := [(3,1),(3,6),(4,1),(4,7)], upper := (rows 35 70 14 392 81 160 113 177 305), lower := (rows 35 70 14 392 81 160 64 128 256), losses := [] }

theorem u18945 : Upper (D 7) (R 7) [34,68,10,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18946 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 392 112 33 209 145 401), lower := (rows 35 70 14 392 112 33 64 128 256), losses := [] }

theorem u18946 : Upper (D 7) (R 7) [34,68,10,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18947 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 14 392 112 48 193 129 385), lower := (rows 35 70 14 392 112 48 64 128 256), losses := [] }

theorem u18947 : Upper (D 7) (R 7) [34,68,10,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18947 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18948 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 80, targets := 128 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 392 112 160 81 145 273), lower := (rows 35 70 14 392 112 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 35 7 47 424 48 160 0 160 256) }] }

theorem u18948 : Upper (D 7) (R 7) [34,68,10,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18949 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 392 145 33 112 240 368), lower := (rows 35 70 14 392 145 33 64 128 256), losses := [] }

theorem u18949 : Upper (D 7) (R 7) [34,68,10,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18950 : Route 9 := (fun mask => (mask,id))

def c18950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18950 : Upper (D 7) (R 7) [34,68,10,384,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,10,384,129,16] 13 (by decide) (choices 1) [1,32] r18950 c18950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5205
  · exact u5206

def b18951 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 392 145 96 113 177 305), lower := (rows 35 70 14 392 145 96 64 128 256), losses := [] }

theorem u18951 : Upper (D 7) (R 7) [34,68,10,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18952 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 392 176 33 81 209 337), lower := (rows 35 70 14 392 176 33 64 128 256), losses := [] }

theorem u18952 : Upper (D 7) (R 7) [34,68,10,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18953 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 14 392 176 48 65 193 321), lower := (rows 35 70 14 392 176 48 64 128 256), losses := [] }

theorem u18953 : Upper (D 7) (R 7) [34,68,10,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18953 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18954 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 14 392 176 96 81 145 273), lower := (rows 35 70 14 392 176 96 64 128 256), losses := [] }

theorem u18954 : Upper (D 7) (R 7) [34,68,10,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18955 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 14 392 208 33 113 177 305), lower := (rows 35 70 14 392 208 33 64 128 256), losses := [] }

theorem u18955 : Upper (D 7) (R 7) [34,68,10,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18956 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 14 392 208 48 97 161 289), lower := (rows 35 70 14 392 208 48 64 128 256), losses := [] }

theorem u18956 : Upper (D 7) (R 7) [34,68,10,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18956 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18957 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 28 73 400 33 226 162 418), lower := (rows 35 70 28 73 400 33 64 128 256), losses := [] }

theorem u18957 : Upper (D 7) (R 7) [34,68,24,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18958 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 73 400 34 225 161 417), lower := (rows 35 70 28 73 400 34 64 128 256), losses := [] }

theorem u18958 : Upper (D 7) (R 7) [34,68,24,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18959 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 72, targets := 128 }], pairs := [(0,6),(2,6),(3,7),(4,6)], upper := (rows 35 70 28 73 400 160 99 163 291), lower := (rows 35 70 28 73 400 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 27 187 0 131 259), good := (rows 435 439 60 445 432 160 0 160 256) }] }

theorem u18959 : Upper (D 7) (R 7) [34,68,24,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18959
end Delivery.IrregularNine14.P07
