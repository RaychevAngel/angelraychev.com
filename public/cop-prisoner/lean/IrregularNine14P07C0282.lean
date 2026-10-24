import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0066

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16920 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 392 19 160 82 210 338), lower := (rows 13 98 37 392 19 160 64 128 256), losses := [] }

theorem u16920 : Upper (D 7) (R 7) [12,96,33,384,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16921 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 38, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 37 392 81 34 210 146 402), lower := (rows 13 98 37 392 81 34 64 128 256), losses := [] }

theorem u16921 : Upper (D 7) (R 7) [12,96,33,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16922 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 392 81 48 194 130 386), lower := (rows 13 98 37 392 81 48 64 128 256), losses := [] }

theorem u16922 : Upper (D 7) (R 7) [12,96,33,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16922 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16923 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 392 81 160 82 146 274), lower := (rows 13 98 37 392 81 160 64 128 256), losses := [] }

theorem u16923 : Upper (D 7) (R 7) [12,96,33,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16924 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 98 37 392 146 33 82 210 338), lower := (rows 13 98 37 392 146 33 64 128 256), losses := [] }

theorem u16924 : Upper (D 7) (R 7) [12,96,33,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16925 : Route 9 := (fun mask => (mask,id))

def c16925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16925 : Upper (D 7) (R 7) [12,96,33,384,130,2] 13 := by
  apply FastRouting.sound _ _ [12,96,33,384,130,2] 13 (by decide) (choices 1) [1,16] r16925 c16925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3973
  · exact u3974

def r16926 : Route 9 := (fun mask => (mask,id))

def c16926 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16926 : Upper (D 7) (R 7) [12,96,33,384,130,16] 13 := by
  apply FastRouting.sound _ _ [12,96,33,384,130,16] 13 (by decide) (choices 1) [1,2] r16926 c16926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3975
  · exact u3976

def b16927 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 392 146 96 83 147 275), lower := (rows 13 98 37 392 146 96 64 128 256), losses := [] }

theorem u16927 : Upper (D 7) (R 7) [12,96,33,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16928 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 98 37 392 208 33 82 146 274), lower := (rows 13 98 37 392 208 33 64 128 256), losses := [] }

theorem u16928 : Upper (D 7) (R 7) [12,96,33,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16929 : Route 9 := (fun mask => (mask,id))

def c16929 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16929 : Upper (D 7) (R 7) [12,96,33,384,192,2] 13 := by
  apply FastRouting.sound _ _ [12,96,33,384,192,2] 13 (by decide) (choices 1) [1,2,16] r16929 c16929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3977
  · exact u3978
  · exact u3979

def b16930 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 392 208 48 67 131 259), lower := (rows 13 98 37 392 208 48 64 128 256), losses := [] }

theorem u16930 : Upper (D 7) (R 7) [12,96,33,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16930 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16931 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 38, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 137 81 34 450 386 386), lower := (rows 13 98 52 137 81 34 64 128 256), losses := [] }

theorem u16931 : Upper (D 7) (R 7) [12,96,48,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16932 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 2, region := 322, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(4,7)], upper := (rows 13 98 52 137 81 160 322 386 258), lower := (rows 13 98 52 137 81 160 64 128 256), losses := [{ target := 7, region := (rows 1 38 4 8 25 32 103 0 295), good := (rows 351 354 374 345 337 354 64 0 256) }] }

theorem u16932 : Upper (D 7) (R 7) [12,96,48,129,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16933 : Route 9 := (fun mask => (mask,id))

def c16933 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16933 : Upper (D 7) (R 7) [12,96,48,129,65,256] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,65,256] 13 (by decide) (choices 1) [2,128] r16933 c16933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3980
  · exact u3981

def b16934 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 52 137 146 33 322 450 322), lower := (rows 13 98 52 137 146 33 64 128 256), losses := [] }

theorem u16934 : Upper (D 7) (R 7) [12,96,48,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16935 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 52 137 146 34 321 449 321), lower := (rows 13 98 52 137 146 34 64 128 256), losses := [] }

theorem u16935 : Upper (D 7) (R 7) [12,96,48,129,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16936 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 137 146 96 323 387 259), lower := (rows 13 98 52 137 146 96 64 128 256), losses := [] }

theorem u16936 : Upper (D 7) (R 7) [12,96,48,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16937 : Route 9 := (fun mask => (mask,id))

def c16937 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16937 : Upper (D 7) (R 7) [12,96,48,129,130,256] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,130,256] 13 (by decide) (choices 1) [1,2] r16937 c16937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3982
  · exact u3983

def b16938 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 52 137 208 33 322 386 258), lower := (rows 13 98 52 137 208 33 64 128 256), losses := [] }

theorem u16938 : Upper (D 7) (R 7) [12,96,48,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16939 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 137 208 34 323 387 259), lower := (rows 13 98 52 137 208 34 64 128 256), losses := [] }

theorem u16939 : Upper (D 7) (R 7) [12,96,48,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16940 : Route 9 := (fun mask => (mask,id))

def c16940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16940 : Upper (D 7) (R 7) [12,96,48,129,192,256] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,192,256] 13 (by decide) (choices 1) [1,2] r16940 c16940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3984
  · exact u3985

def b16941 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,5),(1,0),(1,7),(2,0)], upper := (rows 13 98 52 137 273 34 194 194 450), lower := (rows 13 98 52 137 273 34 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 12 20 0 98 162 290), good := (rows 29 450 477 137 273 450 64 128 256) }] }

theorem u16941 : Upper (D 7) (R 7) [12,96,48,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16942 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 137 273 96 194 130 386), lower := (rows 13 98 52 137 273 96 64 128 256), losses := [] }

theorem u16942 : Upper (D 7) (R 7) [12,96,48,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16943 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(4,7)], upper := (rows 13 98 52 137 273 160 66 194 322), lower := (rows 13 98 52 137 273 160 64 128 256), losses := [{ target := 7, region := (rows 1 38 4 8 25 32 103 0 295), good := (rows 351 354 374 345 337 354 64 0 256) }] }

theorem u16943 : Upper (D 7) (R 7) [12,96,48,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16944 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 470, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(2,0),(4,0),(4,5)], upper := (rows 13 98 52 137 274 33 194 194 450), lower := (rows 13 98 52 137 274 33 64 128 256), losses := [] }

theorem u16944 : Upper (D 7) (R 7) [12,96,48,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16945 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 52 137 274 34 193 193 449), lower := (rows 13 98 52 137 274 34 64 128 256), losses := [] }

theorem u16945 : Upper (D 7) (R 7) [12,96,48,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16946 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 137 274 96 195 131 387), lower := (rows 13 98 52 137 274 96 64 128 256), losses := [] }

theorem u16946 : Upper (D 7) (R 7) [12,96,48,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16947 : Route 9 := (fun mask => (mask,id))

def c16947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16947 : Upper (D 7) (R 7) [12,96,48,129,258,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,258,128] 13 (by decide) (choices 1) [1,2] r16947 c16947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3986
  · exact u3987

def b16948 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 470, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(2,0),(4,0),(4,5)], upper := (rows 13 98 52 137 336 33 194 130 386), lower := (rows 13 98 52 137 336 33 64 128 256), losses := [] }

theorem u16948 : Upper (D 7) (R 7) [12,96,48,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16949 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 137 336 34 195 131 387), lower := (rows 13 98 52 137 336 34 64 128 256), losses := [] }

theorem u16949 : Upper (D 7) (R 7) [12,96,48,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16950 : Route 9 := (fun mask => (mask,id))

def c16950 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16950 : Upper (D 7) (R 7) [12,96,48,129,320,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,320,128] 13 (by decide) (choices 1) [1,2] r16950 c16950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3988
  · exact u3989

def b16951 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 52 137 400 33 66 194 322), lower := (rows 13 98 52 137 400 33 64 128 256), losses := [] }

theorem u16951 : Upper (D 7) (R 7) [12,96,48,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16952 : Route 9 := (fun mask => (mask,id))

def c16952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16952 : Upper (D 7) (R 7) [12,96,48,129,384,2] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,384,2] 13 (by decide) (choices 1) [1,2] r16952 c16952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3990
  · exact u3991

def b16953 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 137 400 96 67 131 259), lower := (rows 13 98 52 137 400 96 64 128 256), losses := [] }

theorem u16953 : Upper (D 7) (R 7) [12,96,48,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16954 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 52 138 19 33 448 448 448), lower := (rows 13 98 52 138 19 33 64 128 256), losses := [] }

theorem u16954 : Upper (D 7) (R 7) [12,96,48,130,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16955 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 138 19 96 449 385 385), lower := (rows 13 98 52 138 19 96 64 128 256), losses := [] }

theorem u16955 : Upper (D 7) (R 7) [12,96,48,130,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16956 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 4, region := 484, targets := 2 }], pairs := [(0,6),(2,1),(2,6),(4,6)], upper := (rows 13 98 52 138 19 160 321 449 321), lower := (rows 13 98 52 138 19 160 64 128 256), losses := [] }

theorem u16956 : Upper (D 7) (R 7) [12,96,48,130,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16957 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 484, targets := 2 },{ cop := 4, region := 200, targets := 32 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 13 98 52 138 19 288 193 193 449), lower := (rows 13 98 52 138 19 288 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 24 16 0 85 149 277), good := (rows 461 66 477 138 475 256 64 128 256) }] }

theorem u16957 : Upper (D 7) (R 7) [12,96,48,130,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16957 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16958 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 392, targets := 33 },{ cop := 4, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(3,0),(3,5)], upper := (rows 13 98 52 138 81 33 450 386 386), lower := (rows 13 98 52 138 81 33 64 128 256), losses := [] }

theorem u16958 : Upper (D 7) (R 7) [12,96,48,130,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16959 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 138 81 34 449 385 385), lower := (rows 13 98 52 138 81 34 64 128 256), losses := [] }

theorem u16959 : Upper (D 7) (R 7) [12,96,48,130,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16960 : Route 9 := (fun mask => (mask,id))

def c16960 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u16960 : Upper (D 7) (R 7) [12,96,48,130,65,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,65,128] 13 (by decide) (choices 1) [1,2,256] r16960 c16960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3992
  · exact u3993
  · exact u3994

def r16961 : Route 9 := (fun mask => (mask,id))

def c16961 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16961 : Upper (D 7) (R 7) [12,96,48,130,65,256] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,65,256] 13 (by decide) (choices 1) [1,2,128] r16961 c16961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3995
  · exact u3996
  · exact u3997

def b16962 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 52 138 145 33 322 450 322), lower := (rows 13 98 52 138 145 33 64 128 256), losses := [] }

theorem u16962 : Upper (D 7) (R 7) [12,96,48,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16963 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(2,6),(4,1),(4,6)], upper := (rows 13 98 52 138 145 34 321 449 321), lower := (rows 13 98 52 138 145 34 64 128 256), losses := [] }

theorem u16963 : Upper (D 7) (R 7) [12,96,48,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16964 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 138 145 96 323 387 259), lower := (rows 13 98 52 138 145 96 64 128 256), losses := [] }

theorem u16964 : Upper (D 7) (R 7) [12,96,48,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16965 : Route 9 := (fun mask => (mask,id))

def c16965 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16965 : Upper (D 7) (R 7) [12,96,48,130,129,256] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,129,256] 13 (by decide) (choices 1) [1,2] r16965 c16965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3998
  · exact u3999

def r16966 : Route 9 := (fun mask => (mask,id))

def c16966 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u16966 : Upper (D 7) (R 7) [12,96,48,130,192,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,192,1] 13 (by decide) (choices 1) [1,2,256] r16966 c16966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4000
  · exact u4001
  · exact u4002

def b16967 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 46, targets := 1 },{ cop := 0, region := 464, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 13 98 52 138 208 34 321 385 257), lower := (rows 13 98 52 138 208 34 64 128 256), losses := [] }

theorem u16967 : Upper (D 7) (R 7) [12,96,48,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16968 : Route 9 := (fun mask => (mask,id))

def c16968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16968 : Upper (D 7) (R 7) [12,96,48,130,192,256] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,192,256] 13 (by decide) (choices 1) [1,2] r16968 c16968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4003
  · exact u4004

def b16969 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 },{ cop := 1, region := 136, targets := 1 }], pairs := [(2,1),(2,6),(2,7),(3,0)], upper := (rows 13 98 52 138 273 33 194 194 450), lower := (rows 13 98 52 138 273 33 64 128 256), losses := [] }

theorem u16969 : Upper (D 7) (R 7) [12,96,48,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16970 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 98 52 138 273 34 193 193 449), lower := (rows 13 98 52 138 273 34 64 128 256), losses := [] }

theorem u16970 : Upper (D 7) (R 7) [12,96,48,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16971 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 138 273 96 195 131 387), lower := (rows 13 98 52 138 273 96 64 128 256), losses := [] }

theorem u16971 : Upper (D 7) (R 7) [12,96,48,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16972 : Route 9 := (fun mask => (mask,id))

def c16972 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16972 : Upper (D 7) (R 7) [12,96,48,130,257,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,257,128] 13 (by decide) (choices 1) [1,2] r16972 c16972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4005
  · exact u4006

def r16973 : Route 9 := (fun mask => (mask,id))

def c16973 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16973 : Upper (D 7) (R 7) [12,96,48,130,258,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,258,1] 13 (by decide) (choices 1) [1,128] r16973 c16973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4007
  · exact u4008

def b16974 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 52 138 274 96 193 129 385), lower := (rows 13 98 52 138 274 96 64 128 256), losses := [] }

theorem u16974 : Upper (D 7) (R 7) [12,96,48,130,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16975 : Route 9 := (fun mask => (mask,id))

def c16975 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16975 : Upper (D 7) (R 7) [12,96,48,130,258,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,258,128] 13 (by decide) (choices 1) [1] r16975 c16975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u4009

def r16976 : Route 9 := (fun mask => (mask,id))

def c16976 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16976 : Upper (D 7) (R 7) [12,96,48,130,320,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,320,1] 13 (by decide) (choices 1) [1,2,128] r16976 c16976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4010
  · exact u4011
  · exact u4012

def b16977 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 52 138 336 34 193 129 385), lower := (rows 13 98 52 138 336 34 64 128 256), losses := [] }

theorem u16977 : Upper (D 7) (R 7) [12,96,48,130,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16978 : Route 9 := (fun mask => (mask,id))

def c16978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16978 : Upper (D 7) (R 7) [12,96,48,130,320,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,320,128] 13 (by decide) (choices 1) [1,2] r16978 c16978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4013
  · exact u4014

def r16979 : Route 9 := (fun mask => (mask,id))

def c16979 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16979 : Upper (D 7) (R 7) [12,96,48,130,384,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,384,1] 13 (by decide) (choices 1) [1,2] r16979 c16979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4015
  · exact u4016

#print axioms u16979
end Delivery.IrregularNine14.P07
