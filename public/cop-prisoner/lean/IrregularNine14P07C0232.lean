import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0036

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13920 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(4,7)], upper := (rows 7 98 44 138 273 160 81 209 337), lower := (rows 7 98 44 138 273 160 64 128 256), losses := [] }

theorem u13920 : Upper (D 7) (R 7) [6,96,40,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13921 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 138 336 33 209 145 401), lower := (rows 7 98 44 138 336 33 64 128 256), losses := [] }

theorem u13921 : Upper (D 7) (R 7) [6,96,40,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13922 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 138 336 48 193 129 385), lower := (rows 7 98 44 138 336 48 64 128 256), losses := [] }

theorem u13922 : Upper (D 7) (R 7) [6,96,40,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13922 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13923 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(4,7)], upper := (rows 7 98 44 138 336 160 81 145 273), lower := (rows 7 98 44 138 336 160 64 128 256), losses := [] }

theorem u13923 : Upper (D 7) (R 7) [6,96,40,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13924 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 138 400 33 81 209 337), lower := (rows 7 98 44 138 400 33 64 128 256), losses := [] }

theorem u13924 : Upper (D 7) (R 7) [6,96,40,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13925 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 44 138 400 48 65 193 321), lower := (rows 7 98 44 138 400 48 64 128 256), losses := [] }

theorem u13925 : Upper (D 7) (R 7) [6,96,40,130,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13925 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13926 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 138 400 96 81 145 273), lower := (rows 7 98 44 138 400 96 64 128 256), losses := [] }

theorem u13926 : Upper (D 7) (R 7) [6,96,40,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13927 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(3,0),(3,5),(4,5)], upper := (rows 7 98 44 152 273 33 194 194 450), lower := (rows 7 98 44 152 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 38 4 24 16 32 103 167 295), good := (rows 454 482 494 152 472 482 64 128 256) }] }

theorem u13927 : Upper (D 7) (R 7) [6,96,40,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13928 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 152 273 34 193 193 449), lower := (rows 7 98 44 152 273 34 64 128 256), losses := [] }

theorem u13928 : Upper (D 7) (R 7) [6,96,40,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13929 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 152 273 96 195 131 387), lower := (rows 7 98 44 152 273 96 64 128 256), losses := [] }

theorem u13929 : Upper (D 7) (R 7) [6,96,40,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13930 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 98 44 152 273 160 67 195 323), lower := (rows 7 98 44 152 273 160 64 128 256), losses := [] }

theorem u13930 : Upper (D 7) (R 7) [6,96,40,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13931 : Route 9 := (fun mask => (mask,id))

def c13931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13931 : Upper (D 7) (R 7) [6,96,40,144,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,40,144,258,1] 13 (by decide) (choices 1) [1,128] r13931 c13931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2172
  · exact u2173

def b13932 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 152 274 96 193 129 385), lower := (rows 7 98 44 152 274 96 64 128 256), losses := [] }

theorem u13932 : Upper (D 7) (R 7) [6,96,40,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13933 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 98 44 152 274 160 65 193 321), lower := (rows 7 98 44 152 274 160 64 128 256), losses := [] }

theorem u13933 : Upper (D 7) (R 7) [6,96,40,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13934 : Route 9 := (fun mask => (mask,id))

def c13934 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13934 : Upper (D 7) (R 7) [6,96,40,144,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,40,144,320,1] 13 (by decide) (choices 1) [1,2,128] r13934 c13934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2174
  · exact u2175
  · exact u2176

def b13935 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 152 336 34 193 129 385), lower := (rows 7 98 44 152 336 34 64 128 256), losses := [] }

theorem u13935 : Upper (D 7) (R 7) [6,96,40,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13936 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 98 44 152 336 160 67 131 259), lower := (rows 7 98 44 152 336 160 64 128 256), losses := [] }

theorem u13936 : Upper (D 7) (R 7) [6,96,40,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13937 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 200 146 33 337 401 273), lower := (rows 7 98 44 200 146 33 64 128 256), losses := [] }

theorem u13937 : Upper (D 7) (R 7) [6,96,40,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13938 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 54, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 98 44 200 146 48 321 385 257), lower := (rows 7 98 44 200 146 48 64 128 256), losses := [] }

theorem u13938 : Upper (D 7) (R 7) [6,96,40,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13938 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13939 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 7 98 44 200 146 288 81 145 273), lower := (rows 7 98 44 200 146 288 64 128 256), losses := [] }

theorem u13939 : Upper (D 7) (R 7) [6,96,40,192,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13939 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13940 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 200 273 33 210 146 402), lower := (rows 7 98 44 200 273 33 64 128 256), losses := [] }

theorem u13940 : Upper (D 7) (R 7) [6,96,40,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13941 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 200 273 34 209 145 401), lower := (rows 7 98 44 200 273 34 64 128 256), losses := [] }

theorem u13941 : Upper (D 7) (R 7) [6,96,40,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13942 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 7 98 44 200 273 48 195 131 387), lower := (rows 7 98 44 200 273 48 64 128 256), losses := [] }

theorem u13942 : Upper (D 7) (R 7) [6,96,40,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13942 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13943 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(4,7)], upper := (rows 7 98 44 200 273 160 83 147 275), lower := (rows 7 98 44 200 273 160 64 128 256), losses := [] }

theorem u13943 : Upper (D 7) (R 7) [6,96,40,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13944 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 200 274 33 209 145 401), lower := (rows 7 98 44 200 274 33 64 128 256), losses := [] }

theorem u13944 : Upper (D 7) (R 7) [6,96,40,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13945 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 98 44 200 274 48 193 129 385), lower := (rows 7 98 44 200 274 48 64 128 256), losses := [] }

theorem u13945 : Upper (D 7) (R 7) [6,96,40,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13945 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13946 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(4,7)], upper := (rows 7 98 44 200 274 160 81 145 273), lower := (rows 7 98 44 200 274 160 64 128 256), losses := [] }

theorem u13946 : Upper (D 7) (R 7) [6,96,40,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13947 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 200 400 33 83 147 275), lower := (rows 7 98 44 200 400 33 64 128 256), losses := [] }

theorem u13947 : Upper (D 7) (R 7) [6,96,40,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13948 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 200 400 34 81 145 273), lower := (rows 7 98 44 200 400 34 64 128 256), losses := [] }

theorem u13948 : Upper (D 7) (R 7) [6,96,40,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13949 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 44 200 400 48 67 131 259), lower := (rows 7 98 44 200 400 48 64 128 256), losses := [] }

theorem u13949 : Upper (D 7) (R 7) [6,96,40,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13949 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13950 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 265 81 34 208 144 400), lower := (rows 7 98 44 265 81 34 64 128 256), losses := [] }

theorem u13950 : Upper (D 7) (R 7) [6,96,40,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13951 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 265 81 48 194 130 386), lower := (rows 7 98 44 265 81 48 64 128 256), losses := [] }

theorem u13951 : Upper (D 7) (R 7) [6,96,40,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13951 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13952 : Route 9 := (fun mask => (mask,id))

def c13952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13952 : Upper (D 7) (R 7) [6,96,40,257,65,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,257,65,128] 13 (by decide) (choices 1) [2,16,128] r13952 c13952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2177
  · exact u2178
  · exact u2179

def b13953 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 265 145 34 208 208 464), lower := (rows 7 98 44 265 145 34 64 128 256), losses := [] }

theorem u13953 : Upper (D 7) (R 7) [6,96,40,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13954 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 98 44 265 145 48 194 194 450), lower := (rows 7 98 44 265 145 48 64 128 256), losses := [] }

theorem u13954 : Upper (D 7) (R 7) [6,96,40,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13954 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13955 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 265 145 96 210 146 402), lower := (rows 7 98 44 265 145 96 64 128 256), losses := [] }

theorem u13955 : Upper (D 7) (R 7) [6,96,40,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13956 : Route 9 := (fun mask => (mask,id))

def c13956 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13956 : Upper (D 7) (R 7) [6,96,40,257,129,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,257,129,128] 13 (by decide) (choices 1) [2,16] r13956 c13956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2180
  · exact u2181

def b13957 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 36, targets := 194 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 98 44 265 146 33 208 208 464), lower := (rows 7 98 44 265 146 33 64 128 256), losses := [] }

theorem u13957 : Upper (D 7) (R 7) [6,96,40,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13958 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 98 44 265 146 48 193 193 449), lower := (rows 7 98 44 265 146 48 64 128 256), losses := [] }

theorem u13958 : Upper (D 7) (R 7) [6,96,40,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13958 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13959 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 265 146 96 209 145 401), lower := (rows 7 98 44 265 146 96 64 128 256), losses := [] }

theorem u13959 : Upper (D 7) (R 7) [6,96,40,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13960 : Route 9 := (fun mask => (mask,id))

def c13960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13960 : Upper (D 7) (R 7) [6,96,40,257,130,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,257,130,128] 13 (by decide) (choices 1) [1,16] r13960 c13960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2182
  · exact u2183

def b13961 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 36, targets := 194 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 98 44 265 208 33 210 146 402), lower := (rows 7 98 44 265 208 33 64 128 256), losses := [] }

theorem u13961 : Upper (D 7) (R 7) [6,96,40,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13962 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 265 208 34 209 145 401), lower := (rows 7 98 44 265 208 34 64 128 256), losses := [] }

theorem u13962 : Upper (D 7) (R 7) [6,96,40,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13963 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 265 208 48 195 131 387), lower := (rows 7 98 44 265 208 48 64 128 256), losses := [] }

theorem u13963 : Upper (D 7) (R 7) [6,96,40,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13963 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13964 : Route 9 := (fun mask => (mask,id))

def c13964 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13964 : Upper (D 7) (R 7) [6,96,40,257,192,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,257,192,128] 13 (by decide) (choices 1) [1,2,16] r13964 c13964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2184
  · exact u2185
  · exact u2186

def b13965 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 266 81 33 208 144 400), lower := (rows 7 98 44 266 81 33 64 128 256), losses := [] }

theorem u13965 : Upper (D 7) (R 7) [6,96,40,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13966 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 266 81 48 193 129 385), lower := (rows 7 98 44 266 81 48 64 128 256), losses := [] }

theorem u13966 : Upper (D 7) (R 7) [6,96,40,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13966 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13967 : Route 9 := (fun mask => (mask,id))

def c13967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13967 : Upper (D 7) (R 7) [6,96,40,258,65,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,258,65,128] 13 (by decide) (choices 1) [1,16,128] r13967 c13967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2187
  · exact u2188
  · exact u2189

def b13968 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 266 145 33 208 208 464), lower := (rows 7 98 44 266 145 33 64 128 256), losses := [] }

theorem u13968 : Upper (D 7) (R 7) [6,96,40,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13969 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 98 44 266 145 48 193 193 449), lower := (rows 7 98 44 266 145 48 64 128 256), losses := [] }

theorem u13969 : Upper (D 7) (R 7) [6,96,40,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13969 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13970 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 266 145 96 209 145 401), lower := (rows 7 98 44 266 145 96 64 128 256), losses := [] }

theorem u13970 : Upper (D 7) (R 7) [6,96,40,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13971 : Route 9 := (fun mask => (mask,id))

def c13971 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13971 : Upper (D 7) (R 7) [6,96,40,258,129,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,258,129,128] 13 (by decide) (choices 1) [1,16] r13971 c13971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2190
  · exact u2191

def b13972 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 266 208 33 209 145 401), lower := (rows 7 98 44 266 208 33 64 128 256), losses := [] }

theorem u13972 : Upper (D 7) (R 7) [6,96,40,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13973 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 266 208 48 193 129 385), lower := (rows 7 98 44 266 208 48 64 128 256), losses := [] }

theorem u13973 : Upper (D 7) (R 7) [6,96,40,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13973 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13974 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 208, targets := 2 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 266 208 160 81 145 273), lower := (rows 7 98 44 266 208 160 64 128 256), losses := [] }

theorem u13974 : Upper (D 7) (R 7) [6,96,40,258,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13975 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(3,0),(3,5),(4,5)], upper := (rows 7 98 44 280 145 33 194 194 450), lower := (rows 7 98 44 280 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 38 4 24 16 32 103 167 295), good := (rows 454 482 494 280 472 482 64 128 256) }] }

theorem u13975 : Upper (D 7) (R 7) [6,96,40,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13976 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 280 145 34 193 193 449), lower := (rows 7 98 44 280 145 34 64 128 256), losses := [] }

theorem u13976 : Upper (D 7) (R 7) [6,96,40,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13977 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 280 145 96 195 131 387), lower := (rows 7 98 44 280 145 96 64 128 256), losses := [] }

theorem u13977 : Upper (D 7) (R 7) [6,96,40,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13978 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 280 145 160 67 195 323), lower := (rows 7 98 44 280 145 160 64 128 256), losses := [] }

theorem u13978 : Upper (D 7) (R 7) [6,96,40,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13979 : Route 9 := (fun mask => (mask,id))

def c13979 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13979 : Upper (D 7) (R 7) [6,96,40,272,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,40,272,130,1] 13 (by decide) (choices 1) [1,128] r13979 c13979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2192
  · exact u2193

#print axioms u13979
end Delivery.IrregularNine14.P07
