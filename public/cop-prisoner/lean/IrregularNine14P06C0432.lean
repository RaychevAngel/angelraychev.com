import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0134
import IrregularNine14P06C0135

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25920 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 268 84 48 67 131 259), lower := (rows 41 98 133 268 84 48 64 128 256), losses := [] }

theorem u25920 : Upper (D 6) (R 6) [40,96,129,260,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25920 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25921 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 280 22 33 70 198 326), lower := (rows 41 98 133 280 22 33 64 128 256), losses := [] }

theorem u25921 : Upper (D 6) (R 6) [40,96,129,272,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25922 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 41 98 133 280 22 34 69 197 325), lower := (rows 41 98 133 280 22 34 64 128 256), losses := [] }

theorem u25922 : Upper (D 6) (R 6) [40,96,129,272,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25923 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(0,1),(1,2),(3,2)], upper := (rows 41 98 133 280 22 36 67 195 323), lower := (rows 41 98 133 280 22 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 96 165 313 52 36 64 128 256) },{ target := 2, region := (rows 1 35 0 24 16 32 69 133 261), good := (rows 491 98 451 280 474 482 64 128 256) }] }

theorem u25923 : Upper (D 6) (R 6) [40,96,129,272,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25924 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 280 22 96 71 135 263), lower := (rows 41 98 133 280 22 96 64 128 256), losses := [] }

theorem u25924 : Upper (D 6) (R 6) [40,96,129,272,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25925 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 133 280 81 34 70 134 262), lower := (rows 41 98 133 280 81 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 122 64 128 256), good := (rows 41 98 129 315 115 34 98 128 256) }] }

theorem u25925 : Upper (D 6) (R 6) [40,96,129,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25926 : Route 9 := (fun mask => (mask,id))

def c25926 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25926 : Upper (D 6) (R 6) [40,96,129,272,65,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,272,65,4] 13 (by decide) (choices 1) [2,4] r25926 c25926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8082
  · exact u8083

def b25927 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 280 84 33 70 134 262), lower := (rows 41 98 133 280 84 33 64 128 256), losses := [] }

theorem u25927 : Upper (D 6) (R 6) [40,96,129,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25928 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 133 280 84 34 71 135 263), lower := (rows 41 98 133 280 84 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 122 64 128 256), good := (rows 41 98 129 315 114 34 98 128 256) }] }

theorem u25928 : Upper (D 6) (R 6) [40,96,129,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25929 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 66, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,2)], upper := (rows 41 98 133 280 84 36 67 131 259), lower := (rows 41 98 133 280 84 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 96 165 313 116 36 64 128 256) }] }

theorem u25929 : Upper (D 6) (R 6) [40,96,129,272,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25930 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 328 22 33 86 150 278), lower := (rows 41 98 133 328 22 33 64 128 256), losses := [] }

theorem u25930 : Upper (D 6) (R 6) [40,96,129,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25931 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 133 328 22 34 85 149 277), lower := (rows 41 98 133 328 22 34 64 128 256), losses := [] }

theorem u25931 : Upper (D 6) (R 6) [40,96,129,320,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25932 : Route 9 := (fun mask => (mask,id))

def c25932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25932 : Upper (D 6) (R 6) [40,96,129,320,6,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,320,6,4] 13 (by decide) (choices 1) [1,2,16] r25932 c25932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8084
  · exact u8085
  · exact u8086

def r25933 : Route 9 := (fun mask => (mask,id))

def c25933 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25933 : Upper (D 6) (R 6) [40,96,129,320,6,16] 13 := by
  apply FastRouting.sound _ _ [40,96,129,320,6,16] 13 (by decide) (choices 1) [1,2,4] r25933 c25933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8087
  · exact u8088
  · exact u8089

def b25934 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 336, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 41 98 134 13 81 34 340 404 276), lower := (rows 41 98 134 13 81 34 64 128 256), losses := [] }

theorem u25934 : Upper (D 6) (R 6) [40,96,130,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25935 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 134 13 81 36 338 402 274), lower := (rows 41 98 134 13 81 36 64 128 256), losses := [] }

theorem u25935 : Upper (D 6) (R 6) [40,96,130,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25936 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 13 81 48 326 390 262), lower := (rows 41 98 134 13 81 48 64 128 256), losses := [] }

theorem u25936 : Upper (D 6) (R 6) [40,96,130,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25936 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25937 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 134 13 81 288 86 150 278), lower := (rows 41 98 134 13 81 288 64 128 256), losses := [] }

theorem u25937 : Upper (D 6) (R 6) [40,96,130,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25937 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25938 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 134 13 84 33 338 402 274), lower := (rows 41 98 134 13 84 33 64 128 256), losses := [] }

theorem u25938 : Upper (D 6) (R 6) [40,96,130,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25939 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 336, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 41 98 134 13 84 34 337 401 273), lower := (rows 41 98 134 13 84 34 64 128 256), losses := [] }

theorem u25939 : Upper (D 6) (R 6) [40,96,130,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25940 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 134 13 84 48 323 387 259), lower := (rows 41 98 134 13 84 48 64 128 256), losses := [] }

theorem u25940 : Upper (D 6) (R 6) [40,96,130,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25940 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25941 : Route 9 := (fun mask => (mask,id))

def c25941 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25941 : Upper (D 6) (R 6) [40,96,130,5,68,256] 13 := by
  apply FastRouting.sound _ _ [40,96,130,5,68,256] 13 (by decide) (choices 1) [1,2,16] r25941 c25941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8090
  · exact u8091
  · exact u8092

def b25942 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 336, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 41 98 134 13 273 34 84 212 340), lower := (rows 41 98 134 13 273 34 64 128 256), losses := [] }

theorem u25942 : Upper (D 6) (R 6) [40,96,130,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25943 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 134 13 273 36 82 210 338), lower := (rows 41 98 134 13 273 36 64 128 256), losses := [] }

theorem u25943 : Upper (D 6) (R 6) [40,96,130,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25944 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 134 13 273 48 70 198 326), lower := (rows 41 98 134 13 273 48 64 128 256), losses := [] }

theorem u25944 : Upper (D 6) (R 6) [40,96,130,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25944 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25945 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 13 273 96 86 150 278), lower := (rows 41 98 134 13 273 96 64 128 256), losses := [] }

theorem u25945 : Upper (D 6) (R 6) [40,96,130,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25946 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 134 13 274 33 84 212 340), lower := (rows 41 98 134 13 274 33 64 128 256), losses := [] }

theorem u25946 : Upper (D 6) (R 6) [40,96,130,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25947 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 134 13 274 36 81 209 337), lower := (rows 41 98 134 13 274 36 64 128 256), losses := [] }

theorem u25947 : Upper (D 6) (R 6) [40,96,130,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25948 : Route 9 := (fun mask => (mask,id))

def c25948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25948 : Upper (D 6) (R 6) [40,96,130,5,258,16] 13 := by
  apply FastRouting.sound _ _ [40,96,130,5,258,16] 13 (by decide) (choices 1) [1,4] r25948 c25948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8093
  · exact u8094

def b25949 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 13 274 96 85 149 277), lower := (rows 41 98 134 13 274 96 64 128 256), losses := [] }

theorem u25949 : Upper (D 6) (R 6) [40,96,130,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25950 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 134 13 276 33 82 210 338), lower := (rows 41 98 134 13 276 33 64 128 256), losses := [] }

theorem u25950 : Upper (D 6) (R 6) [40,96,130,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25951 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 336, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 41 98 134 13 276 34 81 209 337), lower := (rows 41 98 134 13 276 34 64 128 256), losses := [] }

theorem u25951 : Upper (D 6) (R 6) [40,96,130,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25952 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 134 13 276 48 67 195 323), lower := (rows 41 98 134 13 276 48 64 128 256), losses := [] }

theorem u25952 : Upper (D 6) (R 6) [40,96,130,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25952 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25953 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 13 276 96 83 147 275), lower := (rows 41 98 134 13 276 96 64 128 256), losses := [] }

theorem u25953 : Upper (D 6) (R 6) [40,96,130,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25954 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 134 13 336 33 86 150 278), lower := (rows 41 98 134 13 336 33 64 128 256), losses := [] }

theorem u25954 : Upper (D 6) (R 6) [40,96,130,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25955 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 336, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 41 98 134 13 336 34 85 149 277), lower := (rows 41 98 134 13 336 34 64 128 256), losses := [] }

theorem u25955 : Upper (D 6) (R 6) [40,96,130,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25956 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 134 13 336 36 83 147 275), lower := (rows 41 98 134 13 336 36 64 128 256), losses := [] }

theorem u25956 : Upper (D 6) (R 6) [40,96,130,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25957 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 13 336 48 71 135 263), lower := (rows 41 98 134 13 336 48 64 128 256), losses := [] }

theorem u25957 : Upper (D 6) (R 6) [40,96,130,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25957 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25958 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 134 25 84 33 326 390 262), lower := (rows 41 98 134 25 84 33 64 128 256), losses := [] }

theorem u25958 : Upper (D 6) (R 6) [40,96,130,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25959 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 134 25 84 34 325 389 261), lower := (rows 41 98 134 25 84 34 64 128 256), losses := [] }

theorem u25959 : Upper (D 6) (R 6) [40,96,130,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25960 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 134 25 84 36 323 387 259), lower := (rows 41 98 134 25 84 36 64 128 256), losses := [] }

theorem u25960 : Upper (D 6) (R 6) [40,96,130,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25961 : Route 9 := (fun mask => (mask,id))

def c25961 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25961 : Upper (D 6) (R 6) [40,96,130,17,68,256] 13 := by
  apply FastRouting.sound _ _ [40,96,130,17,68,256] 13 (by decide) (choices 1) [1,2,4] r25961 c25961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8095
  · exact u8096
  · exact u8097

def b25962 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 25 274 33 68 196 324), lower := (rows 41 98 134 25 274 33 64 128 256), losses := [] }

theorem u25962 : Upper (D 6) (R 6) [40,96,130,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25963 : Route 9 := (fun mask => (mask,id))

def c25963 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25963 : Upper (D 6) (R 6) [40,96,130,17,258,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,17,258,4] 13 (by decide) (choices 1) [1,4] r25963 c25963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8098
  · exact u8099

def b25964 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 25 274 96 69 133 261), lower := (rows 41 98 134 25 274 96 64 128 256), losses := [] }

theorem u25964 : Upper (D 6) (R 6) [40,96,130,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25965 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 25 276 33 70 198 326), lower := (rows 41 98 134 25 276 33 64 128 256), losses := [] }

theorem u25965 : Upper (D 6) (R 6) [40,96,130,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25966 : PairBound 9 := { available := 69, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 134 25 276 34 69 197 325), lower := (rows 41 98 134 25 276 34 64 128 256), losses := [{ target := 2, region := (rows 17 66 0 24 16 102 64 128 256), good := (rows 41 98 162 25 313 34 98 128 256) }] }

theorem u25966 : Upper (D 6) (R 6) [40,96,130,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25967 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 134 25 276 36 67 195 323), lower := (rows 41 98 134 25 276 36 64 128 256), losses := [] }

theorem u25967 : Upper (D 6) (R 6) [40,96,130,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25968 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 25 276 96 71 135 263), lower := (rows 41 98 134 25 276 96 64 128 256), losses := [] }

theorem u25968 : Upper (D 6) (R 6) [40,96,130,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25969 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 134 25 336 33 70 134 262), lower := (rows 41 98 134 25 336 33 64 128 256), losses := [] }

theorem u25969 : Upper (D 6) (R 6) [40,96,130,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25970 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 134 25 336 34 69 133 261), lower := (rows 41 98 134 25 336 34 64 128 256), losses := [] }

theorem u25970 : Upper (D 6) (R 6) [40,96,130,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25971 : Route 9 := (fun mask => (mask,id))

def c25971 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25971 : Upper (D 6) (R 6) [40,96,130,17,320,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,17,320,4] 13 (by decide) (choices 1) [1,2,4] r25971 c25971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8100
  · exact u8101
  · exact u8102

def b25972 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 134 26 84 33 325 389 261), lower := (rows 41 98 134 26 84 33 64 128 256), losses := [] }

theorem u25972 : Upper (D 6) (R 6) [40,96,130,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25973 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 41 98 134 26 84 36 321 385 257), lower := (rows 41 98 134 26 84 36 64 128 256), losses := [] }

theorem u25973 : Upper (D 6) (R 6) [40,96,130,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25974 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 26 84 288 69 133 261), lower := (rows 41 98 134 26 84 288 64 128 256), losses := [] }

theorem u25974 : Upper (D 6) (R 6) [40,96,130,18,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25974 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25975 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 26 273 33 68 196 324), lower := (rows 41 98 134 26 273 33 64 128 256), losses := [] }

theorem u25975 : Upper (D 6) (R 6) [40,96,130,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25976 : Route 9 := (fun mask => (mask,id))

def c25976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25976 : Upper (D 6) (R 6) [40,96,130,18,257,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,18,257,4] 13 (by decide) (choices 1) [1,4] r25976 c25976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8103
  · exact u8104

def b25977 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 26 273 96 69 133 261), lower := (rows 41 98 134 26 273 96 64 128 256), losses := [] }

theorem u25977 : Upper (D 6) (R 6) [40,96,130,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25978 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 26 276 33 69 197 325), lower := (rows 41 98 134 26 276 33 64 128 256), losses := [] }

theorem u25978 : Upper (D 6) (R 6) [40,96,130,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25979 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(0,1),(0,6),(1,2)], upper := (rows 41 98 134 26 276 36 65 193 321), lower := (rows 41 98 134 26 276 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 73 137 265), good := (rows 489 96 164 505 308 36 64 128 256) },{ target := 6, region := (rows 9 2 4 8 16 52 0 128 256), good := (rows 41 34 166 59 308 36 0 128 256) }] }

theorem u25979 : Upper (D 6) (R 6) [40,96,130,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25979
end Delivery.IrregularNine14.P06
