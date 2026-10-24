import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0099

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19920 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 28 274 96 77 141 269), lower := (rows 35 67 164 28 274 96 64 128 256), losses := [] }

theorem u19920 : Upper (D 6) (R 6) [34,65,160,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19921 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 28 280 33 70 198 326), lower := (rows 35 67 164 28 280 33 64 128 256), losses := [] }

theorem u19921 : Upper (D 6) (R 6) [34,65,160,20,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19922 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 28 280 34 69 197 325), lower := (rows 35 67 164 28 280 34 64 128 256), losses := [] }

theorem u19922 : Upper (D 6) (R 6) [34,65,160,20,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19923 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 28 280 36 67 195 323), lower := (rows 35 67 164 28 280 36 64 128 256), losses := [] }

theorem u19923 : Upper (D 6) (R 6) [34,65,160,20,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19924 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 28 280 96 71 135 263), lower := (rows 35 67 164 28 280 96 64 128 256), losses := [] }

theorem u19924 : Upper (D 6) (R 6) [34,65,160,20,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19925 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 28 336 33 78 142 270), lower := (rows 35 67 164 28 336 33 64 128 256), losses := [] }

theorem u19925 : Upper (D 6) (R 6) [34,65,160,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19926 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 28 336 34 77 141 269), lower := (rows 35 67 164 28 336 34 64 128 256), losses := [] }

theorem u19926 : Upper (D 6) (R 6) [34,65,160,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19927 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 28 336 36 75 139 267), lower := (rows 35 67 164 28 336 36 64 128 256), losses := [] }

theorem u19927 : Upper (D 6) (R 6) [34,65,160,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19928 : Route 9 := (fun mask => (mask,id))

def c19928 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19928 : Upper (D 6) (R 6) [34,65,160,20,320,8] 13 := by
  apply FastRouting.sound _ _ [34,65,160,20,320,8] 13 (by decide) (choices 1) [1,2,4] r19928 c19928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5961
  · exact u5962
  · exact u5963

def b19929 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 76 273 34 92 156 284), lower := (rows 35 67 164 76 273 34 64 128 256), losses := [] }

theorem u19929 : Upper (D 6) (R 6) [34,65,160,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19930 : PairBound 9 := { available := 26, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 76 273 36 90 154 282), lower := (rows 35 67 164 76 273 36 64 128 256), losses := [] }

theorem u19930 : Upper (D 6) (R 6) [34,65,160,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19931 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 164 76 273 40 86 150 278), lower := (rows 35 67 164 76 273 40 64 128 256), losses := [] }

theorem u19931 : Upper (D 6) (R 6) [34,65,160,68,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19931 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19932 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 164 76 273 48 78 142 270), lower := (rows 35 67 164 76 273 48 64 128 256), losses := [] }

theorem u19932 : Upper (D 6) (R 6) [34,65,160,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19932 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19933 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 76 274 33 92 156 284), lower := (rows 35 67 164 76 274 33 64 128 256), losses := [] }

theorem u19933 : Upper (D 6) (R 6) [34,65,160,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19934 : PairBound 9 := { available := 25, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 76 274 36 89 153 281), lower := (rows 35 67 164 76 274 36 64 128 256), losses := [] }

theorem u19934 : Upper (D 6) (R 6) [34,65,160,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19935 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 164 76 274 40 85 149 277), lower := (rows 35 67 164 76 274 40 64 128 256), losses := [] }

theorem u19935 : Upper (D 6) (R 6) [34,65,160,68,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19935 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19936 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 164 76 274 48 77 141 269), lower := (rows 35 67 164 76 274 48 64 128 256), losses := [] }

theorem u19936 : Upper (D 6) (R 6) [34,65,160,68,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19936 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19937 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 76 276 33 90 154 282), lower := (rows 35 67 164 76 276 33 64 128 256), losses := [] }

theorem u19937 : Upper (D 6) (R 6) [34,65,160,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19938 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 76 276 34 89 153 281), lower := (rows 35 67 164 76 276 34 64 128 256), losses := [] }

theorem u19938 : Upper (D 6) (R 6) [34,65,160,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19939 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 164 76 276 40 83 147 275), lower := (rows 35 67 164 76 276 40 64 128 256), losses := [] }

theorem u19939 : Upper (D 6) (R 6) [34,65,160,68,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19939 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19940 : Route 9 := (fun mask => (mask,id))

def c19940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19940 : Upper (D 6) (R 6) [34,65,160,68,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,160,68,260,16] 13 (by decide) (choices 1) [1,2,8] r19940 c19940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5964
  · exact u5965
  · exact u5966

def b19941 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 76 280 33 86 150 278), lower := (rows 35 67 164 76 280 33 64 128 256), losses := [] }

theorem u19941 : Upper (D 6) (R 6) [34,65,160,68,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19942 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 76 280 34 85 149 277), lower := (rows 35 67 164 76 280 34 64 128 256), losses := [] }

theorem u19942 : Upper (D 6) (R 6) [34,65,160,68,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19943 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 76 280 36 83 147 275), lower := (rows 35 67 164 76 280 36 64 128 256), losses := [] }

theorem u19943 : Upper (D 6) (R 6) [34,65,160,68,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19944 : Route 9 := (fun mask => (mask,id))

def c19944 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19944 : Upper (D 6) (R 6) [34,65,160,68,264,16] 13 := by
  apply FastRouting.sound _ _ [34,65,160,68,264,16] 13 (by decide) (choices 1) [1,2,4] r19944 c19944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5967
  · exact u5968
  · exact u5969

def b19945 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 88 273 34 76 140 268), lower := (rows 35 67 164 88 273 34 64 128 256), losses := [] }

theorem u19945 : Upper (D 6) (R 6) [34,65,160,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19946 : PairBound 9 := { available := 14, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 88 273 36 78 142 270), lower := (rows 35 67 164 88 273 36 64 128 256), losses := [] }

theorem u19946 : Upper (D 6) (R 6) [34,65,160,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19947 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 164 88 273 40 70 134 262), lower := (rows 35 67 164 88 273 40 64 128 256), losses := [] }

theorem u19947 : Upper (D 6) (R 6) [34,65,160,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19947 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19948 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 88 274 33 76 140 268), lower := (rows 35 67 164 88 274 33 64 128 256), losses := [] }

theorem u19948 : Upper (D 6) (R 6) [34,65,160,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19949 : PairBound 9 := { available := 13, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 88 274 36 77 141 269), lower := (rows 35 67 164 88 274 36 64 128 256), losses := [] }

theorem u19949 : Upper (D 6) (R 6) [34,65,160,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19950 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 164 88 274 40 69 133 261), lower := (rows 35 67 164 88 274 40 64 128 256), losses := [] }

theorem u19950 : Upper (D 6) (R 6) [34,65,160,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19950 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19951 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 88 276 33 78 142 270), lower := (rows 35 67 164 88 276 33 64 128 256), losses := [] }

theorem u19951 : Upper (D 6) (R 6) [34,65,160,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19952 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 88 276 34 77 141 269), lower := (rows 35 67 164 88 276 34 64 128 256), losses := [] }

theorem u19952 : Upper (D 6) (R 6) [34,65,160,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19953 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 88 276 36 75 139 267), lower := (rows 35 67 164 88 276 36 64 128 256), losses := [] }

theorem u19953 : Upper (D 6) (R 6) [34,65,160,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19954 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 164 88 276 40 71 135 263), lower := (rows 35 67 164 88 276 40 64 128 256), losses := [] }

theorem u19954 : Upper (D 6) (R 6) [34,65,160,80,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19954 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19955 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 88 280 33 70 134 262), lower := (rows 35 67 164 88 280 33 64 128 256), losses := [] }

theorem u19955 : Upper (D 6) (R 6) [34,65,160,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19956 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 88 280 34 69 133 261), lower := (rows 35 67 164 88 280 34 64 128 256), losses := [] }

theorem u19956 : Upper (D 6) (R 6) [34,65,160,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19957 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 88 280 36 71 135 263), lower := (rows 35 67 164 88 280 36 64 128 256), losses := [] }

theorem u19957 : Upper (D 6) (R 6) [34,65,160,80,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19958 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 388 13 22 40 112 240 368), lower := (rows 35 67 388 13 22 40 64 128 256), losses := [] }

theorem u19958 : Upper (D 6) (R 6) [34,65,384,5,6,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19958 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19959 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 388 13 22 48 104 232 360), lower := (rows 35 67 388 13 22 48 64 128 256), losses := [] }

theorem u19959 : Upper (D 6) (R 6) [34,65,384,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19959 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19960 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 388 13 22 96 120 184 312), lower := (rows 35 67 388 13 22 96 64 128 256), losses := [] }

theorem u19960 : Upper (D 6) (R 6) [34,65,384,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19961 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 484, targets := 3 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 67 388 13 26 36 112 240 368), lower := (rows 35 67 388 13 26 36 64 128 256), losses := [{ target := 6, region := (rows 17 2 4 8 16 44 0 128 256), good := (rows 35 3 420 45 59 36 0 128 256) }] }

theorem u19961 : Upper (D 6) (R 6) [34,65,384,5,10,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19962 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 388 13 26 48 100 228 356), lower := (rows 35 67 388 13 26 48 64 128 256), losses := [] }

theorem u19962 : Upper (D 6) (R 6) [34,65,384,5,10,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19962 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19963 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 388 13 26 96 116 180 308), lower := (rows 35 67 388 13 26 96 64 128 256), losses := [] }

theorem u19963 : Upper (D 6) (R 6) [34,65,384,5,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19964 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 13 52 34 88 216 344), lower := (rows 35 67 388 13 52 34 64 128 256), losses := [] }

theorem u19964 : Upper (D 6) (R 6) [34,65,384,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19965 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 388 13 52 40 82 210 338), lower := (rows 35 67 388 13 52 40 64 128 256), losses := [] }

theorem u19965 : Upper (D 6) (R 6) [34,65,384,5,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19965 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19966 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 388 13 52 48 74 202 330), lower := (rows 35 67 388 13 52 48 64 128 256), losses := [] }

theorem u19966 : Upper (D 6) (R 6) [34,65,384,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19966 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19967 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 388 13 52 96 90 154 282), lower := (rows 35 67 388 13 52 96 64 128 256), losses := [] }

theorem u19967 : Upper (D 6) (R 6) [34,65,384,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19968 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 13 56 34 84 212 340), lower := (rows 35 67 388 13 56 34 64 128 256), losses := [] }

theorem u19968 : Upper (D 6) (R 6) [34,65,384,5,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19969 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 388 13 56 36 82 210 338), lower := (rows 35 67 388 13 56 36 64 128 256), losses := [] }

theorem u19969 : Upper (D 6) (R 6) [34,65,384,5,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19970 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 388 13 56 48 70 198 326), lower := (rows 35 67 388 13 56 48 64 128 256), losses := [] }

theorem u19970 : Upper (D 6) (R 6) [34,65,384,5,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19970 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19971 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 388 13 56 96 86 150 278), lower := (rows 35 67 388 13 56 96 64 128 256), losses := [] }

theorem u19971 : Upper (D 6) (R 6) [34,65,384,5,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19972 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 13 84 34 120 184 312), lower := (rows 35 67 388 13 84 34 64 128 256), losses := [] }

theorem u19972 : Upper (D 6) (R 6) [34,65,384,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19973 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 388 13 84 40 114 178 306), lower := (rows 35 67 388 13 84 40 64 128 256), losses := [] }

theorem u19973 : Upper (D 6) (R 6) [34,65,384,5,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19973 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19974 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 388 13 84 48 106 170 298), lower := (rows 35 67 388 13 84 48 64 128 256), losses := [] }

theorem u19974 : Upper (D 6) (R 6) [34,65,384,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19974 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19975 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 13 88 34 116 180 308), lower := (rows 35 67 388 13 88 34 64 128 256), losses := [] }

theorem u19975 : Upper (D 6) (R 6) [34,65,384,5,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19976 : Route 9 := (fun mask => (mask,id))

def c19976 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19976 : Upper (D 6) (R 6) [34,65,384,5,72,4] 13 := by
  apply FastRouting.sound _ _ [34,65,384,5,72,4] 13 (by decide) (choices 1) [2,16,32] r19976 c19976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5970
  · exact u5971
  · exact u5972

def b19977 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 388 13 88 48 102 166 294), lower := (rows 35 67 388 13 88 48 64 128 256), losses := [] }

theorem u19977 : Upper (D 6) (R 6) [34,65,384,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19977 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19978 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 13 112 34 92 156 284), lower := (rows 35 67 388 13 112 34 64 128 256), losses := [] }

theorem u19978 : Upper (D 6) (R 6) [34,65,384,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19979 : Route 9 := (fun mask => (mask,id))

def c19979 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19979 : Upper (D 6) (R 6) [34,65,384,5,96,4] 13 := by
  apply FastRouting.sound _ _ [34,65,384,5,96,4] 13 (by decide) (choices 1) [2,8,16] r19979 c19979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5973
  · exact u5974
  · exact u5975

#print axioms u19979
end Delivery.IrregularNine14.P06
