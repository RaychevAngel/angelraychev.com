import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0102
import IrregularNine14P06C0103

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20880 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 84 138 273 33 100 164 292), lower := (rows 35 74 84 138 273 33 64 128 256), losses := [] }

theorem u20880 : Upper (D 6) (R 6) [34,72,80,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20881 : Route 9 := (fun mask => (mask,id))

def c20881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20881 : Upper (D 6) (R 6) [34,72,80,130,257,4] 13 := by
  apply FastRouting.sound _ _ [34,72,80,130,257,4] 13 (by decide) (choices 1) [1,4,32] r20881 c20881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6151
  · exact u6152
  · exact u6153

def b20882 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 84 138 276 33 101 165 293), lower := (rows 35 74 84 138 276 33 64 128 256), losses := [] }

theorem u20882 : Upper (D 6) (R 6) [34,72,80,130,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20883 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 84 138 276 36 97 161 289), lower := (rows 35 74 84 138 276 36 64 128 256), losses := [] }

theorem u20883 : Upper (D 6) (R 6) [34,72,80,130,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20884 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 84 138 304 33 69 133 261), lower := (rows 35 74 84 138 304 33 64 128 256), losses := [] }

theorem u20884 : Upper (D 6) (R 6) [34,72,80,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20885 : Route 9 := (fun mask => (mask,id))

def c20885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20885 : Upper (D 6) (R 6) [34,72,80,130,288,4] 13 := by
  apply FastRouting.sound _ _ [34,72,80,130,288,4] 13 (by decide) (choices 1) [1,4] r20885 c20885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6154
  · exact u6155

def r20886 : Route 9 := (fun mask => (mask,id))

def c20886 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20886 : Upper (D 6) (R 6) [34,72,80,132,257,1] 13 := by
  apply FastRouting.sound _ _ [34,72,80,132,257,1] 13 (by decide) (choices 1) [2,4,32] r20886 c20886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6156
  · exact u6157
  · exact u6158

def b20887 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 140 273 34 101 165 293), lower := (rows 35 74 84 140 273 34 64 128 256), losses := [] }

theorem u20887 : Upper (D 6) (R 6) [34,72,80,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20888 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 272, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(0,6),(4,2),(4,6)], upper := (rows 35 74 84 140 273 36 99 163 291), lower := (rows 35 74 84 140 273 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 19 44 0 131 259), good := (rows 435 443 52 172 401 36 0 128 256) }] }

theorem u20888 : Upper (D 6) (R 6) [34,72,80,132,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20889 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 74 84 140 274 33 101 165 293), lower := (rows 35 74 84 140 274 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 4 12 16 55 0 132 260), good := (rows 35 43 445 428 307 33 0 128 256) }] }

theorem u20889 : Upper (D 6) (R 6) [34,72,80,132,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20890 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 272, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(0,6),(4,2),(4,6)], upper := (rows 35 74 84 140 274 36 97 161 289), lower := (rows 35 74 84 140 274 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 19 44 0 131 259), good := (rows 435 443 52 172 403 36 0 128 256) }] }

theorem u20890 : Upper (D 6) (R 6) [34,72,80,132,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20891 : Route 9 := (fun mask => (mask,id))

def c20891 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20891 : Upper (D 6) (R 6) [34,72,80,132,288,1] 13 := by
  apply FastRouting.sound _ _ [34,72,80,132,288,1] 13 (by decide) (choices 1) [1,2,4] r20891 c20891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6159
  · exact u6160
  · exact u6161

def b20892 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 140 304 34 69 133 261), lower := (rows 35 74 84 140 304 34 64 128 256), losses := [] }

theorem u20892 : Upper (D 6) (R 6) [34,72,80,132,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20893 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 272, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(0,6),(4,2),(4,6)], upper := (rows 35 74 84 140 304 36 67 131 259), lower := (rows 35 74 84 140 304 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 19 44 0 131 259), good := (rows 435 443 52 172 304 36 0 128 256) }] }

theorem u20893 : Upper (D 6) (R 6) [34,72,80,132,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20894 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 84 168 21 33 326 390 262), lower := (rows 35 74 84 168 21 33 64 128 256), losses := [] }

theorem u20894 : Upper (D 6) (R 6) [34,72,80,160,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20895 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 168 21 34 325 389 261), lower := (rows 35 74 84 168 21 34 64 128 256), losses := [] }

theorem u20895 : Upper (D 6) (R 6) [34,72,80,160,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20896 : PairBound 9 := { available := 259, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 84 168 21 36 323 387 259), lower := (rows 35 74 84 168 21 36 64 128 256), losses := [] }

theorem u20896 : Upper (D 6) (R 6) [34,72,80,160,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20897 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 84 168 21 288 71 135 263), lower := (rows 35 74 84 168 21 288 64 128 256), losses := [] }

theorem u20897 : Upper (D 6) (R 6) [34,72,80,160,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20897 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20898 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 84 168 273 33 70 134 262), lower := (rows 35 74 84 168 273 33 64 128 256), losses := [] }

theorem u20898 : Upper (D 6) (R 6) [34,72,80,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20899 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 168 273 34 69 133 261), lower := (rows 35 74 84 168 273 34 64 128 256), losses := [] }

theorem u20899 : Upper (D 6) (R 6) [34,72,80,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20900 : Route 9 := (fun mask => (mask,id))

def c20900 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20900 : Upper (D 6) (R 6) [34,72,80,160,257,4] 13 := by
  apply FastRouting.sound _ _ [34,72,80,160,257,4] 13 (by decide) (choices 1) [1,2,4] r20900 c20900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6162
  · exact u6163
  · exact u6164

def b20901 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 84 168 274 33 69 133 261), lower := (rows 35 74 84 168 274 33 64 128 256), losses := [] }

theorem u20901 : Upper (D 6) (R 6) [34,72,80,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20902 : Route 9 := (fun mask => (mask,id))

def c20902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20902 : Upper (D 6) (R 6) [34,72,80,160,258,4] 13 := by
  apply FastRouting.sound _ _ [34,72,80,160,258,4] 13 (by decide) (choices 1) [1,4] r20902 c20902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6165
  · exact u6166

def b20903 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 84 168 276 33 71 135 263), lower := (rows 35 74 84 168 276 33 64 128 256), losses := [] }

theorem u20903 : Upper (D 6) (R 6) [34,72,80,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20904 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 168 276 34 69 133 261), lower := (rows 35 74 84 168 276 34 64 128 256), losses := [] }

theorem u20904 : Upper (D 6) (R 6) [34,72,80,160,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20905 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 84 168 276 36 67 131 259), lower := (rows 35 74 84 168 276 36 64 128 256), losses := [] }

theorem u20905 : Upper (D 6) (R 6) [34,72,80,160,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20906 : Route 9 := (fun mask => (mask,id))

def c20906 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20906 : Upper (D 6) (R 6) [34,72,80,384,5,1] 13 := by
  apply FastRouting.sound _ _ [34,72,80,384,5,1] 13 (by decide) (choices 1) [2,4,32] r20906 c20906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6167
  · exact u6168
  · exact u6169

def b20907 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 392 21 34 101 165 293), lower := (rows 35 74 84 392 21 34 64 128 256), losses := [] }

theorem u20907 : Upper (D 6) (R 6) [34,72,80,384,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20908 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 84 392 21 36 99 163 291), lower := (rows 35 74 84 392 21 36 64 128 256), losses := [] }

theorem u20908 : Upper (D 6) (R 6) [34,72,80,384,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20909 : Route 9 := (fun mask => (mask,id))

def c20909 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20909 : Upper (D 6) (R 6) [34,72,80,384,36,1] 13 := by
  apply FastRouting.sound _ _ [34,72,80,384,36,1] 13 (by decide) (choices 1) [1,2,4] r20909 c20909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6170
  · exact u6171
  · exact u6172

def b20910 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 392 52 34 69 133 261), lower := (rows 35 74 84 392 52 34 64 128 256), losses := [] }

theorem u20910 : Upper (D 6) (R 6) [34,72,80,384,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20911 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 84 392 52 36 67 131 259), lower := (rows 35 74 84 392 52 36 64 128 256), losses := [] }

theorem u20911 : Upper (D 6) (R 6) [34,72,80,384,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20912 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 13 145 34 340 404 276), lower := (rows 35 74 100 13 145 34 64 128 256), losses := [] }

theorem u20912 : Upper (D 6) (R 6) [34,72,96,5,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20913 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 100 13 145 36 338 402 274), lower := (rows 35 74 100 13 145 36 64 128 256), losses := [] }

theorem u20913 : Upper (D 6) (R 6) [34,72,96,5,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20914 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 74 100 13 145 48 326 390 262), lower := (rows 35 74 100 13 145 48 64 128 256), losses := [] }

theorem u20914 : Upper (D 6) (R 6) [34,72,96,5,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20914 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20915 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 74 100 13 145 288 86 150 278), lower := (rows 35 74 100 13 145 288 64 128 256), losses := [] }

theorem u20915 : Upper (D 6) (R 6) [34,72,96,5,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20915 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20916 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 100 13 146 33 340 404 276), lower := (rows 35 74 100 13 146 33 64 128 256), losses := [] }

theorem u20916 : Upper (D 6) (R 6) [34,72,96,5,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20917 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 100 13 146 36 337 401 273), lower := (rows 35 74 100 13 146 36 64 128 256), losses := [] }

theorem u20917 : Upper (D 6) (R 6) [34,72,96,5,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20918 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 100 13 146 48 325 389 261), lower := (rows 35 74 100 13 146 48 64 128 256), losses := [] }

theorem u20918 : Upper (D 6) (R 6) [34,72,96,5,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20918 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20919 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 74 100 13 146 288 85 149 277), lower := (rows 35 74 100 13 146 288 64 128 256), losses := [] }

theorem u20919 : Upper (D 6) (R 6) [34,72,96,5,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20919 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20920 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 100 13 148 33 338 402 274), lower := (rows 35 74 100 13 148 33 64 128 256), losses := [] }

theorem u20920 : Upper (D 6) (R 6) [34,72,96,5,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20921 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 13 148 34 337 401 273), lower := (rows 35 74 100 13 148 34 64 128 256), losses := [] }

theorem u20921 : Upper (D 6) (R 6) [34,72,96,5,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20922 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 74 100 13 148 48 323 387 259), lower := (rows 35 74 100 13 148 48 64 128 256), losses := [] }

theorem u20922 : Upper (D 6) (R 6) [34,72,96,5,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20922 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20923 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 74 100 13 148 288 83 147 275), lower := (rows 35 74 100 13 148 288 64 128 256), losses := [] }

theorem u20923 : Upper (D 6) (R 6) [34,72,96,5,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20923 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20924 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 100 13 400 33 86 150 278), lower := (rows 35 74 100 13 400 33 64 128 256), losses := [] }

theorem u20924 : Upper (D 6) (R 6) [34,72,96,5,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20925 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 13 400 34 85 149 277), lower := (rows 35 74 100 13 400 34 64 128 256), losses := [] }

theorem u20925 : Upper (D 6) (R 6) [34,72,96,5,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20926 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 100 13 400 36 83 147 275), lower := (rows 35 74 100 13 400 36 64 128 256), losses := [] }

theorem u20926 : Upper (D 6) (R 6) [34,72,96,5,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20927 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 74 100 13 400 48 71 135 263), lower := (rows 35 74 100 13 400 48 64 128 256), losses := [] }

theorem u20927 : Upper (D 6) (R 6) [34,72,96,5,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20927 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20928 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 74 100 25 146 33 324 388 260), lower := (rows 35 74 100 25 146 33 64 128 256), losses := [] }

theorem u20928 : Upper (D 6) (R 6) [34,72,96,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20929 : Route 9 := (fun mask => (mask,id))

def c20929 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u20929 : Upper (D 6) (R 6) [34,72,96,17,130,4] 13 := by
  apply FastRouting.sound _ _ [34,72,96,17,130,4] 13 (by decide) (choices 1) [1,4,256] r20929 c20929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6173
  · exact u6174
  · exact u6175

def r20930 : Route 9 := (fun mask => (mask,id))

def c20930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20930 : Upper (D 6) (R 6) [34,72,96,17,130,256] 13 := by
  apply FastRouting.sound _ _ [34,72,96,17,130,256] 13 (by decide) (choices 1) [1,4] r20930 c20930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6176
  · exact u6177

def b20931 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 100 25 148 33 326 390 262), lower := (rows 35 74 100 25 148 33 64 128 256), losses := [] }

theorem u20931 : Upper (D 6) (R 6) [34,72,96,17,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20932 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 25 148 34 325 389 261), lower := (rows 35 74 100 25 148 34 64 128 256), losses := [] }

theorem u20932 : Upper (D 6) (R 6) [34,72,96,17,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20933 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 322, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 74 100 25 148 36 323 387 259), lower := (rows 35 74 100 25 148 36 64 128 256), losses := [] }

theorem u20933 : Upper (D 6) (R 6) [34,72,96,17,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20934 : Route 9 := (fun mask => (mask,id))

def c20934 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20934 : Upper (D 6) (R 6) [34,72,96,17,132,256] 13 := by
  apply FastRouting.sound _ _ [34,72,96,17,132,256] 13 (by decide) (choices 1) [1,2,4] r20934 c20934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6178
  · exact u6179
  · exact u6180

def b20935 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 100 25 400 33 70 134 262), lower := (rows 35 74 100 25 400 33 64 128 256), losses := [] }

theorem u20935 : Upper (D 6) (R 6) [34,72,96,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20936 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 25 400 34 69 133 261), lower := (rows 35 74 100 25 400 34 64 128 256), losses := [] }

theorem u20936 : Upper (D 6) (R 6) [34,72,96,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20937 : Route 9 := (fun mask => (mask,id))

def c20937 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20937 : Upper (D 6) (R 6) [34,72,96,17,384,4] 13 := by
  apply FastRouting.sound _ _ [34,72,96,17,384,4] 13 (by decide) (choices 1) [1,2,4] r20937 c20937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6181
  · exact u6182
  · exact u6183

def b20938 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 100 26 145 33 324 388 260), lower := (rows 35 74 100 26 145 33 64 128 256), losses := [] }

theorem u20938 : Upper (D 6) (R 6) [34,72,96,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20939 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 74 100 26 145 36 325 389 261), lower := (rows 35 74 100 26 145 36 64 128 256), losses := [] }

theorem u20939 : Upper (D 6) (R 6) [34,72,96,18,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20939
end Delivery.IrregularNine14.P06
