import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0172

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27900 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 140 73 176 48 67 131 259), lower := (rows 37 322 140 73 176 48 64 128 256), losses := [] }

theorem u27900 : Upper (D 7) (R 7) [36,320,136,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27900 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27901 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 140 88 19 33 226 162 418), lower := (rows 37 322 140 88 19 33 64 128 256), losses := [] }

theorem u27901 : Upper (D 7) (R 7) [36,320,136,80,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27902 : PairBound 9 := { available := 161, camps := [], pairs := [(0,6),(2,1),(2,6),(3,1)], upper := (rows 37 322 140 88 19 34 225 161 417), lower := (rows 37 322 140 88 19 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 65 129 257), good := (rows 485 320 140 92 477 32 64 128 256) },{ target := 6, region := (rows 9 2 12 8 16 50 0 153 281), good := (rows 421 290 397 445 435 34 0 128 256) }] }

theorem u27902 : Upper (D 7) (R 7) [36,320,136,80,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27903 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 88 19 160 99 163 291), lower := (rows 37 322 140 88 19 160 64 128 256), losses := [] }

theorem u27903 : Upper (D 7) (R 7) [36,320,136,80,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27904 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 140 88 50 33 195 131 387), lower := (rows 37 322 140 88 50 33 64 128 256), losses := [] }

theorem u27904 : Upper (D 7) (R 7) [36,320,136,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27905 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 37 322 140 88 50 34 193 129 385), lower := (rows 37 322 140 88 50 34 64 128 256), losses := [] }

theorem u27905 : Upper (D 7) (R 7) [36,320,136,80,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27906 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 88 50 160 67 131 259), lower := (rows 37 322 140 88 50 160 64 128 256), losses := [] }

theorem u27906 : Upper (D 7) (R 7) [36,320,136,80,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27907 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 140 88 145 33 98 162 290), lower := (rows 37 322 140 88 145 33 64 128 256), losses := [] }

theorem u27907 : Upper (D 7) (R 7) [36,320,136,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27908 : Route 9 := (fun mask => (mask,id))

def c27908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27908 : Upper (D 7) (R 7) [36,320,136,80,129,2] 13 := by
  apply FastRouting.sound _ _ [36,320,136,80,129,2] 13 (by decide) (choices 1) [1,2,32] r27908 c27908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10323
  · exact u10324
  · exact u10325

def b27909 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 322 140 88 146 33 99 163 291), lower := (rows 37 322 140 88 146 33 64 128 256), losses := [] }

theorem u27909 : Upper (D 7) (R 7) [36,320,136,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27910 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 37 322 140 88 146 34 97 161 289), lower := (rows 37 322 140 88 146 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 137 265), good := (rows 421 290 397 445 178 34 0 128 256) }] }

theorem u27910 : Upper (D 7) (R 7) [36,320,136,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27911 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 140 88 176 33 67 131 259), lower := (rows 37 322 140 88 176 33 64 128 256), losses := [] }

theorem u27911 : Upper (D 7) (R 7) [36,320,136,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27912 : Route 9 := (fun mask => (mask,id))

def c27912 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27912 : Upper (D 7) (R 7) [36,320,136,80,160,2] 13 := by
  apply FastRouting.sound _ _ [36,320,136,80,160,2] 13 (by decide) (choices 1) [1,2] r27912 c27912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10326
  · exact u10327

def b27913 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 140 104 19 33 210 146 402), lower := (rows 37 322 140 104 19 33 64 128 256), losses := [] }

theorem u27913 : Upper (D 7) (R 7) [36,320,136,96,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27914 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 40, targets := 129 }], pairs := [(1,5),(3,0),(3,7),(4,5)], upper := (rows 37 322 140 104 19 34 209 145 401), lower := (rows 37 322 140 104 19 34 64 128 256), losses := [] }

theorem u27914 : Upper (D 7) (R 7) [36,320,136,96,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27915 : Route 9 := (fun mask => (mask,id))

def c27915 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27915 : Upper (D 7) (R 7) [36,320,136,96,3,16] 13 := by
  apply FastRouting.sound _ _ [36,320,136,96,3,16] 13 (by decide) (choices 1) [1,2,128] r27915 c27915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10328
  · exact u10329
  · exact u10330

def b27916 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 0, region := 338, targets := 32 }], pairs := [(1,5),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 104 19 160 83 147 275), lower := (rows 37 322 140 104 19 160 64 128 256), losses := [] }

theorem u27916 : Upper (D 7) (R 7) [36,320,136,96,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27917 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 140 104 146 33 83 147 275), lower := (rows 37 322 140 104 146 33 64 128 256), losses := [] }

theorem u27917 : Upper (D 7) (R 7) [36,320,136,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27918 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 40, targets := 129 }], pairs := [(1,5),(3,0),(3,7),(4,5)], upper := (rows 37 322 140 104 146 34 81 145 273), lower := (rows 37 322 140 104 146 34 64 128 256), losses := [] }

theorem u27918 : Upper (D 7) (R 7) [36,320,136,96,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27919 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 37 322 140 104 146 48 67 131 259), lower := (rows 37 322 140 104 146 48 64 128 256), losses := [] }

theorem u27919 : Upper (D 7) (R 7) [36,320,136,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27919 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27920 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 48, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 322 196 11 50 33 216 152 408), lower := (rows 37 322 196 11 50 33 64 128 256), losses := [] }

theorem u27920 : Upper (D 7) (R 7) [36,320,192,3,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27921 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 48, targets := 129 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,7)], upper := (rows 37 322 196 11 50 40 209 145 401), lower := (rows 37 322 196 11 50 40 64 128 256), losses := [] }

theorem u27921 : Upper (D 7) (R 7) [36,320,192,3,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27921 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27922 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 196 11 50 48 201 137 393), lower := (rows 37 322 196 11 50 48 64 128 256), losses := [] }

theorem u27922 : Upper (D 7) (R 7) [36,320,192,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27922 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27923 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 196 11 50 160 89 153 281), lower := (rows 37 322 196 11 50 160 64 128 256), losses := [] }

theorem u27923 : Upper (D 7) (R 7) [36,320,192,3,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27924 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 196 11 56 33 210 146 402), lower := (rows 37 322 196 11 56 33 64 128 256), losses := [] }

theorem u27924 : Upper (D 7) (R 7) [36,320,192,3,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27925 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 48, targets := 129 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,7)], upper := (rows 37 322 196 11 56 34 209 145 401), lower := (rows 37 322 196 11 56 34 64 128 256), losses := [] }

theorem u27925 : Upper (D 7) (R 7) [36,320,192,3,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27926 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 196 11 56 48 195 131 387), lower := (rows 37 322 196 11 56 48 64 128 256), losses := [] }

theorem u27926 : Upper (D 7) (R 7) [36,320,192,3,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27926 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27927 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 196 11 56 160 83 147 275), lower := (rows 37 322 196 11 56 160 64 128 256), losses := [] }

theorem u27927 : Upper (D 7) (R 7) [36,320,192,3,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27928 : Route 9 := (fun mask => (mask,id))

def c27928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27928 : Upper (D 7) (R 7) [36,320,192,3,129,2] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3,129,2] 13 (by decide) (choices 1) [8,16,32] r27928 c27928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10331
  · exact u10332
  · exact u10333

def b27929 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 3, region := 176, targets := 64 }], pairs := [(1,7),(3,7),(4,6)], upper := (rows 37 322 196 11 145 40 114 178 306), lower := (rows 37 322 196 11 145 40 64 128 256), losses := [] }

theorem u27929 : Upper (D 7) (R 7) [36,320,192,3,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27929 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27930 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 196 11 145 48 106 170 298), lower := (rows 37 322 196 11 145 48 64 128 256), losses := [] }

theorem u27930 : Upper (D 7) (R 7) [36,320,192,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27930 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27931 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 176, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 322 196 11 146 33 120 184 312), lower := (rows 37 322 196 11 146 33 64 128 256), losses := [] }

theorem u27931 : Upper (D 7) (R 7) [36,320,192,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27932 : Route 9 := (fun mask => (mask,id))

def c27932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27932 : Upper (D 7) (R 7) [36,320,192,3,130,8] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3,130,8] 13 (by decide) (choices 1) [1,16,32] r27932 c27932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10334
  · exact u10335
  · exact u10336

def b27933 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 176, targets := 64 }], pairs := [(1,7),(3,7),(4,6)], upper := (rows 37 322 196 11 146 48 105 169 297), lower := (rows 37 322 196 11 146 48 64 128 256), losses := [] }

theorem u27933 : Upper (D 7) (R 7) [36,320,192,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27933 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27934 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 176, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 322 196 11 152 33 114 178 306), lower := (rows 37 322 196 11 152 33 64 128 256), losses := [] }

theorem u27934 : Upper (D 7) (R 7) [36,320,192,3,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27935 : Route 9 := (fun mask => (mask,id))

def c27935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27935 : Upper (D 7) (R 7) [36,320,192,3,136,2] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3,136,2] 13 (by decide) (choices 1) [1,16,32] r27935 c27935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10337
  · exact u10338
  · exact u10339

def b27936 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 176, targets := 64 }], pairs := [(1,7),(3,7),(4,6)], upper := (rows 37 322 196 11 152 48 99 163 291), lower := (rows 37 322 196 11 152 48 64 128 256), losses := [] }

theorem u27936 : Upper (D 7) (R 7) [36,320,192,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27936 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27937 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 196 11 176 33 90 154 282), lower := (rows 37 322 196 11 176 33 64 128 256), losses := [] }

theorem u27937 : Upper (D 7) (R 7) [36,320,192,3,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27938 : Route 9 := (fun mask => (mask,id))

def c27938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27938 : Upper (D 7) (R 7) [36,320,192,3,160,2] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3,160,2] 13 (by decide) (choices 1) [1,8,16] r27938 c27938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10340
  · exact u10341
  · exact u10342

def r27939 : Route 9 := (fun mask => (mask,id))

def c27939 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27939 : Upper (D 7) (R 7) [36,320,192,3,160,8] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3,160,8] 13 (by decide) (choices 1) [1,2,16] r27939 c27939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10343
  · exact u10344
  · exact u10345

def b27940 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 196 11 176 48 75 139 267), lower := (rows 37 322 196 11 176 48 64 128 256), losses := [] }

theorem u27940 : Upper (D 7) (R 7) [36,320,192,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27940 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27941 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 196 25 26 33 226 162 418), lower := (rows 37 322 196 25 26 33 64 128 256), losses := [] }

theorem u27941 : Upper (D 7) (R 7) [36,320,192,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27942 : Route 9 := (fun mask => (mask,id))

def c27942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27942 : Upper (D 7) (R 7) [36,320,192,17,10,2] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,10,2] 13 (by decide) (choices 1) [1,32,128] r27942 c27942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10346
  · exact u10347
  · exact u10348

def b27943 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 196 25 26 160 99 163 291), lower := (rows 37 322 196 25 26 160 64 128 256), losses := [] }

theorem u27943 : Upper (D 7) (R 7) [36,320,192,17,10,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27944 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 196 25 50 33 202 138 394), lower := (rows 37 322 196 25 50 33 64 128 256), losses := [] }

theorem u27944 : Upper (D 7) (R 7) [36,320,192,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27945 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 205, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 322 196 25 50 34 201 137 393), lower := (rows 37 322 196 25 50 34 64 128 256), losses := [] }

theorem u27945 : Upper (D 7) (R 7) [36,320,192,17,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27946 : Route 9 := (fun mask => (mask,id))

def c27946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27946 : Upper (D 7) (R 7) [36,320,192,17,34,8] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,34,8] 13 (by decide) (choices 1) [1,2,128] r27946 c27946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10349
  · exact u10350
  · exact u10351

def b27947 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 196 25 50 160 75 139 267), lower := (rows 37 322 196 25 50 160 64 128 256), losses := [] }

theorem u27947 : Upper (D 7) (R 7) [36,320,192,17,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27948 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 354, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 322 196 25 146 33 106 170 298), lower := (rows 37 322 196 25 146 33 64 128 256), losses := [] }

theorem u27948 : Upper (D 7) (R 7) [36,320,192,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27949 : Route 9 := (fun mask => (mask,id))

def c27949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27949 : Upper (D 7) (R 7) [36,320,192,17,130,2] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,130,2] 13 (by decide) (choices 1) [1,8,32] r27949 c27949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10352
  · exact u10353
  · exact u10354

def r27950 : Route 9 := (fun mask => (mask,id))

def c27950 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27950 : Upper (D 7) (R 7) [36,320,192,17,130,8] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,130,8] 13 (by decide) (choices 1) [1,2,32] r27950 c27950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10355
  · exact u10356
  · exact u10357

def b27951 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 322 196 25 152 33 98 162 290), lower := (rows 37 322 196 25 152 33 64 128 256), losses := [] }

theorem u27951 : Upper (D 7) (R 7) [36,320,192,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27952 : Route 9 := (fun mask => (mask,id))

def c27952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27952 : Upper (D 7) (R 7) [36,320,192,17,136,2] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,136,2] 13 (by decide) (choices 1) [1,2,32] r27952 c27952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10358
  · exact u10359
  · exact u10360

def b27953 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 322 196 25 176 33 74 138 266), lower := (rows 37 322 196 25 176 33 64 128 256), losses := [] }

theorem u27953 : Upper (D 7) (R 7) [36,320,192,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27954 : Route 9 := (fun mask => (mask,id))

def c27954 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27954 : Upper (D 7) (R 7) [36,320,192,17,160,2] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,160,2] 13 (by decide) (choices 1) [1,2,8] r27954 c27954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10361
  · exact u10362
  · exact u10363

def b27955 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 322 196 25 176 40 67 131 259), lower := (rows 37 322 196 25 176 40 64 128 256), losses := [] }

theorem u27955 : Upper (D 7) (R 7) [36,320,192,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27955 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27956 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 196 26 56 33 195 131 387), lower := (rows 37 322 196 26 56 33 64 128 256), losses := [] }

theorem u27956 : Upper (D 7) (R 7) [36,320,192,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27957 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 56, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 37 322 196 26 56 34 193 129 385), lower := (rows 37 322 196 26 56 34 64 128 256), losses := [] }

theorem u27957 : Upper (D 7) (R 7) [36,320,192,18,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27958 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 0, region := 322, targets := 32 }], pairs := [(1,5),(1,7),(3,7),(4,7)], upper := (rows 37 322 196 26 56 160 67 131 259), lower := (rows 37 322 196 26 56 160 64 128 256), losses := [] }

theorem u27958 : Upper (D 7) (R 7) [36,320,192,18,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27959 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 196 26 145 33 106 170 298), lower := (rows 37 322 196 26 145 33 64 128 256), losses := [] }

theorem u27959 : Upper (D 7) (R 7) [36,320,192,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27959
end Delivery.IrregularNine14.P07
