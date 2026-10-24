import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0140
import IrregularNine14P07C0141

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24900 : PairBound 9 := { available := 25, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 104 400 34 89 153 281), lower := (rows 37 194 7 104 400 34 64 128 256), losses := [] }

theorem u24900 : Upper (D 7) (R 7) [36,192,3,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24901 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 7 104 400 40 83 147 275), lower := (rows 37 194 7 104 400 40 64 128 256), losses := [] }

theorem u24901 : Upper (D 7) (R 7) [36,192,3,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24901 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24902 : Route 9 := (fun mask => (mask,id))

def c24902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24902 : Upper (D 7) (R 7) [36,192,3,96,384,16] 13 := by
  apply FastRouting.sound _ _ [36,192,3,96,384,16] 13 (by decide) (choices 1) [1,2,8] r24902 c24902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8433
  · exact u8434
  · exact u8435

def b24903 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 13 26 112 33 450 386 386), lower := (rows 37 194 13 26 112 33 64 128 256), losses := [] }

theorem u24903 : Upper (D 7) (R 7) [36,192,9,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24904 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 13 26 112 34 449 385 385), lower := (rows 37 194 13 26 112 34 64 128 256), losses := [] }

theorem u24904 : Upper (D 7) (R 7) [36,192,9,18,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24905 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 56, targets := 1 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 37 194 13 26 112 160 323 387 259), lower := (rows 37 194 13 26 112 160 64 128 256), losses := [] }

theorem u24905 : Upper (D 7) (R 7) [36,192,9,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24906 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,6),(1,5),(2,6)], upper := (rows 37 194 13 26 112 288 195 131 387), lower := (rows 37 194 13 26 112 288 64 128 256), losses := [] }

theorem u24906 : Upper (D 7) (R 7) [36,192,9,18,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24906 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24907 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 13 26 273 34 224 224 480), lower := (rows 37 194 13 26 273 34 64 128 256), losses := [] }

theorem u24907 : Upper (D 7) (R 7) [36,192,9,18,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24908 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 194 13 26 273 96 226 162 418), lower := (rows 37 194 13 26 273 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 98 64 128 256), good := (rows 37 224 13 61 273 96 96 128 256) }] }

theorem u24908 : Upper (D 7) (R 7) [36,192,9,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24909 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 26 304 33 194 194 450), lower := (rows 37 194 13 26 304 33 64 128 256), losses := [] }

theorem u24909 : Upper (D 7) (R 7) [36,192,9,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24910 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 13 26 304 34 193 193 449), lower := (rows 37 194 13 26 304 34 64 128 256), losses := [] }

theorem u24910 : Upper (D 7) (R 7) [36,192,9,18,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24911 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,7),(1,5),(2,1)], upper := (rows 37 194 13 26 304 96 195 131 387), lower := (rows 37 194 13 26 304 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 98 64 128 256), good := (rows 37 224 13 61 304 96 96 128 256) },{ target := 7, region := (rows 9 2 12 8 16 98 64 0 256), good := (rows 37 98 13 63 304 96 96 0 256) }] }

theorem u24911 : Upper (D 7) (R 7) [36,192,9,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24912 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 13 26 336 33 226 162 418), lower := (rows 37 194 13 26 336 33 64 128 256), losses := [] }

theorem u24912 : Upper (D 7) (R 7) [36,192,9,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24913 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 13 26 336 34 225 161 417), lower := (rows 37 194 13 26 336 34 64 128 256), losses := [] }

theorem u24913 : Upper (D 7) (R 7) [36,192,9,18,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24914 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 165, targets := 64 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 194 13 26 336 160 99 163 291), lower := (rows 37 194 13 26 336 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 162 64 128 256), good := (rows 37 224 13 61 336 160 64 160 256) }] }

theorem u24914 : Upper (D 7) (R 7) [36,192,9,18,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24915 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 88 50 33 450 386 386), lower := (rows 37 194 13 88 50 33 64 128 256), losses := [] }

theorem u24915 : Upper (D 7) (R 7) [36,192,9,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24916 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 13 88 50 34 449 385 385), lower := (rows 37 194 13 88 50 34 64 128 256), losses := [] }

theorem u24916 : Upper (D 7) (R 7) [36,192,9,80,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24917 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 56, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 37 194 13 88 50 160 323 387 259), lower := (rows 37 194 13 88 50 160 64 128 256), losses := [] }

theorem u24917 : Upper (D 7) (R 7) [36,192,9,80,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24918 : Route 9 := (fun mask => (mask,id))

def c24918 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24918 : Upper (D 7) (R 7) [36,192,9,80,34,256] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,34,256] 13 (by decide) (choices 1) [1,2,128] r24918 c24918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8436
  · exact u8437
  · exact u8438

def r24919 : Route 9 := (fun mask => (mask,id))

def c24919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u24919 : Upper (D 7) (R 7) [36,192,9,80,129,2] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,129,2] 13 (by decide) (choices 1) [2,32,256] r24919 c24919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8439
  · exact u8440
  · exact u8441

def r24920 : Route 9 := (fun mask => (mask,id))

def c24920 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24920 : Upper (D 7) (R 7) [36,192,9,80,129,256] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,129,256] 13 (by decide) (choices 1) [2,32] r24920 c24920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8442
  · exact u8443

def b24921 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 88 176 33 322 386 258), lower := (rows 37 194 13 88 176 33 64 128 256), losses := [] }

theorem u24921 : Upper (D 7) (R 7) [36,192,9,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24922 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 56, targets := 1 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 48, targets := 64 }], pairs := [(1,5),(3,0),(4,0),(4,6)], upper := (rows 37 194 13 88 176 34 323 387 259), lower := (rows 37 194 13 88 176 34 64 128 256), losses := [] }

theorem u24922 : Upper (D 7) (R 7) [36,192,9,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24923 : Route 9 := (fun mask => (mask,id))

def c24923 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24923 : Upper (D 7) (R 7) [36,192,9,80,160,256] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,160,256] 13 (by decide) (choices 1) [1,2] r24923 c24923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8444
  · exact u8445

def r24924 : Route 9 := (fun mask => (mask,id))

def c24924 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u24924 : Upper (D 7) (R 7) [36,192,9,80,257,2] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,257,2] 13 (by decide) (choices 1) [2,32,128] r24924 c24924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8446
  · exact u8447
  · exact u8448

def r24925 : Route 9 := (fun mask => (mask,id))

def c24925 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24925 : Upper (D 7) (R 7) [36,192,9,80,257,128] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,257,128] 13 (by decide) (choices 1) [2,32] r24925 c24925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8449
  · exact u8450

def b24926 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 88 274 33 226 162 418), lower := (rows 37 194 13 88 274 33 64 128 256), losses := [] }

theorem u24926 : Upper (D 7) (R 7) [36,192,9,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24927 : PairBound 9 := { available := 161, camps := [], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 13 88 274 34 225 161 417), lower := (rows 37 194 13 88 274 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 137 265), good := (rows 421 162 397 445 306 34 0 128 256) },{ target := 7, region := (rows 9 2 12 8 16 50 64 0 256), good := (rows 37 98 13 125 306 34 64 0 256) }] }

theorem u24927 : Upper (D 7) (R 7) [36,192,9,80,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24928 : Route 9 := (fun mask => (mask,id))

def c24928 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24928 : Upper (D 7) (R 7) [36,192,9,80,258,128] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,258,128] 13 (by decide) (choices 1) [1,2,32] r24928 c24928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8451
  · exact u8452
  · exact u8453

def b24929 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 88 304 33 194 130 386), lower := (rows 37 194 13 88 304 33 64 128 256), losses := [] }

theorem u24929 : Upper (D 7) (R 7) [36,192,9,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24930 : Route 9 := (fun mask => (mask,id))

def c24930 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24930 : Upper (D 7) (R 7) [36,192,9,80,288,2] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,288,2] 13 (by decide) (choices 1) [1,2,128] r24930 c24930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8454
  · exact u8455
  · exact u8456

def r24931 : Route 9 := (fun mask => (mask,id))

def c24931 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24931 : Upper (D 7) (R 7) [36,192,9,80,288,128] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,288,128] 13 (by decide) (choices 1) [1,2] r24931 c24931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8457
  · exact u8458

def b24932 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 88 400 33 98 162 290), lower := (rows 37 194 13 88 400 33 64 128 256), losses := [] }

theorem u24932 : Upper (D 7) (R 7) [36,192,9,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24933 : Route 9 := (fun mask => (mask,id))

def c24933 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24933 : Upper (D 7) (R 7) [36,192,9,80,384,2] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,384,2] 13 (by decide) (choices 1) [1,2,32] r24933 c24933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8459
  · exact u8460
  · exact u8461

def b24934 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 194 13 266 19 48 224 224 480), lower := (rows 37 194 13 266 19 48 64 128 256), losses := [] }

theorem u24934 : Upper (D 7) (R 7) [36,192,9,258,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24934 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24935 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 490, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 194 13 266 19 96 240 176 432), lower := (rows 37 194 13 266 19 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 114 80 144 272), good := (rows 37 224 13 301 497 96 96 128 256) }] }

theorem u24935 : Upper (D 7) (R 7) [36,192,9,258,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24936 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 13 266 50 33 208 208 464), lower := (rows 37 194 13 266 50 33 64 128 256), losses := [] }

theorem u24936 : Upper (D 7) (R 7) [36,192,9,258,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24937 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 194 13 266 50 48 193 193 449), lower := (rows 37 194 13 266 50 48 64 128 256), losses := [] }

theorem u24937 : Upper (D 7) (R 7) [36,192,9,258,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24937 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24938 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 194 13 266 50 96 209 145 401), lower := (rows 37 194 13 266 50 96 64 128 256), losses := [] }

theorem u24938 : Upper (D 7) (R 7) [36,192,9,258,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24939 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 13 266 81 34 240 176 432), lower := (rows 37 194 13 266 81 34 64 128 256), losses := [] }

theorem u24939 : Upper (D 7) (R 7) [36,192,9,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24940 : Route 9 := (fun mask => (mask,id))

def c24940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u24940 : Upper (D 7) (R 7) [36,192,9,258,65,16] 13 := by
  apply FastRouting.sound _ _ [36,192,9,258,65,16] 13 (by decide) (choices 1) [2,32,128] r24940 c24940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8462
  · exact u8463
  · exact u8464

def b24941 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 426, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 194 13 266 81 160 114 178 306), lower := (rows 37 194 13 266 81 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 162 64 128 256), good := (rows 37 224 13 301 81 160 64 160 256) }] }

theorem u24941 : Upper (D 7) (R 7) [36,192,9,258,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24942 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 266 112 33 210 146 402), lower := (rows 37 194 13 266 112 33 64 128 256), losses := [] }

theorem u24942 : Upper (D 7) (R 7) [36,192,9,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24943 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 13 266 112 34 209 145 401), lower := (rows 37 194 13 266 112 34 64 128 256), losses := [] }

theorem u24943 : Upper (D 7) (R 7) [36,192,9,258,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24944 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 13 266 112 48 195 131 387), lower := (rows 37 194 13 266 112 48 64 128 256), losses := [] }

theorem u24944 : Upper (D 7) (R 7) [36,192,9,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24944 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24945 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 48, targets := 1 },{ cop := 1, region := 48, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,1)], upper := (rows 37 194 13 266 112 160 83 147 275), lower := (rows 37 194 13 266 112 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 18 162 64 128 256), good := (rows 37 240 13 317 112 160 64 160 256) }] }

theorem u24945 : Upper (D 7) (R 7) [36,192,9,258,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24946 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(3,1)], upper := (rows 37 194 13 280 19 34 224 224 480), lower := (rows 37 194 13 280 19 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 97 161 289), good := (rows 485 192 461 284 477 480 64 128 256) }] }

theorem u24946 : Upper (D 7) (R 7) [36,192,9,272,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24947 : Route 9 := (fun mask => (mask,id))

def c24947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u24947 : Upper (D 7) (R 7) [36,192,9,272,3,64] 13 := by
  apply FastRouting.sound _ _ [36,192,9,272,3,64] 13 (by decide) (choices 1) [2,32,128] r24947 c24947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8465
  · exact u8466
  · exact u8467

def b24948 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 280 50 33 194 194 450), lower := (rows 37 194 13 280 50 33 64 128 256), losses := [] }

theorem u24948 : Upper (D 7) (R 7) [36,192,9,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24949 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 461, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 194 13 280 50 34 193 193 449), lower := (rows 37 194 13 280 50 34 64 128 256), losses := [] }

theorem u24949 : Upper (D 7) (R 7) [36,192,9,272,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24950 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 194 13 280 50 96 195 131 387), lower := (rows 37 194 13 280 50 96 64 128 256), losses := [] }

theorem u24950 : Upper (D 7) (R 7) [36,192,9,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24951 : Route 9 := (fun mask => (mask,id))

def c24951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u24951 : Upper (D 7) (R 7) [36,192,9,272,65,2] 13 := by
  apply FastRouting.sound _ _ [36,192,9,272,65,2] 13 (by decide) (choices 1) [2,32,128] r24951 c24951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8468
  · exact u8469
  · exact u8470

def r24952 : Route 9 := (fun mask => (mask,id))

def c24952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24952 : Upper (D 7) (R 7) [36,192,9,272,65,128] 13 := by
  apply FastRouting.sound _ _ [36,192,9,272,65,128] 13 (by decide) (choices 1) [2,32] r24952 c24952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8471
  · exact u8472

def b24953 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 280 112 33 194 130 386), lower := (rows 37 194 13 280 112 33 64 128 256), losses := [] }

theorem u24953 : Upper (D 7) (R 7) [36,192,9,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24954 : Route 9 := (fun mask => (mask,id))

def c24954 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24954 : Upper (D 7) (R 7) [36,192,9,272,96,2] 13 := by
  apply FastRouting.sound _ _ [36,192,9,272,96,2] 13 (by decide) (choices 1) [1,2,128] r24954 c24954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8473
  · exact u8474
  · exact u8475

def r24955 : Route 9 := (fun mask => (mask,id))

def c24955 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24955 : Upper (D 7) (R 7) [36,192,9,272,96,128] 13 := by
  apply FastRouting.sound _ _ [36,192,9,272,96,128] 13 (by decide) (choices 1) [1,2] r24955 c24955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8476
  · exact u8477

def r24956 : Route 9 := (fun mask => (mask,id))

def c24956 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u24956 : Upper (D 7) (R 7) [36,192,9,320,3,2] 13 := by
  apply FastRouting.sound _ _ [36,192,9,320,3,2] 13 (by decide) (choices 1) [16,32,128] r24956 c24956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8478
  · exact u8479
  · exact u8480

def r24957 : Route 9 := (fun mask => (mask,id))

def c24957 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u24957 : Upper (D 7) (R 7) [36,192,9,320,3,16] 13 := by
  apply FastRouting.sound _ _ [36,192,9,320,3,16] 13 (by decide) (choices 1) [2,32,128] r24957 c24957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8481
  · exact u8482
  · exact u8483

def r24958 : Route 9 := (fun mask => (mask,id))

def c24958 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24958 : Upper (D 7) (R 7) [36,192,9,320,3,128] 13 := by
  apply FastRouting.sound _ _ [36,192,9,320,3,128] 13 (by decide) (choices 1) [2,16,32] r24958 c24958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8484
  · exact u8485
  · exact u8486

def b24959 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 328 50 33 210 146 402), lower := (rows 37 194 13 328 50 33 64 128 256), losses := [] }

theorem u24959 : Upper (D 7) (R 7) [36,192,9,320,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u24959
end Delivery.IrregularNine14.P07
