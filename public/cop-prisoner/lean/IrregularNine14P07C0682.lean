import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0498
import IrregularNine14P07C0499

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40920 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 386 13 168 81 54 86 150 278), lower := (rows 97 386 13 168 81 32 64 128 256), losses := [] }

theorem u40920 : Upper (D 7) (R 7) [96,384,9,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40921 : Route 9 := (fun mask => (mask,id))

def c40921 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40921 : Upper (D 7) (R 7) [96,384,9,160,66] 13 := by
  apply FastRouting.sound _ _ [96,384,9,160,66] 13 (by decide) (choices 1) [1,2,4,16] r40921 c40921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29930
  · exact u29931
  · exact u29932
  · exact u29933

def r40922 : Route 9 := (fun mask => (mask,id))

def c40922 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40922 : Upper (D 7) (R 7) [96,384,9,160,68] 13 := by
  apply FastRouting.sound _ _ [96,384,9,160,68] 13 (by decide) (choices 1) [1,2,16] r40922 c40922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29934
  · exact u29935
  · exact u29936

def b40923 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 386 14 14 145 113 113 241 369), lower := (rows 97 386 14 14 145 32 64 128 256), losses := [] }

theorem u40923 : Upper (D 7) (R 7) [96,384,10,6,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40924 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 386 14 14 176 113 81 209 337), lower := (rows 97 386 14 14 176 32 64 128 256), losses := [] }

theorem u40924 : Upper (D 7) (R 7) [96,384,10,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40925 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 386 14 26 52 225 193 193 449), lower := (rows 97 386 14 26 52 32 64 128 256), losses := [] }

theorem u40925 : Upper (D 7) (R 7) [96,384,10,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40926 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 4, targets := 97 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,6)], upper := (rows 97 386 14 26 145 101 101 229 357), lower := (rows 97 386 14 26 145 32 64 128 256), losses := [] }

theorem u40926 : Upper (D 7) (R 7) [96,384,10,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40927 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 28, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 97 386 14 26 148 97 97 225 353), lower := (rows 97 386 14 26 148 32 64 128 256), losses := [] }

theorem u40927 : Upper (D 7) (R 7) [96,384,10,18,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40928 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 4, targets := 97 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,6)], upper := (rows 97 386 14 26 176 101 69 197 325), lower := (rows 97 386 14 26 176 32 64 128 256), losses := [] }

theorem u40928 : Upper (D 7) (R 7) [96,384,10,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40929 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 386 14 28 49 227 195 195 451), lower := (rows 97 386 14 28 49 32 64 128 256), losses := [] }

theorem u40929 : Upper (D 7) (R 7) [96,384,10,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40930 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 386 14 28 50 225 193 193 449), lower := (rows 97 386 14 28 50 32 64 128 256), losses := [] }

theorem u40930 : Upper (D 7) (R 7) [96,384,10,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40931 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 386 14 28 112 163 195 131 387), lower := (rows 97 386 14 28 112 32 64 128 256), losses := [] }

theorem u40931 : Upper (D 7) (R 7) [96,384,10,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40932 : Route 9 := (fun mask => (mask,id))

def c40932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40932 : Upper (D 7) (R 7) [96,384,10,20,129] 13 := by
  apply FastRouting.sound _ _ [96,384,10,20,129] 13 (by decide) (choices 1) [1,2,64] r40932 c40932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29937
  · exact u29938
  · exact u29939

def b40933 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 28, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 97 386 14 28 146 97 97 225 353), lower := (rows 97 386 14 28 146 32 64 128 256), losses := [] }

theorem u40933 : Upper (D 7) (R 7) [96,384,10,20,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40934 : Route 9 := (fun mask => (mask,id))

def c40934 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40934 : Upper (D 7) (R 7) [96,384,10,20,160] 13 := by
  apply FastRouting.sound _ _ [96,384,10,20,160] 13 (by decide) (choices 1) [1,2,64] r40934 c40934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29940
  · exact u29941
  · exact u29942

def b40935 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 14 41 82 181 213 149 405), lower := (rows 97 386 14 41 82 32 64 128 256), losses := [] }

theorem u40935 : Upper (D 7) (R 7) [96,384,10,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40936 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 14 41 84 179 211 147 403), lower := (rows 97 386 14 41 84 32 64 128 256), losses := [] }

theorem u40936 : Upper (D 7) (R 7) [96,384,10,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40937 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 14 41 145 118 86 214 342), lower := (rows 97 386 14 41 145 32 64 128 256), losses := [] }

theorem u40937 : Upper (D 7) (R 7) [96,384,10,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40938 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 14 41 148 115 83 211 339), lower := (rows 97 386 14 41 148 32 64 128 256), losses := [] }

theorem u40938 : Upper (D 7) (R 7) [96,384,10,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40939 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 14 41 208 55 87 151 279), lower := (rows 97 386 14 41 208 32 64 128 256), losses := [] }

theorem u40939 : Upper (D 7) (R 7) [96,384,10,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40940 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 386 14 42 84 177 209 145 401), lower := (rows 97 386 14 42 84 32 64 128 256), losses := [] }

theorem u40940 : Upper (D 7) (R 7) [96,384,10,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40941 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 386 14 42 145 117 85 213 341), lower := (rows 97 386 14 42 145 32 64 128 256), losses := [] }

theorem u40941 : Upper (D 7) (R 7) [96,384,10,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40942 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 386 14 42 148 113 81 209 337), lower := (rows 97 386 14 42 148 32 64 128 256), losses := [] }

theorem u40942 : Upper (D 7) (R 7) [96,384,10,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40943 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 386 14 42 208 53 85 149 277), lower := (rows 97 386 14 42 208 32 64 128 256), losses := [] }

theorem u40943 : Upper (D 7) (R 7) [96,384,10,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40944 : PairBound 9 := { available := 147, camps := [{ cop := 4, region := 430, targets := 64 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,6),(2,6),(3,6),(4,1)], upper := (rows 97 386 14 44 81 179 211 147 403), lower := (rows 97 386 14 44 81 32 64 128 256), losses := [] }

theorem u40944 : Upper (D 7) (R 7) [96,384,10,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40945 : Route 9 := (fun mask => (mask,id))

def c40945 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40945 : Upper (D 7) (R 7) [96,384,10,36,66] 13 := by
  apply FastRouting.sound _ _ [96,384,10,36,66] 13 (by decide) (choices 1) [1,16,128] r40945 c40945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29943
  · exact u29944
  · exact u29945

def r40946 : Route 9 := (fun mask => (mask,id))

def c40946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40946 : Upper (D 7) (R 7) [96,384,10,36,129] 13 := by
  apply FastRouting.sound _ _ [96,384,10,36,129] 13 (by decide) (choices 1) [1,2,16,64] r40946 c40946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29946
  · exact u29947
  · exact u29948
  · exact u29949

def b40947 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 14 44 146 113 81 209 337), lower := (rows 97 386 14 44 146 32 64 128 256), losses := [] }

theorem u40947 : Upper (D 7) (R 7) [96,384,10,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40948 : Route 9 := (fun mask => (mask,id))

def c40948 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40948 : Upper (D 7) (R 7) [96,384,10,36,192] 13 := by
  apply FastRouting.sound _ _ [96,384,10,36,192] 13 (by decide) (choices 1) [1,2,16] r40948 c40948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29950
  · exact u29951
  · exact u29952

def b40949 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 386 14 56 81 167 199 135 391), lower := (rows 97 386 14 56 81 32 64 128 256), losses := [] }

theorem u40949 : Upper (D 7) (R 7) [96,384,10,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40950 : Route 9 := (fun mask => (mask,id))

def c40950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40950 : Upper (D 7) (R 7) [96,384,10,48,66] 13 := by
  apply FastRouting.sound _ _ [96,384,10,48,66] 13 (by decide) (choices 1) [1,4,128] r40950 c40950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29953
  · exact u29954
  · exact u29955

def r40951 : Route 9 := (fun mask => (mask,id))

def c40951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40951 : Upper (D 7) (R 7) [96,384,10,48,68] 13 := by
  apply FastRouting.sound _ _ [96,384,10,48,68] 13 (by decide) (choices 1) [1,2,128] r40951 c40951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29956
  · exact u29957
  · exact u29958

def r40952 : Route 9 := (fun mask => (mask,id))

def c40952 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40952 : Upper (D 7) (R 7) [96,384,10,48,129] 13 := by
  apply FastRouting.sound _ _ [96,384,10,48,129] 13 (by decide) (choices 1) [1,2,4,64] r40952 c40952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29959
  · exact u29960
  · exact u29961
  · exact u29962

def b40953 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 14 56 146 101 69 197 325), lower := (rows 97 386 14 56 146 32 64 128 256), losses := [] }

theorem u40953 : Upper (D 7) (R 7) [96,384,10,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40954 : Route 9 := (fun mask => (mask,id))

def c40954 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40954 : Upper (D 7) (R 7) [96,384,10,48,132] 13 := by
  apply FastRouting.sound _ _ [96,384,10,48,132] 13 (by decide) (choices 1) [1,2,64] r40954 c40954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29963
  · exact u29964
  · exact u29965

def r40955 : Route 9 := (fun mask => (mask,id))

def c40955 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40955 : Upper (D 7) (R 7) [96,384,10,48,192] 13 := by
  apply FastRouting.sound _ _ [96,384,10,48,192] 13 (by decide) (choices 1) [1,2,4] r40955 c40955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29966
  · exact u29967
  · exact u29968

def b40956 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 386 14 104 145 55 87 151 279), lower := (rows 97 386 14 104 145 32 64 128 256), losses := [] }

theorem u40956 : Upper (D 7) (R 7) [96,384,10,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40957 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 386 14 104 148 51 83 147 275), lower := (rows 97 386 14 104 148 32 64 128 256), losses := [] }

theorem u40957 : Upper (D 7) (R 7) [96,384,10,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40958 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 386 14 137 49 118 86 214 342), lower := (rows 97 386 14 137 49 32 64 128 256), losses := [] }

theorem u40958 : Upper (D 7) (R 7) [96,384,10,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40959 : Route 9 := (fun mask => (mask,id))

def c40959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40959 : Upper (D 7) (R 7) [96,384,10,129,34] 13 := by
  apply FastRouting.sound _ _ [96,384,10,129,34] 13 (by decide) (choices 1) [1,4,16,64] r40959 c40959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29969
  · exact u29970
  · exact u29971
  · exact u29972

def r40960 : Route 9 := (fun mask => (mask,id))

def c40960 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40960 : Upper (D 7) (R 7) [96,384,10,129,36] 13 := by
  apply FastRouting.sound _ _ [96,384,10,129,36] 13 (by decide) (choices 1) [1,2,16,64] r40960 c40960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29973
  · exact u29974
  · exact u29975
  · exact u29976

def b40961 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 386 14 137 112 55 87 151 279), lower := (rows 97 386 14 137 112 32 64 128 256), losses := [] }

theorem u40961 : Upper (D 7) (R 7) [96,384,10,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40962 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 97 386 14 138 52 113 81 209 337), lower := (rows 97 386 14 138 52 32 64 128 256), losses := [] }

theorem u40962 : Upper (D 7) (R 7) [96,384,10,130,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40963 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 97 386 14 140 50 113 81 209 337), lower := (rows 97 386 14 140 50 32 64 128 256), losses := [] }

theorem u40963 : Upper (D 7) (R 7) [96,384,10,132,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40964 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 386 14 152 49 103 71 199 327), lower := (rows 97 386 14 152 49 32 64 128 256), losses := [] }

theorem u40964 : Upper (D 7) (R 7) [96,384,10,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40965 : Route 9 := (fun mask => (mask,id))

def c40965 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40965 : Upper (D 7) (R 7) [96,384,10,144,34] 13 := by
  apply FastRouting.sound _ _ [96,384,10,144,34] 13 (by decide) (choices 1) [1,4,64] r40965 c40965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29977
  · exact u29978
  · exact u29979

def r40966 : Route 9 := (fun mask => (mask,id))

def c40966 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40966 : Upper (D 7) (R 7) [96,384,10,144,36] 13 := by
  apply FastRouting.sound _ _ [96,384,10,144,36] 13 (by decide) (choices 1) [1,2,64] r40966 c40966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29980
  · exact u29981
  · exact u29982

def b40967 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 386 14 152 112 39 71 135 263), lower := (rows 97 386 14 152 112 32 64 128 256), losses := [] }

theorem u40967 : Upper (D 7) (R 7) [96,384,10,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40968 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 386 14 168 81 55 87 151 279), lower := (rows 97 386 14 168 81 32 64 128 256), losses := [] }

theorem u40968 : Upper (D 7) (R 7) [96,384,10,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40969 : Route 9 := (fun mask => (mask,id))

def c40969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40969 : Upper (D 7) (R 7) [96,384,10,160,66] 13 := by
  apply FastRouting.sound _ _ [96,384,10,160,66] 13 (by decide) (choices 1) [1,4,16] r40969 c40969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29983
  · exact u29984
  · exact u29985

def r40970 : Route 9 := (fun mask => (mask,id))

def c40970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40970 : Upper (D 7) (R 7) [96,384,10,160,68] 13 := by
  apply FastRouting.sound _ _ [96,384,10,160,68] 13 (by decide) (choices 1) [1,2,16] r40970 c40970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29986
  · exact u29987
  · exact u29988

def b40971 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 28 41 82 167 199 135 391), lower := (rows 97 386 28 41 82 32 64 128 256), losses := [] }

theorem u40971 : Upper (D 7) (R 7) [96,384,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40972 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 28, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 386 28 41 84 163 195 131 387), lower := (rows 97 386 28 41 84 32 64 128 256), losses := [] }

theorem u40972 : Upper (D 7) (R 7) [96,384,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40973 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 28 41 145 102 70 198 326), lower := (rows 97 386 28 41 145 32 64 128 256), losses := [] }

theorem u40973 : Upper (D 7) (R 7) [96,384,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40974 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 28 41 148 99 67 195 323), lower := (rows 97 386 28 41 148 32 64 128 256), losses := [] }

theorem u40974 : Upper (D 7) (R 7) [96,384,24,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40975 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 386 28 41 208 39 71 135 263), lower := (rows 97 386 28 41 208 32 64 128 256), losses := [] }

theorem u40975 : Upper (D 7) (R 7) [96,384,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40976 : Route 9 := (fun mask => (mask,id))

def c40976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40976 : Upper (D 7) (R 7) [96,384,24,34,66] 13 := by
  apply FastRouting.sound _ _ [96,384,24,34,66] 13 (by decide) (choices 1) [1,4,128] r40976 c40976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29989
  · exact u29990
  · exact u29991

def r40977 : Route 9 := (fun mask => (mask,id))

def c40977 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40977 : Upper (D 7) (R 7) [96,384,24,34,68] 13 := by
  apply FastRouting.sound _ _ [96,384,24,34,68] 13 (by decide) (choices 1) [1,2,128] r40977 c40977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29992
  · exact u29993
  · exact u29994

def r40978 : Route 9 := (fun mask => (mask,id))

def c40978 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40978 : Upper (D 7) (R 7) [96,384,24,34,129] 13 := by
  apply FastRouting.sound _ _ [96,384,24,34,129] 13 (by decide) (choices 1) [1,2,4,64] r40978 c40978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29995
  · exact u29996
  · exact u29997
  · exact u29998

def b40979 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 28 42 146 101 69 197 325), lower := (rows 97 386 28 42 146 32 64 128 256), losses := [] }

theorem u40979 : Upper (D 7) (R 7) [96,384,24,34,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u40979
end Delivery.IrregularNine14.P07
