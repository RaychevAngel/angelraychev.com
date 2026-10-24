import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0414
import IrregularNine14P07C0415
import IrregularNine14P07C0416

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37920 : Route 9 := (fun mask => (mask,id))

def c37920 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37920 : Upper (D 7) (R 7) [36,192,3,80,264] 13 := by
  apply FastRouting.sound _ _ [36,192,3,80,264] 13 (by decide) (choices 1) [1,2,128] r37920 c37920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24877
  · exact u24878
  · exact u24879

def r37921 : Route 9 := (fun mask => (mask,id))

def c37921 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37921 : Upper (D 7) (R 7) [36,192,3,80,288] 13 := by
  apply FastRouting.sound _ _ [36,192,3,80,288] 13 (by decide) (choices 1) [1,2,8,128] r37921 c37921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24880
  · exact u24881
  · exact u24882
  · exact u24883

def r37922 : Route 9 := (fun mask => (mask,id))

def c37922 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37922 : Upper (D 7) (R 7) [36,192,3,80,384] 13 := by
  apply FastRouting.sound _ _ [36,192,3,80,384] 13 (by decide) (choices 1) [1,2,8] r37922 c37922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24884
  · exact u24885
  · exact u24886

def r37923 : Route 9 := (fun mask => (mask,id))

def c37923 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37923 : Upper (D 7) (R 7) [36,192,3,96,257] 13 := by
  apply FastRouting.sound _ _ [36,192,3,96,257] 13 (by decide) (choices 1) [2,8,16,128] r37923 c37923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24887
  · exact u24888
  · exact u24889
  · exact u24890

def r37924 : Route 9 := (fun mask => (mask,id))

def c37924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37924 : Upper (D 7) (R 7) [36,192,3,96,258] 13 := by
  apply FastRouting.sound _ _ [36,192,3,96,258] 13 (by decide) (choices 1) [1,8,16,128] r37924 c37924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24891
  · exact u24892
  · exact u24893
  · exact u24894

def r37925 : Route 9 := (fun mask => (mask,id))

def c37925 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37925 : Upper (D 7) (R 7) [36,192,3,96,264] 13 := by
  apply FastRouting.sound _ _ [36,192,3,96,264] 13 (by decide) (choices 1) [1,2,16,128] r37925 c37925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24895
  · exact u24896
  · exact u24897
  · exact u24898

def r37926 : Route 9 := (fun mask => (mask,id))

def c37926 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37926 : Upper (D 7) (R 7) [36,192,3,96,384] 13 := by
  apply FastRouting.sound _ _ [36,192,3,96,384] 13 (by decide) (choices 1) [1,2,8,16] r37926 c37926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24899
  · exact u24900
  · exact u24901
  · exact u24902

def b37927 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 7 200 273 58 122 186 314), lower := (rows 37 194 7 200 273 32 64 128 256), losses := [] }

theorem u37927 : Upper (D 7) (R 7) [36,192,3,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37928 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 7 200 274 57 121 185 313), lower := (rows 37 194 7 200 274 32 64 128 256), losses := [] }

theorem u37928 : Upper (D 7) (R 7) [36,192,3,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37929 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 7 200 280 51 115 179 307), lower := (rows 37 194 7 200 280 32 64 128 256), losses := [] }

theorem u37929 : Upper (D 7) (R 7) [36,192,3,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37930 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 7 200 304 59 91 155 283), lower := (rows 37 194 7 200 304 32 64 128 256), losses := [] }

theorem u37930 : Upper (D 7) (R 7) [36,192,3,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37931 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 37 194 13 26 19 480 480 480 480), lower := (rows 37 194 13 26 19 32 64 128 256), losses := [] }

theorem u37931 : Upper (D 7) (R 7) [36,192,9,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37932 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 13 26 49 482 450 450 450), lower := (rows 37 194 13 26 49 32 64 128 256), losses := [] }

theorem u37932 : Upper (D 7) (R 7) [36,192,9,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37933 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 13 26 50 481 449 449 449), lower := (rows 37 194 13 26 50 32 64 128 256), losses := [] }

theorem u37933 : Upper (D 7) (R 7) [36,192,9,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37934 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 194 13 26 81 418 482 418 418), lower := (rows 37 194 13 26 81 32 64 128 256), losses := [] }

theorem u37934 : Upper (D 7) (R 7) [36,192,9,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37935 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 194 13 26 82 417 481 417 417), lower := (rows 37 194 13 26 82 32 64 128 256), losses := [] }

theorem u37935 : Upper (D 7) (R 7) [36,192,9,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37936 : Route 9 := (fun mask => (mask,id))

def c37936 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37936 : Upper (D 7) (R 7) [36,192,9,18,96] 13 := by
  apply FastRouting.sound _ _ [36,192,9,18,96] 13 (by decide) (choices 1) [1,2,128,256] r37936 c37936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24903
  · exact u24904
  · exact u24905
  · exact u24906

def b37937 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 13 26 208 291 355 419 291), lower := (rows 37 194 13 26 208 32 64 128 256), losses := [] }

theorem u37937 : Upper (D 7) (R 7) [36,192,9,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37938 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37938 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37938 : Upper (D 7) (R 7) [36,192,9,18,257] 13 := by
  apply FastRouting.sound _ _ [36,192,9,18,257] 13 (by decide) (choices 1) [2,64] r37938 c37938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24907
  · exact u24908

def b37939 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 13 26 274 225 225 225 481), lower := (rows 37 194 13 26 274 32 64 128 256), losses := [] }

theorem u37939 : Upper (D 7) (R 7) [36,192,9,18,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37940 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37940 : Upper (D 7) (R 7) [36,192,9,18,288] 13 := by
  apply FastRouting.sound _ _ [36,192,9,18,288] 13 (by decide) (choices 1) [1,2,64] r37940 c37940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24909
  · exact u24910
  · exact u24911

def r37941 : Route 9 := (fun mask => (mask,id))

def c37941 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37941 : Upper (D 7) (R 7) [36,192,9,18,320] 13 := by
  apply FastRouting.sound _ _ [36,192,9,18,320] 13 (by decide) (choices 1) [1,2,128] r37941 c37941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24912
  · exact u24913
  · exact u24914

def b37942 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 490, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 194 13 88 19 418 482 418 418), lower := (rows 37 194 13 88 19 32 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 146 274), good := (rows 37 418 13 445 435 32 0 128 256) }] }

theorem u37942 : Upper (D 7) (R 7) [36,192,9,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37943 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 13 88 49 418 450 386 386), lower := (rows 37 194 13 88 49 32 64 128 256), losses := [] }

theorem u37943 : Upper (D 7) (R 7) [36,192,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37944 : Route 9 := (fun mask => (mask,id))

def c37944 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37944 : Upper (D 7) (R 7) [36,192,9,80,34] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,34] 13 (by decide) (choices 1) [1,2,128,256] r37944 c37944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24915
  · exact u24916
  · exact u24917
  · exact u24918

def r37945 : Route 9 := (fun mask => (mask,id))

def c37945 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37945 : Upper (D 7) (R 7) [36,192,9,80,129] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,129] 13 (by decide) (choices 1) [2,256] r37945 c37945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24919
  · exact u24920

def b37946 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 13 88 146 291 355 419 291), lower := (rows 37 194 13 88 146 32 64 128 256), losses := [] }

theorem u37946 : Upper (D 7) (R 7) [36,192,9,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37947 : Route 9 := (fun mask => (mask,id))

def c37947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37947 : Upper (D 7) (R 7) [36,192,9,80,160] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,160] 13 (by decide) (choices 1) [1,2,256] r37947 c37947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24921
  · exact u24922
  · exact u24923

def r37948 : Route 9 := (fun mask => (mask,id))

def c37948 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37948 : Upper (D 7) (R 7) [36,192,9,80,257] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,257] 13 (by decide) (choices 1) [2,128] r37948 c37948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24924
  · exact u24925

def r37949 : Route 9 := (fun mask => (mask,id))

def c37949 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37949 : Upper (D 7) (R 7) [36,192,9,80,258] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,258] 13 (by decide) (choices 1) [1,2,128] r37949 c37949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24926
  · exact u24927
  · exact u24928

def r37950 : Route 9 := (fun mask => (mask,id))

def c37950 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37950 : Upper (D 7) (R 7) [36,192,9,80,288] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,288] 13 (by decide) (choices 1) [1,2,128] r37950 c37950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24929
  · exact u24930
  · exact u24931

def r37951 : Route 9 := (fun mask => (mask,id))

def c37951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37951 : Upper (D 7) (R 7) [36,192,9,80,384] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,384] 13 (by decide) (choices 1) [1,2] r37951 c37951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24932
  · exact u24933

def r37952 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37952 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37952 : Upper (D 7) (R 7) [36,192,9,258,3] 13 := by
  apply FastRouting.sound _ _ [36,192,9,258,3] 13 (by decide) (choices 1) [16,64] r37952 c37952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24934
  · exact u24935

def b37953 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 13 266 49 242 210 210 466), lower := (rows 37 194 13 266 49 32 64 128 256), losses := [] }

theorem u37953 : Upper (D 7) (R 7) [36,192,9,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37954 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37954 : Upper (D 7) (R 7) [36,192,9,258,34] 13 := by
  apply FastRouting.sound _ _ [36,192,9,258,34] 13 (by decide) (choices 1) [1,16,64] r37954 c37954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24936
  · exact u24937
  · exact u24938

def r37955 : Route 9 := (fun mask => (mask,id))

def c37955 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37955 : Upper (D 7) (R 7) [36,192,9,258,65] 13 := by
  apply FastRouting.sound _ _ [36,192,9,258,65] 13 (by decide) (choices 1) [2,16,128] r37955 c37955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24939
  · exact u24940
  · exact u24941

def b37956 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 13 266 82 177 241 177 433), lower := (rows 37 194 13 266 82 32 64 128 256), losses := [] }

theorem u37956 : Upper (D 7) (R 7) [36,192,9,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37957 : Route 9 := (fun mask => (mask,id))

def c37957 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37957 : Upper (D 7) (R 7) [36,192,9,258,96] 13 := by
  apply FastRouting.sound _ _ [36,192,9,258,96] 13 (by decide) (choices 1) [1,2,16,128] r37957 c37957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24942
  · exact u24943
  · exact u24944
  · exact u24945

def b37958 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 13 266 208 51 115 179 307), lower := (rows 37 194 13 266 208 32 64 128 256), losses := [] }

theorem u37958 : Upper (D 7) (R 7) [36,192,9,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37959 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37959 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37959 : Upper (D 7) (R 7) [36,192,9,272,3] 13 := by
  apply FastRouting.sound _ _ [36,192,9,272,3] 13 (by decide) (choices 1) [2,64] r37959 c37959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24946
  · exact u24947

def b37960 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 13 280 49 226 194 194 450), lower := (rows 37 194 13 280 49 32 64 128 256), losses := [] }

theorem u37960 : Upper (D 7) (R 7) [36,192,9,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37961 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37961 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37961 : Upper (D 7) (R 7) [36,192,9,272,34] 13 := by
  apply FastRouting.sound _ _ [36,192,9,272,34] 13 (by decide) (choices 1) [1,2,64] r37961 c37961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24948
  · exact u24949
  · exact u24950

def r37962 : Route 9 := (fun mask => (mask,id))

def c37962 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37962 : Upper (D 7) (R 7) [36,192,9,272,65] 13 := by
  apply FastRouting.sound _ _ [36,192,9,272,65] 13 (by decide) (choices 1) [2,128] r37962 c37962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24951
  · exact u24952

def b37963 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 13 280 82 163 227 163 419), lower := (rows 37 194 13 280 82 32 64 128 256), losses := [] }

theorem u37963 : Upper (D 7) (R 7) [36,192,9,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37964 : Route 9 := (fun mask => (mask,id))

def c37964 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37964 : Upper (D 7) (R 7) [36,192,9,272,96] 13 := by
  apply FastRouting.sound _ _ [36,192,9,272,96] 13 (by decide) (choices 1) [1,2,128] r37964 c37964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24953
  · exact u24954
  · exact u24955

def b37965 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 13 280 208 35 99 163 291), lower := (rows 37 194 13 280 208 32 64 128 256), losses := [] }

theorem u37965 : Upper (D 7) (R 7) [36,192,9,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37966 : Route 9 := (fun mask => (mask,id))

def c37966 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37966 : Upper (D 7) (R 7) [36,192,9,320,3] 13 := by
  apply FastRouting.sound _ _ [36,192,9,320,3] 13 (by decide) (choices 1) [2,16,128] r37966 c37966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24956
  · exact u24957
  · exact u24958

def b37967 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 13 328 49 178 210 146 402), lower := (rows 37 194 13 328 49 32 64 128 256), losses := [] }

theorem u37967 : Upper (D 7) (R 7) [36,192,9,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37968 : Route 9 := (fun mask => (mask,id))

def c37968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37968 : Upper (D 7) (R 7) [36,192,9,320,34] 13 := by
  apply FastRouting.sound _ _ [36,192,9,320,34] 13 (by decide) (choices 1) [1,2,16,128] r37968 c37968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24959
  · exact u24960
  · exact u24961
  · exact u24962

def r37969 : Route 9 := (fun mask => (mask,id))

def c37969 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37969 : Upper (D 7) (R 7) [36,192,9,320,129] 13 := by
  apply FastRouting.sound _ _ [36,192,9,320,129] 13 (by decide) (choices 1) [2,16] r37969 c37969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24963
  · exact u24964

def b37970 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 13 328 146 51 115 179 307), lower := (rows 37 194 13 328 146 32 64 128 256), losses := [] }

theorem u37970 : Upper (D 7) (R 7) [36,192,9,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37971 : Route 9 := (fun mask => (mask,id))

def c37971 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37971 : Upper (D 7) (R 7) [36,192,9,320,160] 13 := by
  apply FastRouting.sound _ _ [36,192,9,320,160] 13 (by decide) (choices 1) [1,2,16] r37971 c37971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24965
  · exact u24966
  · exact u24967

def b37972 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 37 194 14 25 19 480 480 480 480), lower := (rows 37 194 14 25 19 32 64 128 256), losses := [] }

theorem u37972 : Upper (D 7) (R 7) [36,192,10,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37973 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 194 14 25 49 482 450 450 450), lower := (rows 37 194 14 25 49 32 64 128 256), losses := [] }

theorem u37973 : Upper (D 7) (R 7) [36,192,10,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37974 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 14 25 50 481 449 449 449), lower := (rows 37 194 14 25 50 32 64 128 256), losses := [] }

theorem u37974 : Upper (D 7) (R 7) [36,192,10,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37975 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 194 14 25 81 418 482 418 418), lower := (rows 37 194 14 25 81 32 64 128 256), losses := [] }

theorem u37975 : Upper (D 7) (R 7) [36,192,10,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37976 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 14 25 82 417 481 417 417), lower := (rows 37 194 14 25 82 32 64 128 256), losses := [] }

theorem u37976 : Upper (D 7) (R 7) [36,192,10,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37977 : Route 9 := (fun mask => (mask,id))

def c37977 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37977 : Upper (D 7) (R 7) [36,192,10,17,96] 13 := by
  apply FastRouting.sound _ _ [36,192,10,17,96] 13 (by decide) (choices 1) [1,2,128,256] r37977 c37977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24968
  · exact u24969
  · exact u24970
  · exact u24971

def b37978 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 14 25 208 291 355 419 291), lower := (rows 37 194 14 25 208 32 64 128 256), losses := [] }

theorem u37978 : Upper (D 7) (R 7) [36,192,10,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37979 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 194 14 25 273 226 226 226 482), lower := (rows 37 194 14 25 273 32 64 128 256), losses := [] }

theorem u37979 : Upper (D 7) (R 7) [36,192,10,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u37979
end Delivery.IrregularNine14.P07
