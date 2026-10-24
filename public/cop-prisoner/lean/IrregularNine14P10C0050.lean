import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0020
import IrregularNine14P10C0021
import IrregularNine14P10C0022
import IrregularNine14P10C0023
import IrregularNine14P10C0024
import IrregularNine14P10C0025
import IrregularNine14P10C0029
import IrregularNine14P10C0030
import IrregularNine14P10C0031
import IrregularNine14P10C0032
import IrregularNine14P10C0033
import IrregularNine14P10C0034

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3000 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 44 88 436 420 484 420 420), lower := (rows 35 67 44 88 16 32 64 128 256), losses := [] }

theorem u3000 : Upper (D 10) (R 10) [34,65,40,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3000 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3001 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 44 104 404 436 468 404 404), lower := (rows 35 67 44 104 16 32 64 128 256), losses := [] }

theorem u3001 : Upper (D 10) (R 10) [34,65,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3001 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3002_160 : Upper (D 10) (R 10) [34,65,40,132,160] 13 :=
  permutation_upper _ _ _ [34,65,40,132,96] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1939

theorem m3002_384 : Upper (D 10) (R 10) [34,65,40,132,384] 13 :=
  permutation_upper _ _ _ [34,65,40,132,320] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1942

def r3002 : Route 9 := (fun mask => (mask,id))

def c3002 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3002 : Upper (D 10) (R 10) [34,65,40,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132] 13 (by decide) (choices 2) [96,160,192,288,320,384] r3002 c3002
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1939
  · exact m3002_160
  · exact u1940
  · exact u1941
  · exact u1942
  · exact m3002_384

theorem m3003_36 : Upper (D 10) (R 10) [34,65,40,144,36] 13 :=
  permutation_upper _ _ _ [34,36,65,48,136] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1866

def r3003 : Route 9 := (fun mask => (mask,id))

def c3003 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3003 : Upper (D 10) (R 10) [34,65,40,144] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144] 13 (by decide) (choices 2) [36,68,96,132,160,192,260,288,320,384] r3003 c3003
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3003_36
  · exact u1943
  · exact u1944
  · exact u1945
  · exact u1946
  · exact u1947
  · exact u1948
  · exact u1949
  · exact u1950
  · exact u1951

def b3004 : PairBound 9 := { available := 468, camps := [{ cop := 3, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 35 67 44 168 468 500 468 468 468), lower := (rows 35 67 44 168 16 32 64 128 256), losses := [] }

theorem u3004 : Upper (D 10) (R 10) [34,65,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3004 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3005 : PairBound 9 := { available := 436, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 44 200 436 436 500 436 436), lower := (rows 35 67 44 200 16 32 64 128 256), losses := [] }

theorem u3005 : Upper (D 10) (R 10) [34,65,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3005 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3006_36 : Upper (D 10) (R 10) [34,65,40,384,36] 13 :=
  permutation_upper _ _ _ [34,36,192,48,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1914

def r3006 : Route 9 := (fun mask => match mask with | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3006 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3006 : Upper (D 10) (R 10) [34,65,40,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384] 13 (by decide) (choices 2) [36,68,96,132,160,192,384] r3006 c3006
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3006_36
  · exact u1960
  · exact u1961
  · exact u1962
  · exact u1963
  · exact u1964
  · exact u1965

theorem m3007_40 : Upper (D 10) (R 10) [34,65,48,132,40] 13 :=
  permutation_upper _ _ _ [34,36,65,48,136] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1866

theorem m3007_72 : Upper (D 10) (R 10) [34,65,48,132,72] 13 :=
  permutation_upper _ _ _ [34,65,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1934

theorem m3007_96 : Upper (D 10) (R 10) [34,65,48,132,96] 13 :=
  permutation_upper _ _ _ [34,65,40,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1937

theorem m3007_136 : Upper (D 10) (R 10) [34,65,48,132,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1945

theorem m3007_160 : Upper (D 10) (R 10) [34,65,48,132,160] 13 :=
  permutation_upper _ _ _ [34,65,40,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1952

theorem m3007_192 : Upper (D 10) (R 10) [34,65,48,132,192] 13 :=
  permutation_upper _ _ _ [34,65,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1955

theorem m3007_264 : Upper (D 10) (R 10) [34,65,48,132,264] 13 :=
  permutation_upper _ _ _ [34,65,40,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1948

theorem m3007_288 : Upper (D 10) (R 10) [34,65,48,132,288] 13 :=
  permutation_upper _ _ _ [34,65,40,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1953

theorem m3007_320 : Upper (D 10) (R 10) [34,65,48,132,320] 13 :=
  permutation_upper _ _ _ [34,65,40,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1957

theorem m3007_384 : Upper (D 10) (R 10) [34,65,48,132,384] 13 :=
  permutation_upper _ _ _ [34,65,40,384,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1962

def r3007 : Route 9 := (fun mask => (mask,id))

def c3007 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3007 : Upper (D 10) (R 10) [34,65,48,132] 13 := by
  apply FastRouting.sound _ _ [34,65,48,132] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r3007 c3007
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3007_40
  · exact m3007_72
  · exact m3007_96
  · exact m3007_136
  · exact m3007_160
  · exact m3007_192
  · exact m3007_264
  · exact m3007_288
  · exact m3007_320
  · exact m3007_384

theorem m3008_12 : Upper (D 10) (R 10) [34,65,48,160,12] 13 :=
  permutation_upper _ _ _ [6,33,96,48,136] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1242

theorem m3008_68 : Upper (D 10) (R 10) [34,65,48,160,68] 13 :=
  permutation_upper _ _ _ [34,65,40,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1932

theorem m3008_72 : Upper (D 10) (R 10) [34,65,48,160,72] 13 :=
  permutation_upper _ _ _ [34,65,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1935

theorem m3008_132 : Upper (D 10) (R 10) [34,65,48,160,132] 13 :=
  permutation_upper _ _ _ [34,65,40,132,96] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1939

theorem m3008_136 : Upper (D 10) (R 10) [34,65,48,160,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1946

theorem m3008_192 : Upper (D 10) (R 10) [34,65,48,160,192] 13 :=
  permutation_upper _ _ _ [34,65,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1956

theorem m3008_260 : Upper (D 10) (R 10) [34,65,48,160,260] 13 :=
  permutation_upper _ _ _ [34,65,40,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1941

theorem m3008_264 : Upper (D 10) (R 10) [34,65,48,160,264] 13 :=
  permutation_upper _ _ _ [34,65,40,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1949

theorem m3008_320 : Upper (D 10) (R 10) [34,65,48,160,320] 13 :=
  permutation_upper _ _ _ [34,65,40,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1958

theorem m3008_384 : Upper (D 10) (R 10) [34,65,48,160,384] 13 :=
  permutation_upper _ _ _ [34,65,40,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1963

def r3008 : Route 9 := (fun mask => (mask,id))

def c3008 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u3008 : Upper (D 10) (R 10) [34,65,48,160] 13 := by
  apply FastRouting.sound _ _ [34,65,48,160] 13 (by decide) (choices 2) [12,68,72,132,136,192,260,264,320,384] r3008 c3008
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3008_12
  · exact m3008_68
  · exact m3008_72
  · exact m3008_132
  · exact m3008_136
  · exact m3008_192
  · exact m3008_260
  · exact m3008_264
  · exact m3008_320
  · exact m3008_384

theorem m3009_12 : Upper (D 10) (R 10) [34,65,48,384,12] 13 :=
  permutation_upper _ _ _ [6,33,192,48,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1261

theorem m3009_36 : Upper (D 10) (R 10) [34,65,48,384,36] 13 :=
  permutation_upper _ _ _ [34,33,40,68,384] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1843

theorem m3009_40 : Upper (D 10) (R 10) [34,65,48,384,40] 13 :=
  permutation_upper _ _ _ [34,36,192,48,264] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1914

theorem m3009_68 : Upper (D 10) (R 10) [34,65,48,384,68] 13 :=
  permutation_upper _ _ _ [34,65,40,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1933

theorem m3009_72 : Upper (D 10) (R 10) [34,65,48,384,72] 13 :=
  permutation_upper _ _ _ [34,65,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1936

theorem m3009_96 : Upper (D 10) (R 10) [34,65,48,384,96] 13 :=
  permutation_upper _ _ _ [34,65,40,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1938

theorem m3009_132 : Upper (D 10) (R 10) [34,65,48,384,132] 13 :=
  permutation_upper _ _ _ [34,65,40,132,320] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1942

theorem m3009_136 : Upper (D 10) (R 10) [34,65,48,384,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1951

theorem m3009_160 : Upper (D 10) (R 10) [34,65,48,384,160] 13 :=
  permutation_upper _ _ _ [34,65,40,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1954

theorem m3009_192 : Upper (D 10) (R 10) [34,65,48,384,192] 13 :=
  permutation_upper _ _ _ [34,65,40,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1959

theorem m3009_384 : Upper (D 10) (R 10) [34,65,48,384,384] 13 :=
  permutation_upper _ _ _ [34,65,40,384,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1965

def r3009 : Route 9 := (fun mask => match mask with | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3009 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u3009 : Upper (D 10) (R 10) [34,65,48,384] 13 := by
  apply FastRouting.sound _ _ [34,65,48,384] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192,384] r3009 c3009
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3009_12
  · exact m3009_36
  · exact m3009_40
  · exact m3009_68
  · exact m3009_72
  · exact m3009_96
  · exact m3009_132
  · exact m3009_136
  · exact m3009_160
  · exact m3009_192
  · exact m3009_384

def b3010 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 67 76 140 432 432 496 432 432), lower := (rows 35 67 76 140 16 32 64 128 256), losses := [] }

theorem u3010 : Upper (D 10) (R 10) [34,65,72,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3010 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3011 : PairBound 9 := { available := 436, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 76 168 436 436 500 436 436), lower := (rows 35 67 76 168 16 32 64 128 256), losses := [] }

theorem u3011 : Upper (D 10) (R 10) [34,65,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3011 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3012 : PairBound 9 := { available := 436, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 76 392 436 436 500 436 436), lower := (rows 35 67 76 392 16 32 64 128 256), losses := [] }

theorem u3012 : Upper (D 10) (R 10) [34,65,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3012 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3013 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 84 140 440 424 488 424 424), lower := (rows 35 67 84 140 16 32 64 128 256), losses := [] }

theorem u3013 : Upper (D 10) (R 10) [34,65,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3013 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3014 : PairBound 9 := { available := 428, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 84 168 444 428 492 428 428), lower := (rows 35 67 84 168 16 32 64 128 256), losses := [] }

theorem u3014 : Upper (D 10) (R 10) [34,65,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3014 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3015 : PairBound 9 := { available := 428, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 84 392 444 428 492 428 428), lower := (rows 35 67 84 392 16 32 64 128 256), losses := [] }

theorem u3015 : Upper (D 10) (R 10) [34,65,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3015 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3016 : PairBound 9 := { available := 440, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 100 140 440 440 504 440 440), lower := (rows 35 67 100 140 16 32 64 128 256), losses := [] }

theorem u3016 : Upper (D 10) (R 10) [34,65,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3016 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3017 : PairBound 9 := { available := 412, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 100 168 412 444 476 412 412), lower := (rows 35 67 100 168 16 32 64 128 256), losses := [] }

theorem u3017 : Upper (D 10) (R 10) [34,65,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3017 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3018 : PairBound 9 := { available := 444, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 100 392 444 444 508 444 444), lower := (rows 35 67 100 392 16 32 64 128 256), losses := [] }

theorem u3018 : Upper (D 10) (R 10) [34,65,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3018 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3019 : PairBound 9 := { available := 368, camps := [{ cop := 7, region := 12, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 35 67 140 140 368 368 368 496 368), lower := (rows 35 67 140 140 16 32 64 128 256), losses := [] }

theorem u3019 : Upper (D 10) (R 10) [34,65,136,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3019 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3020 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 152 372 356 356 484 356), lower := (rows 35 67 140 152 16 32 64 128 256), losses := [] }

theorem u3020 : Upper (D 10) (R 10) [34,65,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3020 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3021 : PairBound 9 := { available := 372, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 168 372 372 372 500 372), lower := (rows 35 67 140 168 16 32 64 128 256), losses := [] }

theorem u3021 : Upper (D 10) (R 10) [34,65,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3021 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3022 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 200 308 308 372 436 308), lower := (rows 35 67 140 200 16 32 64 128 256), losses := [] }

theorem u3022 : Upper (D 10) (R 10) [34,65,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3022 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3023_96 : Upper (D 10) (R 10) [34,65,136,260,96] 13 :=
  permutation_upper _ _ _ [34,65,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1981

theorem m3023_288 : Upper (D 10) (R 10) [34,65,136,260,288] 13 :=
  permutation_upper _ _ _ [34,65,136,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1991

theorem m3023_320 : Upper (D 10) (R 10) [34,65,136,260,320] 13 :=
  permutation_upper _ _ _ [34,65,136,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1992

def r3023 : Route 9 := (fun mask => (mask,id))

def c3023 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3023 : Upper (D 10) (R 10) [34,65,136,260] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260] 13 (by decide) (choices 2) [96,160,192,288,320,384] r3023 c3023
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3023_96
  · exact u1991
  · exact u1992
  · exact m3023_288
  · exact m3023_320
  · exact u1993

theorem m3024_36 : Upper (D 10) (R 10) [34,65,136,272,36] 13 :=
  permutation_upper _ _ _ [34,65,40,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1948

theorem m3024_68 : Upper (D 10) (R 10) [34,65,136,272,68] 13 :=
  permutation_upper _ _ _ [34,65,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1969

theorem m3024_96 : Upper (D 10) (R 10) [34,65,136,272,96] 13 :=
  permutation_upper _ _ _ [34,65,96,132,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1978

theorem m3024_132 : Upper (D 10) (R 10) [34,65,136,272,132] 13 :=
  permutation_upper _ _ _ [34,65,136,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1985

theorem m3024_260 : Upper (D 10) (R 10) [34,65,136,272,260] 13 :=
  permutation_upper _ _ _ [34,65,136,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1985

theorem m3024_288 : Upper (D 10) (R 10) [34,65,136,272,288] 13 :=
  permutation_upper _ _ _ [34,65,136,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1987

theorem m3024_320 : Upper (D 10) (R 10) [34,65,136,272,320] 13 :=
  permutation_upper _ _ _ [34,65,136,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1989

def r3024 : Route 9 := (fun mask => (mask,id))

def c3024 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3024 : Upper (D 10) (R 10) [34,65,136,272] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272] 13 (by decide) (choices 2) [36,68,96,132,160,192,260,288,320,384] r3024 c3024
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3024_36
  · exact m3024_68
  · exact m3024_96
  · exact m3024_132
  · exact u1994
  · exact u1995
  · exact m3024_260
  · exact m3024_288
  · exact m3024_320
  · exact u1996

theorem m3025_36 : Upper (D 10) (R 10) [34,65,136,288,36] 13 :=
  permutation_upper _ _ _ [34,65,40,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1949

theorem m3025_68 : Upper (D 10) (R 10) [34,65,136,288,68] 13 :=
  permutation_upper _ _ _ [34,65,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1970

theorem m3025_96 : Upper (D 10) (R 10) [34,65,136,288,96] 13 :=
  permutation_upper _ _ _ [34,65,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1982

theorem m3025_132 : Upper (D 10) (R 10) [34,65,136,288,132] 13 :=
  permutation_upper _ _ _ [34,65,136,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1986

theorem m3025_260 : Upper (D 10) (R 10) [34,65,136,288,260] 13 :=
  permutation_upper _ _ _ [34,65,136,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1994

def r3025 : Route 9 := (fun mask => (mask,id))

def c3025 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3025 : Upper (D 10) (R 10) [34,65,136,288] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288] 13 (by decide) (choices 2) [36,68,96,132,160,192,260,288,320,384] r3025 c3025
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3025_36
  · exact m3025_68
  · exact m3025_96
  · exact m3025_132
  · exact u1997
  · exact u1998
  · exact m3025_260
  · exact u1999
  · exact u2000
  · exact u2001

def b3026 : PairBound 9 := { available := 436, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 140 328 436 436 500 436 436), lower := (rows 35 67 140 328 16 32 64 128 256), losses := [] }

theorem u3026 : Upper (D 10) (R 10) [34,65,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3026 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3027 : PairBound 9 := { available := 372, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 140 392 372 372 372 500 372), lower := (rows 35 67 140 392 16 32 64 128 256), losses := [] }

theorem u3027 : Upper (D 10) (R 10) [34,65,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3027 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3028_12 : Upper (D 10) (R 10) [34,65,144,160,12] 13 :=
  permutation_upper _ _ _ [6,65,96,48,136] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1444

theorem m3028_36 : Upper (D 10) (R 10) [34,65,144,160,36] 13 :=
  permutation_upper _ _ _ [34,65,40,132,96] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1939

theorem m3028_40 : Upper (D 10) (R 10) [34,65,144,160,40] 13 :=
  permutation_upper _ _ _ [34,65,40,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1952

theorem m3028_68 : Upper (D 10) (R 10) [34,65,144,160,68] 13 :=
  permutation_upper _ _ _ [34,65,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1966

theorem m3028_72 : Upper (D 10) (R 10) [34,65,144,160,72] 13 :=
  permutation_upper _ _ _ [34,65,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1971

theorem m3028_96 : Upper (D 10) (R 10) [34,65,144,160,96] 13 :=
  permutation_upper _ _ _ [34,65,96,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1977

theorem m3028_260 : Upper (D 10) (R 10) [34,65,144,160,260] 13 :=
  permutation_upper _ _ _ [34,65,136,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1991

theorem m3028_264 : Upper (D 10) (R 10) [34,65,144,160,264] 13 :=
  permutation_upper _ _ _ [34,65,136,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1994

theorem m3028_288 : Upper (D 10) (R 10) [34,65,144,160,288] 13 :=
  permutation_upper _ _ _ [34,65,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1997

theorem m3028_320 : Upper (D 10) (R 10) [34,65,144,160,320] 13 :=
  permutation_upper _ _ _ [34,65,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2002

def r3028 : Route 9 := (fun mask => (mask,id))

def c3028 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3028 : Upper (D 10) (R 10) [34,65,144,160] 13 := by
  apply FastRouting.sound _ _ [34,65,144,160] 13 (by decide) (choices 2) [12,36,40,68,72,96,260,264,288,320] r3028 c3028
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3028_12
  · exact m3028_36
  · exact m3028_40
  · exact m3028_68
  · exact m3028_72
  · exact m3028_96
  · exact m3028_260
  · exact m3028_264
  · exact m3028_288
  · exact m3028_320

theorem m3029_12 : Upper (D 10) (R 10) [34,65,144,288,12] 13 :=
  permutation_upper _ _ _ [6,65,160,48,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1487

theorem m3029_36 : Upper (D 10) (R 10) [34,65,144,288,36] 13 :=
  permutation_upper _ _ _ [34,65,40,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1941

theorem m3029_40 : Upper (D 10) (R 10) [34,65,144,288,40] 13 :=
  permutation_upper _ _ _ [34,65,40,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1953

theorem m3029_68 : Upper (D 10) (R 10) [34,65,144,288,68] 13 :=
  permutation_upper _ _ _ [34,65,72,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1967

theorem m3029_72 : Upper (D 10) (R 10) [34,65,144,288,72] 13 :=
  permutation_upper _ _ _ [34,65,72,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1972

theorem m3029_96 : Upper (D 10) (R 10) [34,65,144,288,96] 13 :=
  permutation_upper _ _ _ [34,65,96,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1979

theorem m3029_132 : Upper (D 10) (R 10) [34,65,144,288,132] 13 :=
  permutation_upper _ _ _ [34,65,136,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1984

theorem m3029_136 : Upper (D 10) (R 10) [34,65,144,288,136] 13 :=
  permutation_upper _ _ _ [34,65,136,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1986

theorem m3029_160 : Upper (D 10) (R 10) [34,65,144,288,160] 13 :=
  permutation_upper _ _ _ [34,65,136,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1988

theorem m3029_192 : Upper (D 10) (R 10) [34,65,144,288,192] 13 :=
  permutation_upper _ _ _ [34,65,136,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1990

theorem m3029_260 : Upper (D 10) (R 10) [34,65,144,288,260] 13 :=
  permutation_upper _ _ _ [34,65,136,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1991

theorem m3029_264 : Upper (D 10) (R 10) [34,65,144,288,264] 13 :=
  permutation_upper _ _ _ [34,65,136,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1987

theorem m3029_288 : Upper (D 10) (R 10) [34,65,144,288,288] 13 :=
  permutation_upper _ _ _ [34,65,136,288,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1999

theorem m3029_320 : Upper (D 10) (R 10) [34,65,144,288,320] 13 :=
  permutation_upper _ _ _ [34,65,136,320,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2003

theorem m3029_384 : Upper (D 10) (R 10) [34,65,144,288,384] 13 :=
  permutation_upper _ _ _ [34,65,136,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2005

def r3029 : Route 9 := (fun mask => (mask,id))

def c3029 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u3029 : Upper (D 10) (R 10) [34,65,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,144,288] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192,260,264,288,320,384] r3029 c3029
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3029_12
  · exact m3029_36
  · exact m3029_40
  · exact m3029_68
  · exact m3029_72
  · exact m3029_96
  · exact m3029_132
  · exact m3029_136
  · exact m3029_160
  · exact m3029_192
  · exact m3029_260
  · exact m3029_264
  · exact m3029_288
  · exact m3029_320
  · exact m3029_384

theorem m3030_12 : Upper (D 10) (R 10) [34,65,144,384,12] 13 :=
  permutation_upper _ _ _ [6,65,192,48,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1515

theorem m3030_36 : Upper (D 10) (R 10) [34,65,144,384,36] 13 :=
  permutation_upper _ _ _ [34,65,40,132,320] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1942

theorem m3030_40 : Upper (D 10) (R 10) [34,65,144,384,40] 13 :=
  permutation_upper _ _ _ [34,65,40,384,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1962

theorem m3030_68 : Upper (D 10) (R 10) [34,65,144,384,68] 13 :=
  permutation_upper _ _ _ [34,65,72,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1968

theorem m3030_72 : Upper (D 10) (R 10) [34,65,144,384,72] 13 :=
  permutation_upper _ _ _ [34,65,72,384,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1975

theorem m3030_96 : Upper (D 10) (R 10) [34,65,144,384,96] 13 :=
  permutation_upper _ _ _ [34,65,96,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1980

theorem m3030_260 : Upper (D 10) (R 10) [34,65,144,384,260] 13 :=
  permutation_upper _ _ _ [34,65,136,260,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1993

theorem m3030_264 : Upper (D 10) (R 10) [34,65,144,384,264] 13 :=
  permutation_upper _ _ _ [34,65,136,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1996

theorem m3030_288 : Upper (D 10) (R 10) [34,65,144,384,288] 13 :=
  permutation_upper _ _ _ [34,65,136,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2001

theorem m3030_320 : Upper (D 10) (R 10) [34,65,144,384,320] 13 :=
  permutation_upper _ _ _ [34,65,136,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2004

def r3030 : Route 9 := (fun mask => (mask,id))

def c3030 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3030 : Upper (D 10) (R 10) [34,65,144,384] 13 := by
  apply FastRouting.sound _ _ [34,65,144,384] 13 (by decide) (choices 2) [12,36,40,68,72,96,260,264,288,320] r3030 c3030
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3030_12
  · exact m3030_36
  · exact m3030_40
  · exact m3030_68
  · exact m3030_72
  · exact m3030_96
  · exact m3030_260
  · exact m3030_264
  · exact m3030_288
  · exact m3030_320

def b3031 : PairBound 9 := { available := 348, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 35 67 164 168 348 380 348 476 348), lower := (rows 35 67 164 168 16 32 64 128 256), losses := [] }

theorem u3031 : Upper (D 10) (R 10) [34,65,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3031 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3032 : PairBound 9 := { available := 316, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 164 200 316 316 380 444 316), lower := (rows 35 67 164 200 16 32 64 128 256), losses := [] }

theorem u3032 : Upper (D 10) (R 10) [34,65,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3032 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3033_12 : Upper (D 10) (R 10) [34,65,160,288,12] 13 :=
  permutation_upper _ _ _ [6,96,160,48,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1749

theorem m3033_68 : Upper (D 10) (R 10) [34,65,160,288,68] 13 :=
  permutation_upper _ _ _ [34,65,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1973

theorem m3033_72 : Upper (D 10) (R 10) [34,65,160,288,72] 13 :=
  permutation_upper _ _ _ [34,65,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1973

theorem m3033_132 : Upper (D 10) (R 10) [34,65,160,288,132] 13 :=
  permutation_upper _ _ _ [34,65,136,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1988

theorem m3033_136 : Upper (D 10) (R 10) [34,65,160,288,136] 13 :=
  permutation_upper _ _ _ [34,65,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1997

theorem m3033_192 : Upper (D 10) (R 10) [34,65,160,288,192] 13 :=
  permutation_upper _ _ _ [34,65,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2006

theorem m3033_260 : Upper (D 10) (R 10) [34,65,160,288,260] 13 :=
  permutation_upper _ _ _ [34,65,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1997

theorem m3033_264 : Upper (D 10) (R 10) [34,65,160,288,264] 13 :=
  permutation_upper _ _ _ [34,65,136,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1988

theorem m3033_320 : Upper (D 10) (R 10) [34,65,160,288,320] 13 :=
  permutation_upper _ _ _ [34,65,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2006

def r3033 : Route 9 := (fun mask => (mask,id))

def c3033 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u3033 : Upper (D 10) (R 10) [34,65,160,288] 13 := by
  apply FastRouting.sound _ _ [34,65,160,288] 13 (by decide) (choices 2) [12,68,72,132,136,192,260,264,320,384] r3033 c3033
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3033_12
  · exact m3033_68
  · exact m3033_72
  · exact m3033_132
  · exact m3033_136
  · exact m3033_192
  · exact m3033_260
  · exact m3033_264
  · exact m3033_320
  · exact u2007

def b3034 : PairBound 9 := { available := 444, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 164 328 444 444 508 444 444), lower := (rows 35 67 164 328 16 32 64 128 256), losses := [] }

theorem u3034 : Upper (D 10) (R 10) [34,65,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3034 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3035_12 : Upper (D 10) (R 10) [34,65,160,384,12] 13 :=
  permutation_upper _ _ _ [6,96,192,48,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1783

theorem m3035_36 : Upper (D 10) (R 10) [34,65,160,384,36] 13 :=
  permutation_upper _ _ _ [34,65,40,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1954

theorem m3035_40 : Upper (D 10) (R 10) [34,65,160,384,40] 13 :=
  permutation_upper _ _ _ [34,65,40,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1963

theorem m3035_68 : Upper (D 10) (R 10) [34,65,160,384,68] 13 :=
  permutation_upper _ _ _ [34,65,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1974

theorem m3035_72 : Upper (D 10) (R 10) [34,65,160,384,72] 13 :=
  permutation_upper _ _ _ [34,65,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1976

theorem m3035_96 : Upper (D 10) (R 10) [34,65,160,384,96] 13 :=
  permutation_upper _ _ _ [34,65,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1983

theorem m3035_260 : Upper (D 10) (R 10) [34,65,160,384,260] 13 :=
  permutation_upper _ _ _ [34,65,136,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2001

theorem m3035_264 : Upper (D 10) (R 10) [34,65,160,384,264] 13 :=
  permutation_upper _ _ _ [34,65,136,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2005

theorem m3035_288 : Upper (D 10) (R 10) [34,65,160,384,288] 13 :=
  permutation_upper _ _ _ [34,65,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2007

theorem m3035_320 : Upper (D 10) (R 10) [34,65,160,384,320] 13 :=
  permutation_upper _ _ _ [34,65,160,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2008

def r3035 : Route 9 := (fun mask => (mask,id))

def c3035 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3035 : Upper (D 10) (R 10) [34,65,160,384] 13 := by
  apply FastRouting.sound _ _ [34,65,160,384] 13 (by decide) (choices 2) [12,36,40,68,72,96,260,264,288,320] r3035 c3035
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3035_12
  · exact m3035_36
  · exact m3035_40
  · exact m3035_68
  · exact m3035_72
  · exact m3035_96
  · exact m3035_260
  · exact m3035_264
  · exact m3035_288
  · exact m3035_320

def b3036 : PairBound 9 := { available := 316, camps := [{ cop := 2, region := 312, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 196 392 316 316 380 444 316), lower := (rows 35 67 196 392 16 32 64 128 256), losses := [] }

theorem u3036 : Upper (D 10) (R 10) [34,65,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3036 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3037 : PairBound 9 := { available := 124, camps := [{ cop := 2, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 35 67 388 392 124 124 124 252 380), lower := (rows 35 67 388 392 16 32 64 128 256), losses := [] }

theorem u3037 : Upper (D 10) (R 10) [34,65,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3037 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3038 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 73 432 432 496 432 432), lower := (rows 35 70 44 73 16 32 64 128 256), losses := [] }

theorem u3038 : Upper (D 10) (R 10) [34,68,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3038 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3039 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 88 433 417 481 417 417), lower := (rows 35 70 44 88 16 32 64 128 256), losses := [] }

theorem u3039 : Upper (D 10) (R 10) [34,68,40,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3039 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3040 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 44 104 401 433 465 401 401), lower := (rows 35 70 44 104 16 32 64 128 256), losses := [] }

theorem u3040 : Upper (D 10) (R 10) [34,68,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3040 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3041_160 : Upper (D 10) (R 10) [34,68,40,129,160] 13 :=
  permutation_upper _ _ _ [34,68,40,129,96] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2016

theorem m3041_384 : Upper (D 10) (R 10) [34,68,40,129,384] 13 :=
  permutation_upper _ _ _ [34,68,40,129,320] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2019

def r3041 : Route 9 := (fun mask => (mask,id))

def c3041 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3041 : Upper (D 10) (R 10) [34,68,40,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129] 13 (by decide) (choices 2) [96,160,192,288,320,384] r3041 c3041
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2016
  · exact m3041_160
  · exact u2017
  · exact u2018
  · exact u2019
  · exact m3041_384

theorem m3042_33 : Upper (D 10) (R 10) [34,68,40,144,33] 13 :=
  permutation_upper _ _ _ [34,36,72,48,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1880

def r3042 : Route 9 := (fun mask => (mask,id))

def c3042 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3042 : Upper (D 10) (R 10) [34,68,40,144] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r3042 c3042
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3042_33
  · exact u2020
  · exact u2021
  · exact u2022
  · exact u2023
  · exact u2024
  · exact u2025
  · exact u2026
  · exact u2027
  · exact u2028

def b3043 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 35 70 44 168 465 497 465 465 465), lower := (rows 35 70 44 168 16 32 64 128 256), losses := [] }

theorem u3043 : Upper (D 10) (R 10) [34,68,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3043 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3044 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 44 200 433 433 497 433 433), lower := (rows 35 70 44 200 16 32 64 128 256), losses := [] }

theorem u3044 : Upper (D 10) (R 10) [34,68,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3044 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3045_33 : Upper (D 10) (R 10) [34,68,40,384,33] 13 :=
  permutation_upper _ _ _ [34,36,72,48,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1881

def r3045 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3045 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3045 : Upper (D 10) (R 10) [34,68,40,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r3045 c3045
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3045_33
  · exact u2039
  · exact u2040
  · exact u2041
  · exact u2042
  · exact u2043
  · exact u2044

theorem m3046_9 : Upper (D 10) (R 10) [34,68,48,96,9] 13 :=
  permutation_upper _ _ _ [6,40,96,80,33] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1352

theorem m3046_129 : Upper (D 10) (R 10) [34,68,48,96,129] 13 :=
  permutation_upper _ _ _ [34,68,40,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2016

theorem m3046_136 : Upper (D 10) (R 10) [34,68,48,96,136] 13 :=
  permutation_upper _ _ _ [34,68,40,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2021

theorem m3046_384 : Upper (D 10) (R 10) [34,68,48,96,384] 13 :=
  permutation_upper _ _ _ [34,68,40,384,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2040

def r3046 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3046 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3046 : Upper (D 10) (R 10) [34,68,48,96] 13 := by
  apply FastRouting.sound _ _ [34,68,48,96] 13 (by decide) (choices 2) [9,129,136,384] r3046 c3046
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m3046_9
  · exact m3046_129
  · exact m3046_136
  · exact m3046_384

theorem m3047_40 : Upper (D 10) (R 10) [34,68,48,129,40] 13 :=
  permutation_upper _ _ _ [34,36,72,48,129] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1880

theorem m3047_72 : Upper (D 10) (R 10) [34,68,48,129,72] 13 :=
  permutation_upper _ _ _ [34,68,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2011

theorem m3047_96 : Upper (D 10) (R 10) [34,68,48,129,96] 13 :=
  permutation_upper _ _ _ [34,68,40,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2014

theorem m3047_136 : Upper (D 10) (R 10) [34,68,48,129,136] 13 :=
  permutation_upper _ _ _ [34,68,40,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2022

theorem m3047_160 : Upper (D 10) (R 10) [34,68,48,129,160] 13 :=
  permutation_upper _ _ _ [34,68,40,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2029

theorem m3047_192 : Upper (D 10) (R 10) [34,68,48,129,192] 13 :=
  permutation_upper _ _ _ [34,68,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2034

theorem m3047_264 : Upper (D 10) (R 10) [34,68,48,129,264] 13 :=
  permutation_upper _ _ _ [34,68,40,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2025

theorem m3047_288 : Upper (D 10) (R 10) [34,68,48,129,288] 13 :=
  permutation_upper _ _ _ [34,68,40,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2031

theorem m3047_320 : Upper (D 10) (R 10) [34,68,48,129,320] 13 :=
  permutation_upper _ _ _ [34,68,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2036

theorem m3047_384 : Upper (D 10) (R 10) [34,68,48,129,384] 13 :=
  permutation_upper _ _ _ [34,68,40,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2041

def r3047 : Route 9 := (fun mask => (mask,id))

def c3047 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3047 : Upper (D 10) (R 10) [34,68,48,129] 13 := by
  apply FastRouting.sound _ _ [34,68,48,129] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r3047 c3047
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3047_40
  · exact m3047_72
  · exact m3047_96
  · exact m3047_136
  · exact m3047_160
  · exact m3047_192
  · exact m3047_264
  · exact m3047_288
  · exact m3047_320
  · exact m3047_384

theorem m3048_9 : Upper (D 10) (R 10) [34,68,48,160,9] 13 :=
  permutation_upper _ _ _ [6,40,96,144,33] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1364

theorem m3048_65 : Upper (D 10) (R 10) [34,68,48,160,65] 13 :=
  permutation_upper _ _ _ [34,68,40,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2009

theorem m3048_72 : Upper (D 10) (R 10) [34,68,48,160,72] 13 :=
  permutation_upper _ _ _ [34,68,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2012

theorem m3048_129 : Upper (D 10) (R 10) [34,68,48,160,129] 13 :=
  permutation_upper _ _ _ [34,68,40,129,96] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2016

theorem m3048_136 : Upper (D 10) (R 10) [34,68,48,160,136] 13 :=
  permutation_upper _ _ _ [34,68,40,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2023

theorem m3048_192 : Upper (D 10) (R 10) [34,68,48,160,192] 13 :=
  permutation_upper _ _ _ [34,68,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2035

theorem m3048_257 : Upper (D 10) (R 10) [34,68,48,160,257] 13 :=
  permutation_upper _ _ _ [34,68,40,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2018

theorem m3048_264 : Upper (D 10) (R 10) [34,68,48,160,264] 13 :=
  permutation_upper _ _ _ [34,68,40,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2026

theorem m3048_320 : Upper (D 10) (R 10) [34,68,48,160,320] 13 :=
  permutation_upper _ _ _ [34,68,40,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2037

theorem m3048_384 : Upper (D 10) (R 10) [34,68,48,160,384] 13 :=
  permutation_upper _ _ _ [34,68,40,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2042

def r3048 : Route 9 := (fun mask => (mask,id))

def c3048 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u3048 : Upper (D 10) (R 10) [34,68,48,160] 13 := by
  apply FastRouting.sound _ _ [34,68,48,160] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r3048 c3048
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3048_9
  · exact m3048_65
  · exact m3048_72
  · exact m3048_129
  · exact m3048_136
  · exact m3048_192
  · exact m3048_257
  · exact m3048_264
  · exact m3048_320
  · exact m3048_384

theorem m3049_9 : Upper (D 10) (R 10) [34,68,48,192,9] 13 :=
  permutation_upper _ _ _ [6,40,192,80,33] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1403

theorem m3049_33 : Upper (D 10) (R 10) [34,68,48,192,33] 13 :=
  permutation_upper _ _ _ [34,36,40,65,192] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1859

theorem m3049_40 : Upper (D 10) (R 10) [34,68,48,192,40] 13 :=
  permutation_upper _ _ _ [34,36,192,48,65] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1912

theorem m3049_129 : Upper (D 10) (R 10) [34,68,48,192,129] 13 :=
  permutation_upper _ _ _ [34,68,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2017

theorem m3049_136 : Upper (D 10) (R 10) [34,68,48,192,136] 13 :=
  permutation_upper _ _ _ [34,68,40,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2024

theorem m3049_160 : Upper (D 10) (R 10) [34,68,48,192,160] 13 :=
  permutation_upper _ _ _ [34,68,40,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2030

theorem m3049_257 : Upper (D 10) (R 10) [34,68,48,192,257] 13 :=
  permutation_upper _ _ _ [34,68,40,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2019

theorem m3049_264 : Upper (D 10) (R 10) [34,68,48,192,264] 13 :=
  permutation_upper _ _ _ [34,68,40,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2027

theorem m3049_288 : Upper (D 10) (R 10) [34,68,48,192,288] 13 :=
  permutation_upper _ _ _ [34,68,40,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2032

theorem m3049_384 : Upper (D 10) (R 10) [34,68,48,192,384] 13 :=
  permutation_upper _ _ _ [34,68,40,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2043

def r3049 : Route 9 := (fun mask => (mask,id))

def c3049 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3049 : Upper (D 10) (R 10) [34,68,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,48,192] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r3049 c3049
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3049_9
  · exact m3049_33
  · exact m3049_40
  · exact m3049_129
  · exact m3049_136
  · exact m3049_160
  · exact m3049_257
  · exact m3049_264
  · exact m3049_288
  · exact m3049_384

theorem m3050_9 : Upper (D 10) (R 10) [34,68,48,384,9] 13 :=
  permutation_upper _ _ _ [6,40,192,272,33] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1421

theorem m3050_33 : Upper (D 10) (R 10) [34,68,48,384,33] 13 :=
  permutation_upper _ _ _ [34,36,40,65,384] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1860

theorem m3050_40 : Upper (D 10) (R 10) [34,68,48,384,40] 13 :=
  permutation_upper _ _ _ [34,36,192,48,257] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1913

theorem m3050_65 : Upper (D 10) (R 10) [34,68,48,384,65] 13 :=
  permutation_upper _ _ _ [34,68,40,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2010

theorem m3050_72 : Upper (D 10) (R 10) [34,68,48,384,72] 13 :=
  permutation_upper _ _ _ [34,68,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2013

theorem m3050_96 : Upper (D 10) (R 10) [34,68,48,384,96] 13 :=
  permutation_upper _ _ _ [34,68,40,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2015

theorem m3050_129 : Upper (D 10) (R 10) [34,68,48,384,129] 13 :=
  permutation_upper _ _ _ [34,68,40,129,320] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2019

theorem m3050_136 : Upper (D 10) (R 10) [34,68,48,384,136] 13 :=
  permutation_upper _ _ _ [34,68,40,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2028

theorem m3050_160 : Upper (D 10) (R 10) [34,68,48,384,160] 13 :=
  permutation_upper _ _ _ [34,68,40,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2033

theorem m3050_192 : Upper (D 10) (R 10) [34,68,48,384,192] 13 :=
  permutation_upper _ _ _ [34,68,40,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2038

theorem m3050_384 : Upper (D 10) (R 10) [34,68,48,384,384] 13 :=
  permutation_upper _ _ _ [34,68,40,384,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2044

def r3050 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3050 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3050 : Upper (D 10) (R 10) [34,68,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,48,384] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,384] r3050 c3050
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3050_9
  · exact m3050_33
  · exact m3050_40
  · exact m3050_65
  · exact m3050_72
  · exact m3050_96
  · exact m3050_129
  · exact m3050_136
  · exact m3050_160
  · exact m3050_192
  · exact m3050_384

def b3051 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 69 168 440 440 504 440 440), lower := (rows 35 70 69 168 16 32 64 128 256), losses := [] }

theorem u3051 : Upper (D 10) (R 10) [34,68,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3051 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3052 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 69 392 440 440 504 440 440), lower := (rows 35 70 69 392 16 32 64 128 256), losses := [] }

theorem u3052 : Upper (D 10) (R 10) [34,68,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3052 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3053 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 137 432 432 496 432 432), lower := (rows 35 70 76 137 16 32 64 128 256), losses := [] }

theorem u3053 : Upper (D 10) (R 10) [34,68,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3053 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3054 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 168 433 433 497 433 433), lower := (rows 35 70 76 168 16 32 64 128 256), losses := [] }

theorem u3054 : Upper (D 10) (R 10) [34,68,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3054 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3055 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 392 433 433 497 433 433), lower := (rows 35 70 76 392 16 32 64 128 256), losses := [] }

theorem u3055 : Upper (D 10) (R 10) [34,68,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3055 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3056 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 84 137 440 424 488 424 424), lower := (rows 35 70 84 137 16 32 64 128 256), losses := [] }

theorem u3056 : Upper (D 10) (R 10) [34,68,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3056 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3057 : PairBound 9 := { available := 425, camps := [{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 84 168 441 425 489 425 425), lower := (rows 35 70 84 168 16 32 64 128 256), losses := [] }

theorem u3057 : Upper (D 10) (R 10) [34,68,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3057 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3058 : PairBound 9 := { available := 425, camps := [{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 84 392 441 425 489 425 425), lower := (rows 35 70 84 392 16 32 64 128 256), losses := [] }

theorem u3058 : Upper (D 10) (R 10) [34,68,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3058 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3059 : PairBound 9 := { available := 440, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 100 137 440 440 504 440 440), lower := (rows 35 70 100 137 16 32 64 128 256), losses := [] }

theorem u3059 : Upper (D 10) (R 10) [34,68,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3059 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u3059
end Delivery.IrregularNine14.P10
