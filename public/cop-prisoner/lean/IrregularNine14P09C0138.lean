import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0097
import IrregularNine14P09C0098
import IrregularNine14P09C0099

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8280 : Route 9 := (fun mask => (mask,id))

def c8280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8280 : Upper (D 9) (R 9) [96,5,160,66,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,384] 13 (by decide) (choices 1) [1,8,16,256] r8280 c8280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5820
  · exact u5821
  · exact u5822
  · exact u5823

def r8281 : Route 9 := (fun mask => (mask,id))

def c8281 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8281 : Upper (D 9) (R 9) [96,5,160,80,129] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,129] 13 (by decide) (choices 1) [2,8,256] r8281 c8281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5824
  · exact u5825
  · exact u5826

def r8282 : Route 9 := (fun mask => (mask,id))

def c8282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8282 : Upper (D 9) (R 9) [96,5,160,80,130] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,130] 13 (by decide) (choices 1) [1,8,256] r8282 c8282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5827
  · exact u5828
  · exact u5829

def b8283 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 7 164 88 152 291 323 387 259), lower := (rows 97 7 164 88 152 32 64 128 256), losses := [] }

theorem u8283 : Upper (D 9) (R 9) [96,5,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8283 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8284 : Route 9 := (fun mask => (mask,id))

def c8284 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8284 : Upper (D 9) (R 9) [96,5,160,80,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,257] 13 (by decide) (choices 1) [2,8,128,256] r8284 c8284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5830
  · exact u5831
  · exact u5832
  · exact u5833

def r8285 : Route 9 := (fun mask => (mask,id))

def c8285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8285 : Upper (D 9) (R 9) [96,5,160,80,258] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,258] 13 (by decide) (choices 1) [1,8,128,256] r8285 c8285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5834
  · exact u5835
  · exact u5836
  · exact u5837

def r8286 : Route 9 := (fun mask => (mask,id))

def c8286 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8286 : Upper (D 9) (R 9) [96,5,160,80,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,264] 13 (by decide) (choices 1) [1,2,128,256] r8286 c8286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5838
  · exact u5839
  · exact u5840
  · exact u5841

def r8287 : Route 9 := (fun mask => (mask,id))

def c8287 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8287 : Upper (D 9) (R 9) [96,5,160,80,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,384] 13 (by decide) (choices 1) [1,2,8,256] r8287 c8287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5842
  · exact u5843
  · exact u5844
  · exact u5845

def r8288 : Route 9 := (fun mask => (mask,id))

def c8288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u8288 : Upper (D 9) (R 9) [96,5,160,129,258] 13 := by
  apply FastRouting.sound _ _ [96,5,160,129,258] 13 (by decide) (choices 1) [8,16,64,256] r8288 c8288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5846
  · exact u5847
  · exact u5848
  · exact u5849

def r8289 : Route 9 := (fun mask => (mask,id))

def c8289 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8289 : Upper (D 9) (R 9) [96,5,160,129,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,129,264] 13 (by decide) (choices 1) [2,16,64,256] r8289 c8289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5850
  · exact u5851
  · exact u5852
  · exact u5853

def r8290 : Route 9 := (fun mask => (mask,id))

def c8290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8290 : Upper (D 9) (R 9) [96,5,160,129,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,129,320] 13 (by decide) (choices 1) [2,8,16,256] r8290 c8290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5854
  · exact u5855
  · exact u5856
  · exact u5857

def r8291 : Route 9 := (fun mask => (mask,id))

def c8291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u8291 : Upper (D 9) (R 9) [96,5,160,130,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,130,257] 13 (by decide) (choices 1) [8,16,64,256] r8291 c8291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5858
  · exact u5859
  · exact u5860
  · exact u5861

def r8292 : Route 9 := (fun mask => (mask,id))

def c8292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8292 : Upper (D 9) (R 9) [96,5,160,130,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,130,264] 13 (by decide) (choices 1) [1,16,64,256] r8292 c8292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5862
  · exact u5863
  · exact u5864
  · exact u5865

def r8293 : Route 9 := (fun mask => (mask,id))

def c8293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8293 : Upper (D 9) (R 9) [96,5,160,130,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,130,320] 13 (by decide) (choices 1) [1,8,16,256] r8293 c8293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5866
  · exact u5867
  · exact u5868
  · exact u5869

def r8294 : Route 9 := (fun mask => (mask,id))

def c8294 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8294 : Upper (D 9) (R 9) [96,5,160,144,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,144,257] 13 (by decide) (choices 1) [2,8,64,256] r8294 c8294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5870
  · exact u5871
  · exact u5872
  · exact u5873

def r8295 : Route 9 := (fun mask => (mask,id))

def c8295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8295 : Upper (D 9) (R 9) [96,5,160,144,258] 13 := by
  apply FastRouting.sound _ _ [96,5,160,144,258] 13 (by decide) (choices 1) [1,8,64,256] r8295 c8295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5874
  · exact u5875
  · exact u5876
  · exact u5877

def r8296 : Route 9 := (fun mask => (mask,id))

def c8296 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8296 : Upper (D 9) (R 9) [96,5,160,144,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,144,264] 13 (by decide) (choices 1) [1,2,64,256] r8296 c8296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5878
  · exact u5879
  · exact u5880
  · exact u5881

def r8297 : Route 9 := (fun mask => (mask,id))

def c8297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8297 : Upper (D 9) (R 9) [96,5,160,144,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,144,320] 13 (by decide) (choices 1) [1,2,8,256] r8297 c8297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5882
  · exact u5883
  · exact u5884
  · exact u5885

def r8298 : Route 9 := (fun mask => (mask,id))

def c8298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8298 : Upper (D 9) (R 9) [96,5,160,192,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192,257] 13 (by decide) (choices 1) [2,8,16,256] r8298 c8298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5886
  · exact u5887
  · exact u5888
  · exact u5889

def r8299 : Route 9 := (fun mask => (mask,id))

def c8299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8299 : Upper (D 9) (R 9) [96,5,160,192,258] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192,258] 13 (by decide) (choices 1) [1,8,16,256] r8299 c8299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5890
  · exact u5891
  · exact u5892
  · exact u5893

def r8300 : Route 9 := (fun mask => (mask,id))

def c8300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8300 : Upper (D 9) (R 9) [96,5,160,192,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192,264] 13 (by decide) (choices 1) [1,2,16,256] r8300 c8300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5894
  · exact u5895
  · exact u5896
  · exact u5897

def r8301 : Route 9 := (fun mask => (mask,id))

def c8301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u8301 : Upper (D 9) (R 9) [96,5,160,257,258] 13 := by
  apply FastRouting.sound _ _ [96,5,160,257,258] 13 (by decide) (choices 1) [8,16,64,128] r8301 c8301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5898
  · exact u5899
  · exact u5900
  · exact u5901

def b8302 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 16, targets := 225 },{ cop := 4, region := 231, targets := 256 }], pairs := [(0,8),(4,0),(4,5),(4,6),(4,7)], upper := (rows 97 7 164 265 280 242 210 210 466), lower := (rows 97 7 164 265 280 32 64 128 256), losses := [] }

theorem u8302 : Upper (D 9) (R 9) [96,5,160,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8302 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8303 : Route 9 := (fun mask => (mask,id))

def c8303 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8303 : Upper (D 9) (R 9) [96,5,160,257,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,257,320] 13 (by decide) (choices 1) [2,8,16,128] r8303 c8303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5902
  · exact u5903
  · exact u5904
  · exact u5905

def r8304 : Route 9 := (fun mask => (mask,id))

def c8304 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8304 : Upper (D 9) (R 9) [96,5,160,257,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,257,384] 13 (by decide) (choices 1) [2,8,16,64] r8304 c8304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5906
  · exact u5907
  · exact u5908
  · exact u5909

def b8305 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 225 },{ cop := 4, region := 225, targets := 256 }], pairs := [(0,8),(4,0),(4,5),(4,6),(4,7)], upper := (rows 97 7 164 266 280 241 209 209 465), lower := (rows 97 7 164 266 280 32 64 128 256), losses := [] }

theorem u8305 : Upper (D 9) (R 9) [96,5,160,258,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8305 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8306 : Route 9 := (fun mask => (mask,id))

def c8306 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8306 : Upper (D 9) (R 9) [96,5,160,258,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,258,320] 13 (by decide) (choices 1) [1,8,16,128] r8306 c8306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5910
  · exact u5911
  · exact u5912
  · exact u5913

def r8307 : Route 9 := (fun mask => (mask,id))

def c8307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8307 : Upper (D 9) (R 9) [96,5,160,258,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,258,384] 13 (by decide) (choices 1) [1,8,16,64] r8307 c8307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5914
  · exact u5915
  · exact u5916
  · exact u5917

def b8308 : PairBound 9 := { available := 195, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 97 7 164 280 280 227 195 195 451), lower := (rows 97 7 164 280 280 32 64 128 256), losses := [] }

theorem u8308 : Upper (D 9) (R 9) [96,5,160,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8308 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8309 : PairBound 9 := { available := 139, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 7 164 280 336 171 203 139 395), lower := (rows 97 7 164 280 336 32 64 128 256), losses := [] }

theorem u8309 : Upper (D 9) (R 9) [96,5,160,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8309 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8310 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 7 164 280 400 107 75 203 331), lower := (rows 97 7 164 280 400 32 64 128 256), losses := [] }

theorem u8310 : Upper (D 9) (R 9) [96,5,160,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8310 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8311 : Route 9 := (fun mask => (mask,id))

def c8311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8311 : Upper (D 9) (R 9) [96,5,160,320,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,320,384] 13 (by decide) (choices 1) [1,2,8,16] r8311 c8311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5918
  · exact u5919
  · exact u5920
  · exact u5921

def b8312 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,6)], upper := (rows 97 7 388 25 400 106 106 234 362), lower := (rows 97 7 388 25 400 32 64 128 256), losses := [] }

theorem u8312 : Upper (D 9) (R 9) [96,5,384,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8312 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8313 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 97 7 388 26 49 488 456 456 456), lower := (rows 97 7 388 26 49 32 64 128 256), losses := [] }

theorem u8313 : Upper (D 9) (R 9) [96,5,384,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8313 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8314 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8314 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8314 : Upper (D 9) (R 9) [96,5,384,18,40] 13 := by
  apply FastRouting.sound _ _ [96,5,384,18,40] 13 (by decide) (choices 1) [1,64,128] r8314 c8314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5922
  · exact u5923
  · exact u5924

def b8315 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 7 388 26 112 425 457 393 393), lower := (rows 97 7 388 26 112 32 64 128 256), losses := [] }

theorem u8315 : Upper (D 9) (R 9) [96,5,384,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8315 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8316 : Route 9 := (fun mask => (mask,id))

def c8316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8316 : Upper (D 9) (R 9) [96,5,384,18,129] 13 := by
  apply FastRouting.sound _ _ [96,5,384,18,129] 13 (by decide) (choices 1) [8,64,256] r8316 c8316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5925
  · exact u5926
  · exact u5927

def r8317 : Route 9 := (fun mask => (mask,id))

def c8317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8317 : Upper (D 9) (R 9) [96,5,384,18,136] 13 := by
  apply FastRouting.sound _ _ [96,5,384,18,136] 13 (by decide) (choices 1) [1,64,256] r8317 c8317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5928
  · exact u5929
  · exact u5930

def r8318 : Route 9 := (fun mask => (mask,id))

def c8318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8318 : Upper (D 9) (R 9) [96,5,384,18,160] 13 := by
  apply FastRouting.sound _ _ [96,5,384,18,160] 13 (by decide) (choices 1) [1,8,64,256] r8318 c8318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5931
  · exact u5932
  · exact u5933
  · exact u5934

def b8319 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,6)], upper := (rows 97 7 388 26 400 105 105 233 361), lower := (rows 97 7 388 26 400 32 64 128 256), losses := [] }

theorem u8319 : Upper (D 9) (R 9) [96,5,384,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8319 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8320 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 388 41 82 440 472 408 408), lower := (rows 97 7 388 41 82 32 64 128 256), losses := [] }

theorem u8320 : Upper (D 9) (R 9) [96,5,384,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8320 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8321 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 24, targets := 384 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,7),(3,8),(4,7),(4,8)], upper := (rows 97 7 388 41 88 434 466 402 402), lower := (rows 97 7 388 41 88 32 64 128 256), losses := [] }

theorem u8321 : Upper (D 9) (R 9) [96,5,384,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8321 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8322 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 388 41 146 376 344 472 344), lower := (rows 97 7 388 41 146 32 64 128 256), losses := [] }

theorem u8322 : Upper (D 9) (R 9) [96,5,384,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8322 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8323 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 388 41 152 370 338 466 338), lower := (rows 97 7 388 41 152 32 64 128 256), losses := [] }

theorem u8323 : Upper (D 9) (R 9) [96,5,384,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8323 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8324 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 388 41 208 314 346 410 282), lower := (rows 97 7 388 41 208 32 64 128 256), losses := [] }

theorem u8324 : Upper (D 9) (R 9) [96,5,384,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8324 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8325 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8325 : Upper (D 9) (R 9) [96,5,384,34,72] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,72] 13 (by decide) (choices 1) [1,16,128] r8325 c8325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5935
  · exact u5936
  · exact u5937

def r8326 : Route 9 := (fun mask => (mask,id))

def c8326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u8326 : Upper (D 9) (R 9) [96,5,384,34,129] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,129] 13 (by decide) (choices 1) [8,16,64,256] r8326 c8326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5938
  · exact u5939
  · exact u5940
  · exact u5941

def r8327 : Route 9 := (fun mask => (mask,id))

def c8327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8327 : Upper (D 9) (R 9) [96,5,384,34,136] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,136] 13 (by decide) (choices 1) [1,16,64,256] r8327 c8327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5942
  · exact u5943
  · exact u5944
  · exact u5945

def r8328 : Route 9 := (fun mask => (mask,id))

def c8328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8328 : Upper (D 9) (R 9) [96,5,384,34,192] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,192] 13 (by decide) (choices 1) [1,8,16,256] r8328 c8328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5946
  · exact u5947
  · exact u5948
  · exact u5949

def b8329 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,6)], upper := (rows 97 7 388 42 400 121 89 217 345), lower := (rows 97 7 388 42 400 32 64 128 256), losses := [] }

theorem u8329 : Upper (D 9) (R 9) [96,5,384,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8329 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8330 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 24, targets := 384 },{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(3,7),(3,8),(4,7),(4,8)], upper := (rows 97 7 388 56 88 419 451 387 387), lower := (rows 97 7 388 56 88 32 64 128 256), losses := [] }

theorem u8330 : Upper (D 9) (R 9) [96,5,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8330 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8331 : Route 9 := (fun mask => (mask,id))

def c8331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8331 : Upper (D 9) (R 9) [96,5,384,48,129] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,129] 13 (by decide) (choices 1) [2,8,64,256] r8331 c8331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5950
  · exact u5951
  · exact u5952
  · exact u5953

def r8332 : Route 9 := (fun mask => (mask,id))

def c8332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8332 : Upper (D 9) (R 9) [96,5,384,48,130] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,130] 13 (by decide) (choices 1) [1,8,64,256] r8332 c8332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5954
  · exact u5955
  · exact u5956
  · exact u5957

def r8333 : Route 9 := (fun mask => (mask,id))

def c8333 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8333 : Upper (D 9) (R 9) [96,5,384,48,136] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,136] 13 (by decide) (choices 1) [1,2,64,256] r8333 c8333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5958
  · exact u5959
  · exact u5960
  · exact u5961

def r8334 : Route 9 := (fun mask => (mask,id))

def c8334 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8334 : Upper (D 9) (R 9) [96,5,384,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,192] 13 (by decide) (choices 1) [1,2,8,256] r8334 c8334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5962
  · exact u5963
  · exact u5964
  · exact u5965

def b8335 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,6)], upper := (rows 97 7 388 56 400 107 75 203 331), lower := (rows 97 7 388 56 400 32 64 128 256), losses := [] }

theorem u8335 : Upper (D 9) (R 9) [96,5,384,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8335 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8336 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 388 104 145 314 346 410 282), lower := (rows 97 7 388 104 145 32 64 128 256), losses := [] }

theorem u8336 : Upper (D 9) (R 9) [96,5,384,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8336 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8337 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 388 104 146 313 345 409 281), lower := (rows 97 7 388 104 146 32 64 128 256), losses := [] }

theorem u8337 : Upper (D 9) (R 9) [96,5,384,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8337 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8338 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 388 104 152 307 339 403 275), lower := (rows 97 7 388 104 152 32 64 128 256), losses := [] }

theorem u8338 : Upper (D 9) (R 9) [96,5,384,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8338 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8339 : Route 9 := (fun mask => (mask,id))

def c8339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8339 : Upper (D 9) (R 9) [96,5,384,129,258] 13 := by
  apply FastRouting.sound _ _ [96,5,384,129,258] 13 (by decide) (choices 1) [8,16,64] r8339 c8339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5966
  · exact u5967
  · exact u5968

#print axioms u8339
end Delivery.IrregularNine14.P09
