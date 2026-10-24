import SmallBudgetTenFinite9Common

namespace Delivery.SmallBudgetTenFinite9
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile3_node3_cert : CutBound 9 := { lost := (rows 64 0 0 65 0 0 0 0 0), upper := (rows 49 67 69 392 400 416 64 128 256), lower := (rows 49 67 69 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 511 511 511 511 511 511), good := (rows 504 506 508 504 504 504 504 504 504) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile3_node3 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65,65] 6 384 profile3_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65,65] 6 384 profile3_node3_cert).mp (by decide +kernel))

def profile3_node4_cert : CutBound 9 := { lost := (rows 0 128 64 1 0 0 0 0 0), upper := (rows 49 67 133 456 464 480 64 128 256), lower := (rows 49 67 133 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 511 511 511 511 511 511), good := (rows 504 506 508 504 504 504 504 504 504) },{ target := 6, region := (rows 1 2 7 8 16 32 0 511 511), good := (rows 437 391 389 392 400 416 384 384 384) },{ target := 7, region := (rows 1 7 4 8 16 32 511 0 511), good := (rows 371 323 327 328 336 352 320 320 320) }] }

theorem profile3_node4 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65,129] 6 448 profile3_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65,129] 6 448 profile3_node4_cert).mp (by decide +kernel))

def profile3_node5_cert : CutBound 9 := { lost := (rows 64 0 1 64 0 0 0 0 0), upper := (rows 49 67 196 393 401 417 64 128 256), lower := (rows 49 67 196 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 511 8 16 32 511 511 511), good := (rows 500 454 452 460 468 484 452 452 452) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile3_node5 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65,192] 6 385 profile3_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65,192] 6 385 profile3_node5_cert).mp (by decide +kernel))

def profile3_node6_cert : CutBound 9 := { lost := (rows 0 128 65 0 0 0 0 0 0), upper := (rows 49 67 388 457 465 481 64 128 256), lower := (rows 49 67 388 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 511 8 16 32 511 511 511), good := (rows 500 454 452 460 468 484 452 452 452) },{ target := 6, region := (rows 1 2 511 8 16 32 0 511 511), good := (rows 437 391 388 396 404 420 388 388 388) },{ target := 7, region := (rows 1 3 4 8 16 32 511 0 511), good := (rows 371 323 324 328 336 352 320 320 320) }] }

theorem profile3_node6 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65,384] 6 449 profile3_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65,384] 6 449 profile3_node6_cert).mp (by decide +kernel))

def profile3_node2_column : Nat → Fin 9 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile3_node2_route : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile3_node2 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,65] 6 (by decide) (choices 2) [65,129,192,384] profile3_node2_route profile3_node2_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node3
  · exact profile3_node4
  · exact profile3_node5
  · exact profile3_node6

def profile3_node8_cert : CutBound 9 := { lost := (rows 64 1 0 64 0 0 0 0 0), upper := (rows 49 194 69 393 401 417 64 128 256), lower := (rows 49 194 69 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 4 8 16 32 511 511 511), good := (rows 498 450 454 458 466 482 450 450 450) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile3_node8 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192,65] 6 385 profile3_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192,65] 6 385 profile3_node8_cert).mp (by decide +kernel))

def profile3_node9_cert : CutBound 9 := { lost := (rows 64 1 1 64 0 0 0 0 0), upper := (rows 49 194 196 265 273 289 64 128 256), lower := (rows 49 194 196 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 511 8 16 32 511 511 511), good := (rows 502 454 454 462 470 486 454 454 454) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile3_node9 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192,192] 6 257 profile3_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192,192] 6 257 profile3_node9_cert).mp (by decide +kernel))

def profile3_node10_cert : CutBound 9 := { lost := (rows 0 1 192 0 0 0 0 0 0), upper := (rows 49 194 261 457 465 481 64 128 256), lower := (rows 49 194 261 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 4 8 16 32 511 511 511), good := (rows 498 450 454 458 466 482 450 450 450) },{ target := 6, region := (rows 1 2 5 8 16 32 0 511 511), good := (rows 437 386 389 392 400 416 384 384 384) },{ target := 7, region := (rows 1 2 5 8 16 32 511 0 511), good := (rows 373 322 325 328 336 352 320 320 320) }] }

theorem profile3_node10 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192,257] 6 449 profile3_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192,257] 6 449 profile3_node10_cert).mp (by decide +kernel))

def profile3_node11_cert : CutBound 9 := { lost := (rows 64 1 1 64 0 0 0 0 0), upper := (rows 49 194 324 393 401 417 64 128 256), lower := (rows 49 194 324 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 511 8 16 32 511 511 511), good := (rows 502 454 454 462 470 486 454 454 454) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile3_node11 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192,320] 6 385 profile3_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192,320] 6 385 profile3_node11_cert).mp (by decide +kernel))

def profile3_node7_column : Nat → Fin 9 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile3_node7_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile3_node7 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48,192] 6 (by decide) (choices 2) [65,192,257,320] profile3_node7_route profile3_node7_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node8
  · exact profile3_node9
  · exact profile3_node10
  · exact profile3_node11

def profile3_node1_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile3_node1_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile3_node1 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [48] 6 (by decide) (choices 2) [65,192] profile3_node1_route profile3_node1_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node2
  · exact profile3_node7

def profile3_node14_cert : CutBound 9 := { lost := (rows 0 64 0 65 0 0 0 0 0), upper := (rows 81 35 69 392 400 416 64 128 256), lower := (rows 81 35 69 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 511 511 511 511 511 511), good := (rows 504 506 508 504 504 504 504 504 504) },{ target := 6, region := (rows 1 7 4 511 511 511 0 511 511), good := (rows 443 443 447 440 440 440 440 440 440) }] }

theorem profile3_node14 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33,65] 6 384 profile3_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33,65] 6 384 profile3_node14_cert).mp (by decide +kernel))

def profile3_node15_cert : CutBound 9 := { lost := (rows 128 0 64 1 0 0 0 0 0), upper := (rows 81 35 133 456 464 480 64 128 256), lower := (rows 81 35 133 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 511 511 511 511 511 511), good := (rows 504 506 508 504 504 504 504 504 504) },{ target := 6, region := (rows 1 2 7 8 16 32 0 511 511), good := (rows 405 423 389 392 400 416 384 384 384) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 355 325 328 337 352 320 320 320) }] }

theorem profile3_node15 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33,129] 6 448 profile3_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33,129] 6 448 profile3_node15_cert).mp (by decide +kernel))

def profile3_node16_cert : CutBound 9 := { lost := (rows 0 64 1 64 0 0 0 0 0), upper := (rows 81 35 196 393 401 417 64 128 256), lower := (rows 81 35 196 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 511 8 16 32 511 511 511), good := (rows 468 486 452 460 468 484 452 452 452) },{ target := 6, region := (rows 1 3 4 11 19 35 0 511 511), good := (rows 443 443 388 392 400 416 384 384 384) }] }

theorem profile3_node16 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33,192] 6 385 profile3_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33,192] 6 385 profile3_node16_cert).mp (by decide +kernel))

def profile3_node17_cert : CutBound 9 := { lost := (rows 128 0 65 0 0 0 0 0 0), upper := (rows 81 35 388 457 465 481 64 128 256), lower := (rows 81 35 388 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 511 8 16 32 511 511 511), good := (rows 468 486 452 460 468 484 452 452 452) },{ target := 6, region := (rows 1 2 511 8 16 32 0 511 511), good := (rows 405 423 388 396 404 420 388 388 388) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 355 324 328 337 352 320 320 320) }] }

theorem profile3_node17 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33,384] 6 449 profile3_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33,384] 6 449 profile3_node17_cert).mp (by decide +kernel))

def profile3_node13_column : Nat → Fin 9 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile3_node13_route : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile3_node13 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,33] 6 (by decide) (choices 2) [65,129,192,384] profile3_node13_route profile3_node13_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node14
  · exact profile3_node15
  · exact profile3_node16
  · exact profile3_node17

def profile3_node18_cert : CutBound 9 := { lost := (rows 128 128 64 64 0 0 0 0 0), upper := (rows 81 67 421 425 433 417 64 128 256), lower := (rows 81 67 4 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 7 11 19 35 0 511 511), good := (rows 445 447 388 392 400 416 384 384 384) },{ target := 7, region := (rows 17 19 4 8 16 32 511 0 511), good := (rows 339 323 324 328 339 352 320 320 320) }] }

theorem profile3_node18 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,65] 6 417 profile3_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,65] 6 417 profile3_node18_cert).mp (by decide +kernel))

def profile3_node19_cert : CutBound 9 := { lost := (rows 0 1 64 64 0 0 0 0 0), upper := (rows 81 98 389 393 401 417 64 128 256), lower := (rows 81 98 4 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 511 511 511), good := (rows 464 482 452 456 464 482 448 448 448) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 418 388 392 400 416 384 384 384) }] }

theorem profile3_node19 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,96] 6 385 profile3_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,96] 6 385 profile3_node19_cert).mp (by decide +kernel))

def profile3_node20_cert : CutBound 9 := { lost := (rows 384 320 0 0 0 0 0 0 0), upper := (rows 81 131 485 489 497 481 64 128 256), lower := (rows 81 131 4 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 16 32 0 511 511), good := (rows 403 387 388 392 400 416 384 384 384) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 323 324 328 337 352 320 320 320) },{ target := 8, region := (rows 17 19 4 8 16 32 511 511 0), good := (rows 211 195 196 200 211 224 192 192 192) }] }

theorem profile3_node20 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,129] 6 481 profile3_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,129] 6 481 profile3_node20_cert).mp (by decide +kernel))

def profile3_node21_cert : CutBound 9 := { lost := (rows 128 65 0 0 0 0 0 0 0), upper := (rows 81 162 453 457 465 481 64 128 256), lower := (rows 81 162 4 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 511 511 511), good := (rows 464 482 452 456 464 482 448 448 448) },{ target := 6, region := (rows 1 34 4 8 16 32 0 511 511), good := (rows 401 418 388 392 400 418 384 384 384) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 354 324 328 337 352 320 320 320) }] }

theorem profile3_node21 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,160] 6 449 profile3_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,160] 6 449 profile3_node21_cert).mp (by decide +kernel))

def profile3_node22_cert : CutBound 9 := { lost := (rows 0 1 64 64 0 0 0 0 0), upper := (rows 81 194 421 425 433 417 64 128 256), lower := (rows 81 194 4 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 4 8 16 32 511 511 511), good := (rows 466 450 454 458 466 482 450 450 450) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 386 388 392 400 416 384 384 384) }] }

theorem profile3_node22 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,192] 6 417 profile3_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,192] 6 417 profile3_node22_cert).mp (by decide +kernel))

def profile3_node23_cert : CutBound 9 := { lost := (rows 128 65 0 0 0 0 0 0 0), upper := (rows 81 386 485 489 497 481 64 128 256), lower := (rows 81 386 4 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 4 8 16 32 511 511 511), good := (rows 466 450 454 458 466 482 450 450 450) },{ target := 6, region := (rows 1 511 4 8 16 32 0 511 511), good := (rows 403 386 390 394 402 418 386 386 386) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 322 324 328 337 352 320 320 320) }] }

theorem profile3_node23 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,384] 6 481 profile3_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80,384] 6 481 profile3_node23_cert).mp (by decide +kernel))

def profile3_node12_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile3_node12_route : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile3_node12 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [80] 6 (by decide) (choices 2) [33,65,96,129,160,192,384] profile3_node12_route profile3_node12_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node13
  · exact profile3_node18
  · exact profile3_node19
  · exact profile3_node20
  · exact profile3_node21
  · exact profile3_node22
  · exact profile3_node23

def profile3_node26_cert : CutBound 9 := { lost := (rows 256 256 256 1 0 0 0 0 0), upper := (rows 193 19 37 456 464 480 64 128 256), lower := (rows 193 19 37 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 511 511 511 511 511 511), good := (rows 504 506 508 504 504 504 504 504 504) },{ target := 8, region := (rows 511 18 36 8 16 32 511 511 0), good := (rows 193 211 229 201 211 229 193 193 193) }] }

theorem profile3_node26 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,33] 6 448 profile3_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,33] 6 448 profile3_node26_cert).mp (by decide +kernel))

def profile3_node27_cert : CutBound 9 := { lost := (rows 0 64 0 65 0 0 0 0 0), upper := (rows 193 19 69 424 432 416 64 128 256), lower := (rows 193 19 69 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 511 511 511 511 511 511), good := (rows 504 506 508 504 504 504 504 504 504) },{ target := 6, region := (rows 1 7 4 511 511 511 0 511 511), good := (rows 443 443 447 440 440 440 440 440 440) }] }

theorem profile3_node27 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,65] 6 416 profile3_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,65] 6 416 profile3_node27_cert).mp (by decide +kernel))

def profile3_node28_cert : CutBound 9 := { lost := (rows 0 64 1 64 0 0 0 0 0), upper := (rows 193 19 100 393 401 417 64 128 256), lower := (rows 193 19 100 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 511 511 511), good := (rows 448 466 484 456 464 484 448 448 448) },{ target := 6, region := (rows 1 3 4 11 19 35 0 511 511), good := (rows 443 443 420 392 400 416 384 384 384) }] }

theorem profile3_node28 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,96] 6 385 profile3_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,96] 6 385 profile3_node28_cert).mp (by decide +kernel))

def profile3_node29_cert : CutBound 9 := { lost := (rows 0 64 1 64 0 0 0 0 0), upper := (rows 193 19 196 297 305 289 64 128 256), lower := (rows 193 19 196 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 511 8 16 32 511 511 511), good := (rows 452 470 452 460 468 484 452 452 452) },{ target := 6, region := (rows 1 3 4 11 19 35 0 511 511), good := (rows 443 443 388 392 400 416 384 384 384) }] }

theorem profile3_node29 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,192] 6 289 profile3_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,192] 6 289 profile3_node29_cert).mp (by decide +kernel))

def profile3_node30_cert : CutBound 9 := { lost := (rows 0 0 192 1 0 0 0 0 0), upper := (rows 193 19 261 488 496 480 64 128 256), lower := (rows 193 19 261 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 511 511 511 511 511 511), good := (rows 504 506 508 504 504 504 504 504 504) },{ target := 6, region := (rows 1 2 7 8 16 32 0 511 511), good := (rows 389 407 389 392 400 416 384 384 384) },{ target := 7, region := (rows 1 2 7 8 16 32 511 0 511), good := (rows 325 343 325 328 336 352 320 320 320) }] }

theorem profile3_node30 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,257] 6 480 profile3_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,257] 6 480 profile3_node30_cert).mp (by decide +kernel))

def profile3_node31_cert : CutBound 9 := { lost := (rows 0 0 193 0 0 0 0 0 0), upper := (rows 193 19 292 457 465 481 64 128 256), lower := (rows 193 19 292 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 511 511 511), good := (rows 448 466 484 456 464 484 448 448 448) },{ target := 6, region := (rows 1 2 36 8 16 32 0 511 511), good := (rows 385 403 420 392 400 420 384 384 384) },{ target := 7, region := (rows 1 2 36 8 16 32 511 0 511), good := (rows 321 339 356 328 336 356 320 320 320) }] }

theorem profile3_node31 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,288] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,288] 6 449 profile3_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,288] 6 449 profile3_node31_cert).mp (by decide +kernel))

def profile3_node32_cert : CutBound 9 := { lost := (rows 0 64 1 64 0 0 0 0 0), upper := (rows 193 19 324 425 433 417 64 128 256), lower := (rows 193 19 324 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 511 8 16 32 511 511 511), good := (rows 452 470 452 460 468 484 452 452 452) },{ target := 6, region := (rows 1 3 4 11 19 35 0 511 511), good := (rows 443 443 388 392 400 416 384 384 384) }] }

theorem profile3_node32 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,320] 6 417 profile3_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17,320] 6 417 profile3_node32_cert).mp (by decide +kernel))

def profile3_node25_column : Nat → Fin 9 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile3_node25_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile3_node25 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,17] 6 (by decide) (choices 2) [33,65,96,192,257,288,320] profile3_node25_route profile3_node25_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node26
  · exact profile3_node27
  · exact profile3_node28
  · exact profile3_node29
  · exact profile3_node30
  · exact profile3_node31
  · exact profile3_node32

def profile3_node34_cert : CutBound 9 := { lost := (rows 0 64 128 64 0 0 0 0 0), upper := (rows 193 50 69 393 401 417 64 128 256), lower := (rows 193 50 69 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 7 4 13 21 37 0 511 511), good := (rows 443 434 447 392 400 416 384 384 384) },{ target := 7, region := (rows 1 2 5 8 16 32 511 0 511), good := (rows 325 370 325 328 336 352 320 320 320) }] }

theorem profile3_node34 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48,65] 6 385 profile3_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48,65] 6 385 profile3_node34_cert).mp (by decide +kernel))

def profile3_node35_cert : CutBound 9 := { lost := (rows 0 64 1 64 0 0 0 0 0), upper := (rows 193 50 196 265 273 289 64 128 256), lower := (rows 193 50 196 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 511 8 16 32 511 511 511), good := (rows 452 502 452 460 468 484 452 452 452) },{ target := 6, region := (rows 1 3 4 9 17 33 0 511 511), good := (rows 443 434 388 392 400 416 384 384 384) }] }

theorem profile3_node35 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48,192] 6 257 profile3_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48,192] 6 257 profile3_node35_cert).mp (by decide +kernel))

def profile3_node36_cert : CutBound 9 := { lost := (rows 256 0 192 0 0 0 0 0 0), upper := (rows 193 50 261 457 465 481 64 128 256), lower := (rows 193 50 261 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 8 16 32 0 511 511), good := (rows 389 434 389 392 400 416 384 384 384) },{ target := 7, region := (rows 1 2 5 8 16 32 511 0 511), good := (rows 325 370 325 328 336 352 320 320 320) },{ target := 8, region := (rows 511 2 4 8 16 32 511 511 0), good := (rows 193 243 197 201 209 225 193 193 193) }] }

theorem profile3_node36 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48,257] 6 449 profile3_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48,257] 6 449 profile3_node36_cert).mp (by decide +kernel))

def profile3_node37_cert : CutBound 9 := { lost := (rows 0 64 1 64 0 0 0 0 0), upper := (rows 193 50 324 393 401 417 64 128 256), lower := (rows 193 50 324 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 511 8 16 32 511 511 511), good := (rows 452 502 452 460 468 484 452 452 452) },{ target := 6, region := (rows 1 3 4 9 17 33 0 511 511), good := (rows 443 434 388 392 400 416 384 384 384) }] }

theorem profile3_node37 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48,320] 6 385 profile3_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48,320] 6 385 profile3_node37_cert).mp (by decide +kernel))

def profile3_node33_column : Nat → Fin 9 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile3_node33_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile3_node33 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,48] 6 (by decide) (choices 2) [65,192,257,320] profile3_node33_route profile3_node33_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node34
  · exact profile3_node35
  · exact profile3_node36
  · exact profile3_node37

def profile3_node38_cert : CutBound 9 := { lost := (rows 0 128 64 64 0 0 0 0 0), upper := (rows 193 67 437 441 433 433 64 128 256), lower := (rows 193 67 4 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 7 11 19 35 0 511 511), good := (rows 445 447 388 392 400 416 384 384 384) },{ target := 7, region := (rows 1 3 4 8 16 32 511 0 511), good := (rows 323 323 324 328 336 352 320 320 320) }] }

theorem profile3_node38 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,65] 6 433 profile3_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,65] 6 433 profile3_node38_cert).mp (by decide +kernel))

def profile3_node39_cert : CutBound 9 := { lost := (rows 0 1 64 64 0 0 0 0 0), upper := (rows 193 82 421 425 433 417 64 128 256), lower := (rows 193 82 4 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 511 511 511), good := (rows 448 466 452 456 466 480 448 448 448) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 402 388 392 400 416 384 384 384) }] }

theorem profile3_node39 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,80] 6 417 profile3_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,80] 6 417 profile3_node39_cert).mp (by decide +kernel))

def profile3_node40_cert : CutBound 9 := { lost := (rows 0 1 64 64 0 0 0 0 0), upper := (rows 193 194 309 313 305 305 64 128 256), lower := (rows 193 194 4 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 4 8 16 32 511 511 511), good := (rows 450 450 454 458 466 482 450 450 450) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 386 388 392 400 416 384 384 384) }] }

theorem profile3_node40 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,192] 6 305 profile3_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,192] 6 305 profile3_node40_cert).mp (by decide +kernel))

def profile3_node41_cert : CutBound 9 := { lost := (rows 256 192 0 0 0 0 0 0 0), upper := (rows 193 259 501 505 497 497 64 128 256), lower := (rows 193 259 4 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 16 32 0 511 511), good := (rows 387 387 388 392 400 416 384 384 384) },{ target := 7, region := (rows 1 3 4 8 16 32 511 0 511), good := (rows 323 323 324 328 336 352 320 320 320) },{ target := 8, region := (rows 511 2 4 8 16 32 511 511 0), good := (rows 193 195 197 201 209 225 193 193 193) }] }

theorem profile3_node41 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,257] 6 497 profile3_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,257] 6 497 profile3_node41_cert).mp (by decide +kernel))

def profile3_node42_cert : CutBound 9 := { lost := (rows 0 193 0 0 0 0 0 0 0), upper := (rows 193 274 485 489 497 481 64 128 256), lower := (rows 193 274 4 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 511 511 511), good := (rows 448 466 452 456 466 480 448 448 448) },{ target := 6, region := (rows 1 18 4 8 16 32 0 511 511), good := (rows 385 402 388 392 402 416 384 384 384) },{ target := 7, region := (rows 1 18 4 8 16 32 511 0 511), good := (rows 321 338 324 328 338 352 320 320 320) }] }

theorem profile3_node42 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,272] 6 481 profile3_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,272] 6 481 profile3_node42_cert).mp (by decide +kernel))

def profile3_node43_cert : CutBound 9 := { lost := (rows 0 1 64 64 0 0 0 0 0), upper := (rows 193 322 437 441 433 433 64 128 256), lower := (rows 193 322 4 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 4 8 16 32 511 511 511), good := (rows 450 450 454 458 466 482 450 450 450) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 386 388 392 400 416 384 384 384) }] }

theorem profile3_node43 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,320] 6 433 profile3_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192,320] 6 433 profile3_node43_cert).mp (by decide +kernel))

def profile3_node24_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile3_node24_route : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile3_node24 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [192] 6 (by decide) (choices 2) [17,48,65,80,192,257,272,320] profile3_node24_route profile3_node24_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node25
  · exact profile3_node33
  · exact profile3_node38
  · exact profile3_node39
  · exact profile3_node40
  · exact profile3_node41
  · exact profile3_node42
  · exact profile3_node43

def profile3_node0_column : Nat → Fin 9 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile3_node0_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile3_node0 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [] 6 (by decide) (choices 2) [48,80,192] profile3_node0_route profile3_node0_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node1
  · exact profile3_node12
  · exact profile3_node24

theorem profile3 : Upper (D (n:=9) [34,32,32,32,17,17,2,2,2]) (R (n:=9) [34,32,32,32,17,17,2,2,2]) [] 6 := profile3_node0


#print axioms profile3
end Delivery.SmallBudgetTenFinite9
