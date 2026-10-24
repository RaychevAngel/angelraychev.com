import SmallBudgetTenFinite9Common

namespace Delivery.SmallBudgetTenFinite9
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile5_node2_cert : CutBound 9 := { lost := (rows 0 192 16 16 0 0 0 0 0), upper := (rows 49 19 452 456 464 480 64 128 256), lower := (rows 49 19 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 495 492 492 492 492 492 492 492) },{ target := 6, region := (rows 1 3 4 8 16 32 0 511 511), good := (rows 435 403 388 392 400 416 384 384 384) },{ target := 7, region := (rows 1 3 4 8 16 32 511 0 511), good := (rows 371 339 324 328 336 352 320 320 320) }] }

theorem profile5_node2 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,17] 6 448 profile5_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,17] 6 448 profile5_node2_cert).mp (by decide +kernel))

def profile5_node4_cert : CutBound 9 := { lost := (rows 64 16 0 80 0 0 0 0 0), upper := (rows 49 67 84 392 400 416 64 128 256), lower := (rows 49 67 84 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 511 0 511 511 511 511), good := (rows 491 491 492 488 488 488 488 488 488) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile5_node4 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65,80] 6 384 profile5_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65,80] 6 384 profile5_node4_cert).mp (by decide +kernel))

def profile5_node5_cert : CutBound 9 := { lost := (rows 0 144 64 16 0 0 0 0 0), upper := (rows 49 67 148 456 464 480 64 128 256), lower := (rows 49 67 148 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 511 0 511 511 511 511), good := (rows 491 491 492 488 488 488 488 488 488) },{ target := 6, region := (rows 1 2 21 8 16 32 0 511 511), good := (rows 437 391 404 392 404 416 384 384 384) },{ target := 7, region := (rows 1 3 4 8 16 32 511 0 511), good := (rows 371 323 340 328 336 352 320 320 320) }] }

theorem profile5_node5 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65,144] 6 448 profile5_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65,144] 6 448 profile5_node5_cert).mp (by decide +kernel))

def profile5_node6_cert : CutBound 9 := { lost := (rows 64 16 16 64 0 0 0 0 0), upper := (rows 49 67 196 408 400 432 64 128 256), lower := (rows 49 67 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 3 511 8 0 32 511 511 511), good := (rows 487 455 452 460 452 484 452 452 452) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile5_node6 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65,192] 6 400 profile5_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65,192] 6 400 profile5_node6_cert).mp (by decide +kernel))

def profile5_node7_cert : CutBound 9 := { lost := (rows 0 144 80 0 0 0 0 0 0), upper := (rows 49 67 388 472 464 496 64 128 256), lower := (rows 49 67 388 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 3 511 8 0 32 511 511 511), good := (rows 487 455 452 460 452 484 452 452 452) },{ target := 6, region := (rows 1 2 511 8 16 32 0 511 511), good := (rows 437 391 388 396 404 420 388 388 388) },{ target := 7, region := (rows 1 3 4 8 16 32 511 0 511), good := (rows 371 323 324 328 336 352 320 320 320) }] }

theorem profile5_node7 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65,384] 6 464 profile5_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65,384] 6 464 profile5_node7_cert).mp (by decide +kernel))

def profile5_node3_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile5_node3_route : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile5_node3 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,65] 6 (by decide) (choices 2) [80,144,192,384] profile5_node3_route profile5_node3_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node4
  · exact profile5_node5
  · exact profile5_node6
  · exact profile5_node7

def profile5_node8_cert : CutBound 9 := { lost := (rows 0 384 16 16 0 0 0 0 0), upper := (rows 49 82 453 457 465 481 64 128 256), lower := (rows 49 82 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 511 511 511), good := (rows 493 450 452 456 448 480 448 448 448) },{ target := 7, region := (rows 1 19 4 8 16 32 511 0 511), good := (rows 371 338 324 328 338 352 320 320 320) },{ target := 8, region := (rows 1 19 4 8 16 32 511 511 0), good := (rows 243 210 196 200 210 224 192 192 192) }] }

theorem profile5_node8 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,80] 6 449 profile5_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,80] 6 449 profile5_node8_cert).mp (by decide +kernel))

def profile5_node10_cert : CutBound 9 := { lost := (rows 0 16 192 16 0 0 0 0 0), upper := (rows 49 194 21 456 464 480 64 128 256), lower := (rows 49 194 21 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 511 0 511 511 511 511), good := (rows 491 490 495 490 490 490 490 490 490) },{ target := 6, region := (rows 1 2 5 8 16 32 0 511 511), good := (rows 437 386 405 392 400 416 384 384 384) },{ target := 7, region := (rows 1 2 5 8 16 32 511 0 511), good := (rows 373 322 341 328 336 352 320 320 320) }] }

theorem profile5_node10 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,17] 6 448 profile5_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,17] 6 448 profile5_node10_cert).mp (by decide +kernel))

def profile5_node11_cert : CutBound 9 := { lost := (rows 64 16 16 64 0 0 0 0 0), upper := (rows 49 194 69 408 400 432 64 128 256), lower := (rows 49 194 69 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 5 8 0 32 511 511 511), good := (rows 487 450 455 458 450 482 450 450 450) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile5_node11 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,65] 6 400 profile5_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,65] 6 400 profile5_node11_cert).mp (by decide +kernel))

def profile5_node12_cert : CutBound 9 := { lost := (rows 64 16 0 80 0 0 0 0 0), upper := (rows 49 194 84 393 401 417 64 128 256), lower := (rows 49 194 84 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 9 0 33 511 511 511), good := (rows 491 450 454 458 450 482 450 450 450) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile5_node12 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,80] 6 385 profile5_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,80] 6 385 profile5_node12_cert).mp (by decide +kernel))

def profile5_node13_cert : CutBound 9 := { lost := (rows 64 16 16 64 0 0 0 0 0), upper := (rows 49 194 196 281 273 305 64 128 256), lower := (rows 49 194 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 511 8 0 32 511 511 511), good := (rows 487 454 454 462 454 486 454 454 454) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile5_node13 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,192] 6 273 profile5_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,192] 6 273 profile5_node13_cert).mp (by decide +kernel))

def profile5_node14_cert : CutBound 9 := { lost := (rows 0 16 208 0 0 0 0 0 0), upper := (rows 49 194 261 472 464 496 64 128 256), lower := (rows 49 194 261 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 5 8 0 32 511 511 511), good := (rows 487 450 455 458 450 482 450 450 450) },{ target := 6, region := (rows 1 2 5 8 16 32 0 511 511), good := (rows 437 386 389 392 400 416 384 384 384) },{ target := 7, region := (rows 1 2 5 8 16 32 511 0 511), good := (rows 373 322 325 328 336 352 320 320 320) }] }

theorem profile5_node14 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,257] 6 464 profile5_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,257] 6 464 profile5_node14_cert).mp (by decide +kernel))

def profile5_node15_cert : CutBound 9 := { lost := (rows 0 16 192 16 0 0 0 0 0), upper := (rows 49 194 276 457 465 481 64 128 256), lower := (rows 49 194 276 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 9 0 33 511 511 511), good := (rows 491 450 454 458 450 482 450 450 450) },{ target := 6, region := (rows 1 2 21 8 16 32 0 511 511), good := (rows 437 386 404 392 404 416 384 384 384) },{ target := 7, region := (rows 1 2 21 8 16 32 511 0 511), good := (rows 373 322 340 328 340 352 320 320 320) }] }

theorem profile5_node15 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,272] 6 449 profile5_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,272] 6 449 profile5_node15_cert).mp (by decide +kernel))

def profile5_node16_cert : CutBound 9 := { lost := (rows 64 16 16 64 0 0 0 0 0), upper := (rows 49 194 324 409 401 433 64 128 256), lower := (rows 49 194 324 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 511 8 0 32 511 511 511), good := (rows 487 454 454 462 454 486 454 454 454) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile5_node16 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,320] 6 401 profile5_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192,320] 6 401 profile5_node16_cert).mp (by decide +kernel))

def profile5_node9_column : Nat → Fin 9 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile5_node9_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile5_node9 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48,192] 6 (by decide) (choices 2) [17,65,80,192,257,272,320] profile5_node9_route profile5_node9_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node10
  · exact profile5_node11
  · exact profile5_node12
  · exact profile5_node13
  · exact profile5_node14
  · exact profile5_node15
  · exact profile5_node16

def profile5_node1_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile5_node1_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile5_node1 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [48] 6 (by decide) (choices 2) [17,65,80,192] profile5_node1_route profile5_node1_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node2
  · exact profile5_node3
  · exact profile5_node8
  · exact profile5_node9

def profile5_node18_cert : CutBound 9 := { lost := (rows 128 192 16 16 0 0 0 0 0), upper := (rows 81 19 484 488 496 480 64 128 256), lower := (rows 81 19 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 495 492 492 492 492 492 492 492) },{ target := 6, region := (rows 1 3 4 8 16 32 0 511 511), good := (rows 403 403 388 392 400 416 384 384 384) },{ target := 7, region := (rows 19 19 4 8 16 32 511 0 511), good := (rows 339 339 324 328 339 352 320 320 320) }] }

theorem profile5_node18 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,17] 6 480 profile5_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,17] 6 480 profile5_node18_cert).mp (by decide +kernel))

def profile5_node20_cert : CutBound 9 := { lost := (rows 0 80 0 80 0 0 0 0 0), upper := (rows 81 35 84 392 400 416 64 128 256), lower := (rows 81 35 84 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 511 0 511 511 511 511), good := (rows 491 491 492 488 488 488 488 488 488) },{ target := 6, region := (rows 1 3 4 511 511 511 0 511 511), good := (rows 443 443 444 440 440 440 440 440 440) }] }

theorem profile5_node20 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33,80] 6 384 profile5_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33,80] 6 384 profile5_node20_cert).mp (by decide +kernel))

def profile5_node21_cert : CutBound 9 := { lost := (rows 128 16 64 16 0 0 0 0 0), upper := (rows 81 35 148 456 464 480 64 128 256), lower := (rows 81 35 148 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 511 0 511 511 511 511), good := (rows 491 491 492 488 488 488 488 488 488) },{ target := 6, region := (rows 1 2 21 8 16 32 0 511 511), good := (rows 405 423 404 392 404 416 384 384 384) },{ target := 7, region := (rows 21 2 4 8 16 32 511 0 511), good := (rows 337 355 341 328 337 352 320 320 320) }] }

theorem profile5_node21 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33,144] 6 448 profile5_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33,144] 6 448 profile5_node21_cert).mp (by decide +kernel))

def profile5_node22_cert : CutBound 9 := { lost := (rows 128 64 16 64 0 0 0 0 0), upper := (rows 81 35 196 408 400 432 64 128 256), lower := (rows 81 35 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 8 0 32 511 511 511), good := (rows 453 487 452 460 452 484 452 452 452) },{ target := 6, region := (rows 1 3 4 511 511 511 0 511 511), good := (rows 443 443 444 440 440 440 440 440 440) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 355 324 328 337 352 320 320 320) }] }

theorem profile5_node22 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33,192] 6 400 profile5_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33,192] 6 400 profile5_node22_cert).mp (by decide +kernel))

def profile5_node23_cert : CutBound 9 := { lost := (rows 384 0 80 0 0 0 0 0 0), upper := (rows 81 35 388 472 464 496 64 128 256), lower := (rows 81 35 388 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 8 0 32 511 511 511), good := (rows 453 487 452 460 452 484 452 452 452) },{ target := 6, region := (rows 1 2 511 8 16 32 0 511 511), good := (rows 405 423 388 396 404 420 388 388 388) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 355 324 328 337 352 320 320 320) },{ target := 8, region := (rows 17 2 4 8 16 32 511 511 0), good := (rows 209 227 196 200 209 224 192 192 192) }] }

theorem profile5_node23 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33,384] 6 464 profile5_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33,384] 6 464 profile5_node23_cert).mp (by decide +kernel))

def profile5_node19_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile5_node19_route : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile5_node19 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,33] 6 (by decide) (choices 2) [80,144,192,384] profile5_node19_route profile5_node19_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node20
  · exact profile5_node21
  · exact profile5_node22
  · exact profile5_node23

def profile5_node24_cert : CutBound 9 := { lost := (rows 384 0 16 16 0 0 0 0 0), upper := (rows 81 50 453 457 465 481 64 128 256), lower := (rows 81 50 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 511 511 511), good := (rows 493 482 452 456 448 480 448 448 448) },{ target := 7, region := (rows 19 2 4 8 16 32 511 0 511), good := (rows 337 371 324 328 337 352 320 320 320) },{ target := 8, region := (rows 19 2 4 8 16 32 511 511 0), good := (rows 209 243 196 200 209 224 192 192 192) }] }

theorem profile5_node24 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,48] 6 449 profile5_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,48] 6 449 profile5_node24_cert).mp (by decide +kernel))

def profile5_node25_cert : CutBound 9 := { lost := (rows 128 144 64 64 0 0 0 0 0), upper := (rows 81 67 436 440 432 432 64 128 256), lower := (rows 81 67 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 511 511 511), good := (rows 451 451 452 456 448 480 448 448 448) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 447 444 444 444 444 444 444 444) },{ target := 7, region := (rows 17 19 4 8 16 32 511 0 511), good := (rows 339 323 324 328 339 352 320 320 320) }] }

theorem profile5_node25 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,65] 6 432 profile5_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,65] 6 432 profile5_node25_cert).mp (by decide +kernel))

def profile5_node26_cert : CutBound 9 := { lost := (rows 0 0 80 80 0 0 0 0 0), upper := (rows 81 82 421 425 433 417 64 128 256), lower := (rows 81 82 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 511 511 511), good := (rows 493 450 452 456 448 480 448 448 448) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 402 388 392 400 416 384 384 384) }] }

theorem profile5_node26 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,80] 6 417 profile5_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,80] 6 417 profile5_node26_cert).mp (by decide +kernel))

def profile5_node27_cert : CutBound 9 := { lost := (rows 128 144 64 64 0 0 0 0 0), upper := (rows 81 98 405 409 401 433 64 128 256), lower := (rows 81 98 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 511 511 511), good := (rows 449 482 452 456 448 482 448 448 448) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 418 388 392 400 416 384 384 384) },{ target := 7, region := (rows 17 34 4 8 16 32 511 0 511), good := (rows 337 354 324 328 337 354 320 320 320) }] }

theorem profile5_node27 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,96] 6 401 profile5_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,96] 6 401 profile5_node27_cert).mp (by decide +kernel))

def profile5_node28_cert : CutBound 9 := { lost := (rows 384 336 0 0 0 0 0 0 0), upper := (rows 81 131 500 504 496 496 64 128 256), lower := (rows 81 131 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 511 511 511), good := (rows 451 451 452 456 448 480 448 448 448) },{ target := 6, region := (rows 1 3 4 8 16 32 0 511 511), good := (rows 403 387 388 392 400 416 384 384 384) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 323 324 328 337 352 320 320 320) },{ target := 8, region := (rows 17 19 4 8 16 32 511 511 0), good := (rows 211 195 196 200 211 224 192 192 192) }] }

theorem profile5_node28 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,129] 6 496 profile5_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,129] 6 496 profile5_node28_cert).mp (by decide +kernel))

def profile5_node29_cert : CutBound 9 := { lost := (rows 128 64 16 16 0 0 0 0 0), upper := (rows 81 146 485 489 497 481 64 128 256), lower := (rows 81 146 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 511 511 511), good := (rows 493 450 452 456 448 480 448 448 448) },{ target := 6, region := (rows 1 19 4 8 16 32 0 511 511), good := (rows 403 402 388 392 402 416 384 384 384) },{ target := 7, region := (rows 19 2 4 8 16 32 511 0 511), good := (rows 337 339 324 328 337 352 320 320 320) }] }

theorem profile5_node29 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,144] 6 481 profile5_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,144] 6 481 profile5_node29_cert).mp (by decide +kernel))

def profile5_node30_cert : CutBound 9 := { lost := (rows 384 336 0 0 0 0 0 0 0), upper := (rows 81 162 469 473 465 497 64 128 256), lower := (rows 81 162 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 511 511 511), good := (rows 449 482 452 456 448 482 448 448 448) },{ target := 6, region := (rows 1 34 4 8 16 32 0 511 511), good := (rows 401 418 388 392 400 418 384 384 384) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 354 324 328 337 352 320 320 320) },{ target := 8, region := (rows 17 34 4 8 16 32 511 511 0), good := (rows 209 226 196 200 209 226 192 192 192) }] }

theorem profile5_node30 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,160] 6 465 profile5_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,160] 6 465 profile5_node30_cert).mp (by decide +kernel))

def profile5_node31_cert : CutBound 9 := { lost := (rows 128 16 64 64 0 0 0 0 0), upper := (rows 81 194 437 441 433 433 64 128 256), lower := (rows 81 194 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 8 0 32 511 511 511), good := (rows 451 450 454 458 450 482 450 450 450) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 386 388 392 400 416 384 384 384) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 322 324 328 337 352 320 320 320) }] }

theorem profile5_node31 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,192] 6 433 profile5_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,192] 6 433 profile5_node31_cert).mp (by decide +kernel))

def profile5_node32_cert : CutBound 9 := { lost := (rows 384 80 0 0 0 0 0 0 0), upper := (rows 81 386 501 505 497 497 64 128 256), lower := (rows 81 386 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 8 0 32 511 511 511), good := (rows 451 450 454 458 450 482 450 450 450) },{ target := 6, region := (rows 1 511 4 8 16 32 0 511 511), good := (rows 403 386 390 394 402 418 386 386 386) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 322 324 328 337 352 320 320 320) },{ target := 8, region := (rows 17 2 4 8 16 32 511 511 0), good := (rows 209 194 196 200 209 224 192 192 192) }] }

theorem profile5_node32 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,384] 6 497 profile5_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80,384] 6 497 profile5_node32_cert).mp (by decide +kernel))

def profile5_node17_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile5_node17_route : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile5_node17 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [80] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,384] profile5_node17_route profile5_node17_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node18
  · exact profile5_node19
  · exact profile5_node24
  · exact profile5_node25
  · exact profile5_node26
  · exact profile5_node27
  · exact profile5_node28
  · exact profile5_node29
  · exact profile5_node30
  · exact profile5_node31
  · exact profile5_node32

def profile5_node35_cert : CutBound 9 := { lost := (rows 16 64 0 80 0 0 0 0 0), upper := (rows 97 19 84 392 400 416 64 128 256), lower := (rows 97 19 84 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) },{ target := 6, region := (rows 1 3 4 511 511 511 0 511 511), good := (rows 443 443 444 440 440 440 440 440 440) }] }

theorem profile5_node35 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17,80] 6 384 profile5_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17,80] 6 384 profile5_node35_cert).mp (by decide +kernel))

def profile5_node36_cert : CutBound 9 := { lost := (rows 144 0 64 16 0 0 0 0 0), upper := (rows 97 19 148 456 464 480 64 128 256), lower := (rows 97 19 148 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) },{ target := 6, region := (rows 1 2 22 8 16 32 0 511 511), good := (rows 417 407 404 392 404 416 384 384 384) },{ target := 7, region := (rows 33 2 4 8 16 32 511 0 511), good := (rows 353 339 340 328 336 353 320 320 320) }] }

theorem profile5_node36 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17,144] 6 448 profile5_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17,144] 6 448 profile5_node36_cert).mp (by decide +kernel))

def profile5_node37_cert : CutBound 9 := { lost := (rows 16 64 16 64 0 0 0 0 0), upper := (rows 97 19 196 408 400 432 64 128 256), lower := (rows 97 19 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 33 2 511 8 0 32 511 511 511), good := (rows 485 455 452 460 452 485 452 452 452) },{ target := 6, region := (rows 1 3 4 511 511 511 0 511 511), good := (rows 443 443 444 440 440 440 440 440 440) }] }

theorem profile5_node37 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17,192] 6 400 profile5_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17,192] 6 400 profile5_node37_cert).mp (by decide +kernel))

def profile5_node38_cert : CutBound 9 := { lost := (rows 144 0 80 0 0 0 0 0 0), upper := (rows 97 19 388 472 464 496 64 128 256), lower := (rows 97 19 388 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 33 2 511 8 0 32 511 511 511), good := (rows 485 455 452 460 452 485 452 452 452) },{ target := 6, region := (rows 1 2 511 8 16 32 0 511 511), good := (rows 421 407 388 396 404 420 388 388 388) },{ target := 7, region := (rows 33 2 4 8 16 32 511 0 511), good := (rows 353 339 324 328 336 353 320 320 320) }] }

theorem profile5_node38 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17,384] 6 464 profile5_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17,384] 6 464 profile5_node38_cert).mp (by decide +kernel))

def profile5_node34_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile5_node34_route : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile5_node34 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,17] 6 (by decide) (choices 2) [80,144,192,384] profile5_node34_route profile5_node34_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node35
  · exact profile5_node36
  · exact profile5_node37
  · exact profile5_node38

def profile5_node39_cert : CutBound 9 := { lost := (rows 16 16 64 64 0 0 0 0 0), upper := (rows 97 67 404 408 400 432 64 128 256), lower := (rows 97 67 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 511 511 511), good := (rows 483 451 452 456 448 483 448 448 448) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 447 444 444 444 444 444 444 444) }] }

theorem profile5_node39 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,65] 6 400 profile5_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,65] 6 400 profile5_node39_cert).mp (by decide +kernel))

def profile5_node40_cert : CutBound 9 := { lost := (rows 144 128 64 64 0 0 0 0 0), upper := (rows 97 82 405 409 401 433 64 128 256), lower := (rows 97 82 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 511 511 511), good := (rows 481 450 452 456 448 481 448 448 448) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 402 388 392 400 416 384 384 384) },{ target := 7, region := (rows 33 18 4 8 16 32 511 0 511), good := (rows 353 338 324 328 338 353 320 320 320) }] }

theorem profile5_node40 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,80] 6 401 profile5_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,80] 6 401 profile5_node40_cert).mp (by decide +kernel))

def profile5_node41_cert : CutBound 9 := { lost := (rows 144 80 0 0 0 0 0 0 0), upper := (rows 97 131 468 472 464 496 64 128 256), lower := (rows 97 131 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 511 511 511), good := (rows 483 451 452 456 448 483 448 448 448) },{ target := 6, region := (rows 1 3 4 8 16 32 0 511 511), good := (rows 419 387 388 392 400 416 384 384 384) },{ target := 7, region := (rows 33 2 4 8 16 32 511 0 511), good := (rows 353 323 324 328 336 353 320 320 320) }] }

theorem profile5_node41 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,129] 6 464 profile5_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,129] 6 464 profile5_node41_cert).mp (by decide +kernel))

def profile5_node42_cert : CutBound 9 := { lost := (rows 400 320 0 0 0 0 0 0 0), upper := (rows 97 146 469 473 465 497 64 128 256), lower := (rows 97 146 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 511 511 511), good := (rows 481 450 452 456 448 481 448 448 448) },{ target := 6, region := (rows 1 18 4 8 16 32 0 511 511), good := (rows 417 402 388 392 402 416 384 384 384) },{ target := 7, region := (rows 33 2 4 8 16 32 511 0 511), good := (rows 353 338 324 328 336 353 320 320 320) },{ target := 8, region := (rows 33 18 4 8 16 32 511 511 0), good := (rows 225 210 196 200 210 225 192 192 192) }] }

theorem profile5_node42 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,144] 6 465 profile5_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,144] 6 465 profile5_node42_cert).mp (by decide +kernel))

def profile5_node43_cert : CutBound 9 := { lost := (rows 16 16 64 64 0 0 0 0 0), upper := (rows 97 194 405 409 401 433 64 128 256), lower := (rows 97 194 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 33 511 4 8 0 32 511 511 511), good := (rows 483 450 454 458 450 483 450 450 450) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 386 388 392 400 416 384 384 384) }] }

theorem profile5_node43 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,192] 6 401 profile5_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,192] 6 401 profile5_node43_cert).mp (by decide +kernel))

def profile5_node44_cert : CutBound 9 := { lost := (rows 144 80 0 0 0 0 0 0 0), upper := (rows 97 386 469 473 465 497 64 128 256), lower := (rows 97 386 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 33 511 4 8 0 32 511 511 511), good := (rows 483 450 454 458 450 483 450 450 450) },{ target := 6, region := (rows 1 511 4 8 16 32 0 511 511), good := (rows 419 386 390 394 402 418 386 386 386) },{ target := 7, region := (rows 33 2 4 8 16 32 511 0 511), good := (rows 353 322 324 328 336 353 320 320 320) }] }

theorem profile5_node44 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,384] 6 465 profile5_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96,384] 6 465 profile5_node44_cert).mp (by decide +kernel))

def profile5_node33_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile5_node33_route : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile5_node33 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [96] 6 (by decide) (choices 2) [17,65,80,129,144,192,384] profile5_node33_route profile5_node33_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node34
  · exact profile5_node39
  · exact profile5_node40
  · exact profile5_node41
  · exact profile5_node42
  · exact profile5_node43
  · exact profile5_node44

def profile5_node47_cert : CutBound 9 := { lost := (rows 272 256 0 16 0 0 0 0 0), upper := (rows 193 19 52 456 464 480 64 128 256), lower := (rows 193 19 52 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) },{ target := 8, region := (rows 511 22 4 8 16 32 511 511 0), good := (rows 193 211 247 201 211 225 193 193 193) }] }

theorem profile5_node47 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,48] 6 448 profile5_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,48] 6 448 profile5_node47_cert).mp (by decide +kernel))

def profile5_node48_cert : CutBound 9 := { lost := (rows 16 64 0 80 0 0 0 0 0), upper := (rows 193 19 84 424 432 416 64 128 256), lower := (rows 193 19 84 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) },{ target := 6, region := (rows 1 3 4 511 511 511 0 511 511), good := (rows 443 443 444 440 440 440 440 440 440) }] }

theorem profile5_node48 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,80] 6 416 profile5_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,80] 6 416 profile5_node48_cert).mp (by decide +kernel))

def profile5_node49_cert : CutBound 9 := { lost := (rows 16 64 16 64 0 0 0 0 0), upper := (rows 193 19 100 408 400 432 64 128 256), lower := (rows 193 19 100 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 36 8 0 32 511 511 511), good := (rows 449 451 485 457 449 485 449 449 449) },{ target := 6, region := (rows 1 3 4 511 511 511 0 511 511), good := (rows 443 443 444 440 440 440 440 440 440) }] }

theorem profile5_node49 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,96] 6 400 profile5_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,96] 6 400 profile5_node49_cert).mp (by decide +kernel))

def profile5_node50_cert : CutBound 9 := { lost := (rows 16 64 16 64 0 0 0 0 0), upper := (rows 193 19 196 312 304 304 64 128 256), lower := (rows 193 19 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 511 8 0 32 511 511 511), good := (rows 453 455 453 461 453 485 453 453 453) },{ target := 6, region := (rows 1 3 4 511 511 511 0 511 511), good := (rows 443 443 444 440 440 440 440 440 440) }] }

theorem profile5_node50 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,192] 6 304 profile5_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,192] 6 304 profile5_node50_cert).mp (by decide +kernel))

def profile5_node51_cert : CutBound 9 := { lost := (rows 16 0 192 16 0 0 0 0 0), upper := (rows 193 19 276 488 496 480 64 128 256), lower := (rows 193 19 276 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) },{ target := 6, region := (rows 1 2 22 8 16 32 0 511 511), good := (rows 385 407 404 392 404 416 384 384 384) },{ target := 7, region := (rows 1 2 22 8 16 32 511 0 511), good := (rows 321 343 340 328 340 352 320 320 320) }] }

theorem profile5_node51 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,272] 6 480 profile5_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,272] 6 480 profile5_node51_cert).mp (by decide +kernel))

def profile5_node52_cert : CutBound 9 := { lost := (rows 16 0 208 0 0 0 0 0 0), upper := (rows 193 19 292 472 464 496 64 128 256), lower := (rows 193 19 292 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 36 8 0 32 511 511 511), good := (rows 449 451 485 457 449 485 449 449 449) },{ target := 6, region := (rows 1 2 36 8 16 32 0 511 511), good := (rows 385 403 420 392 400 420 384 384 384) },{ target := 7, region := (rows 1 2 36 8 16 32 511 0 511), good := (rows 321 339 356 328 336 356 320 320 320) }] }

theorem profile5_node52 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,288] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,288] 6 464 profile5_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,288] 6 464 profile5_node52_cert).mp (by decide +kernel))

def profile5_node53_cert : CutBound 9 := { lost := (rows 16 64 16 64 0 0 0 0 0), upper := (rows 193 19 324 440 432 432 64 128 256), lower := (rows 193 19 324 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 511 8 0 32 511 511 511), good := (rows 453 455 453 461 453 485 453 453 453) },{ target := 6, region := (rows 1 3 4 511 511 511 0 511 511), good := (rows 443 443 444 440 440 440 440 440 440) }] }

theorem profile5_node53 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,320] 6 432 profile5_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17,320] 6 432 profile5_node53_cert).mp (by decide +kernel))

def profile5_node46_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile5_node46_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile5_node46 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,17] 6 (by decide) (choices 2) [48,80,96,192,272,288,320] profile5_node46_route profile5_node46_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node47
  · exact profile5_node48
  · exact profile5_node49
  · exact profile5_node50
  · exact profile5_node51
  · exact profile5_node52
  · exact profile5_node53

def profile5_node54_cert : CutBound 9 := { lost := (rows 272 272 0 0 0 0 0 0 0), upper := (rows 193 35 468 472 464 496 64 128 256), lower := (rows 193 35 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 34 4 8 0 32 511 511 511), good := (rows 449 483 453 457 449 483 449 449 449) },{ target := 8, region := (rows 511 34 4 8 16 32 511 511 0), good := (rows 193 227 197 201 209 227 193 193 193) }] }

theorem profile5_node54 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,33] 6 464 profile5_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,33] 6 464 profile5_node54_cert).mp (by decide +kernel))

def profile5_node56_cert : CutBound 9 := { lost := (rows 272 0 256 16 0 0 0 0 0), upper := (rows 193 50 21 456 464 480 64 128 256), lower := (rows 193 50 21 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) },{ target := 8, region := (rows 511 2 22 8 16 32 511 511 0), good := (rows 193 247 213 201 213 225 193 193 193) }] }

theorem profile5_node56 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,17] 6 448 profile5_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,17] 6 448 profile5_node56_cert).mp (by decide +kernel))

def profile5_node57_cert : CutBound 9 := { lost := (rows 16 64 16 64 0 0 0 0 0), upper := (rows 193 50 69 408 400 432 64 128 256), lower := (rows 193 50 69 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 511 8 0 32 511 511 511), good := (rows 453 487 453 461 453 485 453 453 453) },{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 447 442 442 442 442 442 442) }] }

theorem profile5_node57 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,65] 6 400 profile5_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,65] 6 400 profile5_node57_cert).mp (by decide +kernel))

def profile5_node58_cert : CutBound 9 := { lost := (rows 16 64 0 80 0 0 0 0 0), upper := (rows 193 50 84 393 401 417 64 128 256), lower := (rows 193 50 84 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) },{ target := 6, region := (rows 1 3 4 9 17 33 0 511 511), good := (rows 443 434 404 392 400 416 384 384 384) }] }

theorem profile5_node58 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,80] 6 385 profile5_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,80] 6 385 profile5_node58_cert).mp (by decide +kernel))

def profile5_node59_cert : CutBound 9 := { lost := (rows 16 64 16 64 0 0 0 0 0), upper := (rows 193 50 196 281 273 305 64 128 256), lower := (rows 193 50 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 511 8 0 32 511 511 511), good := (rows 453 487 453 461 453 485 453 453 453) },{ target := 6, region := (rows 1 3 4 9 17 33 0 511 511), good := (rows 443 434 388 392 400 416 384 384 384) }] }

theorem profile5_node59 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,192] 6 273 profile5_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,192] 6 273 profile5_node59_cert).mp (by decide +kernel))

def profile5_node60_cert : CutBound 9 := { lost := (rows 16 0 208 0 0 0 0 0 0), upper := (rows 193 50 261 472 464 496 64 128 256), lower := (rows 193 50 261 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 511 8 0 32 511 511 511), good := (rows 453 487 453 461 453 485 453 453 453) },{ target := 6, region := (rows 1 2 5 8 16 32 0 511 511), good := (rows 389 434 389 392 400 416 384 384 384) },{ target := 7, region := (rows 1 2 5 8 16 32 511 0 511), good := (rows 325 370 325 328 336 352 320 320 320) }] }

theorem profile5_node60 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,257] 6 464 profile5_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,257] 6 464 profile5_node60_cert).mp (by decide +kernel))

def profile5_node61_cert : CutBound 9 := { lost := (rows 16 0 192 16 0 0 0 0 0), upper := (rows 193 50 276 457 465 481 64 128 256), lower := (rows 193 50 276 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) },{ target := 6, region := (rows 1 2 22 8 16 32 0 511 511), good := (rows 385 438 404 392 404 416 384 384 384) },{ target := 7, region := (rows 1 2 22 8 16 32 511 0 511), good := (rows 321 374 340 328 340 352 320 320 320) }] }

theorem profile5_node61 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,272] 6 449 profile5_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,272] 6 449 profile5_node61_cert).mp (by decide +kernel))

def profile5_node62_cert : CutBound 9 := { lost := (rows 16 64 16 64 0 0 0 0 0), upper := (rows 193 50 324 409 401 433 64 128 256), lower := (rows 193 50 324 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 511 8 0 32 511 511 511), good := (rows 453 487 453 461 453 485 453 453 453) },{ target := 6, region := (rows 1 3 4 9 17 33 0 511 511), good := (rows 443 434 388 392 400 416 384 384 384) }] }

theorem profile5_node62 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,320] 6 401 profile5_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48,320] 6 401 profile5_node62_cert).mp (by decide +kernel))

def profile5_node55_column : Nat → Fin 9 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile5_node55_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile5_node55 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,48] 6 (by decide) (choices 2) [17,65,80,192,257,272,320] profile5_node55_route profile5_node55_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node56
  · exact profile5_node57
  · exact profile5_node58
  · exact profile5_node59
  · exact profile5_node60
  · exact profile5_node61
  · exact profile5_node62

def profile5_node63_cert : CutBound 9 := { lost := (rows 16 16 64 64 0 0 0 0 0), upper := (rows 193 67 436 440 432 432 64 128 256), lower := (rows 193 67 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 511 4 8 0 32 511 511 511), good := (rows 451 451 455 459 451 483 451 451 451) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 447 444 444 444 444 444 444 444) }] }

theorem profile5_node63 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,65] 6 432 profile5_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,65] 6 432 profile5_node63_cert).mp (by decide +kernel))

def profile5_node64_cert : CutBound 9 := { lost := (rows 16 128 64 64 0 0 0 0 0), upper := (rows 193 82 437 441 433 433 64 128 256), lower := (rows 193 82 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 8 0 32 511 511 511), good := (rows 449 451 453 457 449 481 449 449 449) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 402 388 392 400 416 384 384 384) },{ target := 7, region := (rows 1 18 4 8 16 32 511 0 511), good := (rows 321 338 324 328 338 352 320 320 320) }] }

theorem profile5_node64 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,80] 6 433 profile5_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,80] 6 433 profile5_node64_cert).mp (by decide +kernel))

def profile5_node65_cert : CutBound 9 := { lost := (rows 16 16 64 64 0 0 0 0 0), upper := (rows 193 98 405 409 401 433 64 128 256), lower := (rows 193 98 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 34 4 8 0 32 511 511 511), good := (rows 449 483 453 457 449 483 449 449 449) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 418 388 392 400 416 384 384 384) }] }

theorem profile5_node65 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,96] 6 401 profile5_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,96] 6 401 profile5_node65_cert).mp (by decide +kernel))

def profile5_node66_cert : CutBound 9 := { lost := (rows 16 16 64 64 0 0 0 0 0), upper := (rows 193 194 309 313 305 305 64 128 256), lower := (rows 193 194 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 511 4 8 0 32 511 511 511), good := (rows 451 451 455 459 451 483 451 451 451) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 386 388 392 400 416 384 384 384) }] }

theorem profile5_node66 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,192] 6 305 profile5_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,192] 6 305 profile5_node66_cert).mp (by decide +kernel))

def profile5_node67_cert : CutBound 9 := { lost := (rows 16 208 0 0 0 0 0 0 0), upper := (rows 193 259 500 504 496 496 64 128 256), lower := (rows 193 259 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 511 4 8 0 32 511 511 511), good := (rows 451 451 455 459 451 483 451 451 451) },{ target := 6, region := (rows 1 3 4 8 16 32 0 511 511), good := (rows 387 387 388 392 400 416 384 384 384) },{ target := 7, region := (rows 1 3 4 8 16 32 511 0 511), good := (rows 323 323 324 328 336 352 320 320 320) }] }

theorem profile5_node67 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,257] 6 496 profile5_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,257] 6 496 profile5_node67_cert).mp (by decide +kernel))

def profile5_node68_cert : CutBound 9 := { lost := (rows 272 192 0 0 0 0 0 0 0), upper := (rows 193 274 501 505 497 497 64 128 256), lower := (rows 193 274 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 8 0 32 511 511 511), good := (rows 449 451 453 457 449 481 449 449 449) },{ target := 6, region := (rows 1 18 4 8 16 32 0 511 511), good := (rows 385 402 388 392 402 416 384 384 384) },{ target := 7, region := (rows 1 18 4 8 16 32 511 0 511), good := (rows 321 338 324 328 338 352 320 320 320) },{ target := 8, region := (rows 511 2 4 8 16 32 511 511 0), good := (rows 193 211 197 201 209 225 193 193 193) }] }

theorem profile5_node68 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,272] 6 497 profile5_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,272] 6 497 profile5_node68_cert).mp (by decide +kernel))

def profile5_node69_cert : CutBound 9 := { lost := (rows 16 208 0 0 0 0 0 0 0), upper := (rows 193 290 469 473 465 497 64 128 256), lower := (rows 193 290 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 34 4 8 0 32 511 511 511), good := (rows 449 483 453 457 449 483 449 449 449) },{ target := 6, region := (rows 1 34 4 8 16 32 0 511 511), good := (rows 385 418 388 392 400 418 384 384 384) },{ target := 7, region := (rows 1 34 4 8 16 32 511 0 511), good := (rows 321 354 324 328 336 354 320 320 320) }] }

theorem profile5_node69 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,288] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,288] 6 465 profile5_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,288] 6 465 profile5_node69_cert).mp (by decide +kernel))

def profile5_node70_cert : CutBound 9 := { lost := (rows 16 16 64 64 0 0 0 0 0), upper := (rows 193 322 437 441 433 433 64 128 256), lower := (rows 193 322 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 511 4 8 0 32 511 511 511), good := (rows 451 451 455 459 451 483 451 451 451) },{ target := 6, region := (rows 1 2 5 9 17 33 0 511 511), good := (rows 445 386 388 392 400 416 384 384 384) }] }

theorem profile5_node70 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,320] 6 433 profile5_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192,320] 6 433 profile5_node70_cert).mp (by decide +kernel))

def profile5_node45_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile5_node45_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile5_node45 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [192] 6 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] profile5_node45_route profile5_node45_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node46
  · exact profile5_node54
  · exact profile5_node55
  · exact profile5_node63
  · exact profile5_node64
  · exact profile5_node65
  · exact profile5_node66
  · exact profile5_node67
  · exact profile5_node68
  · exact profile5_node69
  · exact profile5_node70

def profile5_node0_column : Nat → Fin 9 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile5_node0_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile5_node0 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [] 6 (by decide) (choices 2) [48,80,96,192] profile5_node0_route profile5_node0_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node1
  · exact profile5_node17
  · exact profile5_node33
  · exact profile5_node45

theorem profile5 : Upper (D (n:=9) [33,32,32,32,18,17,2,2,2]) (R (n:=9) [33,32,32,32,18,17,2,2,2]) [] 6 := profile5_node0


#print axioms profile5
end Delivery.SmallBudgetTenFinite9
