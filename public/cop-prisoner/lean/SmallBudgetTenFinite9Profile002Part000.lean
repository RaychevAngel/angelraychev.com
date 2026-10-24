import SmallBudgetTenFinite9Common

namespace Delivery.SmallBudgetTenFinite9
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile2_node2_cert : CutBound 9 := { lost := (rows 192 192 32 32 32 0 0 0 0), upper := (rows 35 35 452 456 464 32 64 128 256), lower := (rows 35 35 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 511 511 511 0 511 511 511), good := (rows 479 479 476 476 476 476 476 476 476) },{ target := 6, region := (rows 511 511 4 8 16 511 0 511 511), good := (rows 419 419 423 427 435 419 419 419 419) },{ target := 7, region := (rows 511 511 4 8 16 511 511 0 511), good := (rows 355 355 359 363 371 355 355 355 355) }] }

theorem profile2_node2 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,33] 6 448 profile2_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,33] 6 448 profile2_node2_cert).mp (by decide +kernel))

def profile2_node3_cert : CutBound 9 := { lost := (rows 448 416 0 0 0 0 0 0 0), upper := (rows 35 67 484 488 496 32 64 128 256), lower := (rows 35 67 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 511 511 511), good := (rows 451 451 452 456 464 448 448 448 448) },{ target := 6, region := (rows 3 2 4 8 16 511 0 511 511), good := (rows 419 419 420 424 432 416 416 416 416) },{ target := 7, region := (rows 511 511 4 8 16 511 511 0 511), good := (rows 355 355 359 363 371 355 355 355 355) },{ target := 8, region := (rows 511 511 4 8 16 511 511 511 0), good := (rows 227 227 231 235 243 227 227 227 227) }] }

theorem profile2_node3 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,65] 6 480 profile2_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,65] 6 480 profile2_node3_cert).mp (by decide +kernel))

def profile2_node4_cert : CutBound 9 := { lost := (rows 192 128 32 32 32 0 0 0 0), upper := (rows 35 98 453 457 465 32 64 128 256), lower := (rows 35 98 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 511 511 511), good := (rows 479 450 452 456 464 448 448 448 448) },{ target := 6, region := (rows 3 2 4 8 16 511 0 511 511), good := (rows 419 419 420 424 432 416 416 416 416) },{ target := 7, region := (rows 511 511 4 8 16 511 511 0 511), good := (rows 355 355 359 363 371 355 355 355 355) }] }

theorem profile2_node4 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,96] 6 449 profile2_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,96] 6 449 profile2_node4_cert).mp (by decide +kernel))

def profile2_node6_cert : CutBound 9 := { lost := (rows 192 32 192 32 32 0 0 0 0), upper := (rows 35 194 37 456 464 32 64 128 256), lower := (rows 35 194 37 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 4 511 511 0 511 511 511), good := (rows 475 474 479 474 474 474 474 474 474) },{ target := 6, region := (rows 3 2 7 8 16 511 0 511 511), good := (rows 423 423 421 424 432 416 416 416 416) },{ target := 7, region := (rows 3 2 7 8 16 511 511 0 511), good := (rows 359 359 357 360 368 352 352 352 352) }] }

theorem profile2_node6 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,33] 6 448 profile2_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,33] 6 448 profile2_node6_cert).mp (by decide +kernel))

def profile2_node7_cert : CutBound 9 := { lost := (rows 192 32 160 64 64 0 0 0 0), upper := (rows 35 194 69 424 432 32 64 128 256), lower := (rows 35 194 69 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 5 8 16 0 511 511 511), good := (rows 455 450 455 458 466 450 450 450 450) },{ target := 6, region := (rows 3 2 4 511 511 511 0 511 511), good := (rows 443 443 445 440 440 440 440 440 440) },{ target := 7, region := (rows 3 2 7 8 16 511 511 0 511), good := (rows 359 359 357 360 368 352 352 352 352) }] }

theorem profile2_node7 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,65] 6 416 profile2_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,65] 6 416 profile2_node7_cert).mp (by decide +kernel))

def profile2_node8_cert : CutBound 9 := { lost := (rows 64 32 0 96 96 0 0 0 0), upper := (rows 35 194 100 393 401 32 64 128 256), lower := (rows 35 194 100 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 4 9 17 0 511 511 511), good := (rows 475 450 454 458 466 450 450 450 450) },{ target := 6, region := (rows 3 2 4 11 19 511 0 511 511), good := (rows 443 443 420 424 432 416 416 416 416) }] }

theorem profile2_node8 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,96] 6 385 profile2_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,96] 6 385 profile2_node8_cert).mp (by decide +kernel))

def profile2_node9_cert : CutBound 9 := { lost := (rows 192 32 32 192 192 0 0 0 0), upper := (rows 35 194 196 297 305 32 64 128 256), lower := (rows 35 194 196 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 511 8 16 0 511 511 511), good := (rows 455 454 454 462 470 454 454 454 454) },{ target := 6, region := (rows 3 2 4 11 19 511 0 511 511), good := (rows 443 443 420 424 432 416 416 416 416) },{ target := 7, region := (rows 3 2 4 11 19 511 511 0 511), good := (rows 379 379 356 360 368 352 352 352 352) }] }

theorem profile2_node9 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,192] 6 289 profile2_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,192] 6 289 profile2_node9_cert).mp (by decide +kernel))

def profile2_node10_cert : CutBound 9 := { lost := (rows 192 32 224 0 0 0 0 0 0), upper := (rows 35 194 261 488 496 32 64 128 256), lower := (rows 35 194 261 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 5 8 16 0 511 511 511), good := (rows 455 450 455 458 466 450 450 450 450) },{ target := 6, region := (rows 3 2 7 8 16 511 0 511 511), good := (rows 423 423 421 424 432 416 416 416 416) },{ target := 7, region := (rows 3 2 7 8 16 511 511 0 511), good := (rows 359 359 357 360 368 352 352 352 352) }] }

theorem profile2_node10 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,257] 6 480 profile2_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,257] 6 480 profile2_node10_cert).mp (by decide +kernel))

def profile2_node11_cert : CutBound 9 := { lost := (rows 192 32 192 32 32 0 0 0 0), upper := (rows 35 194 292 457 465 32 64 128 256), lower := (rows 35 194 292 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 4 9 17 0 511 511 511), good := (rows 475 450 454 458 466 450 450 450 450) },{ target := 6, region := (rows 3 2 511 8 16 511 0 511 511), good := (rows 423 423 420 428 436 420 420 420 420) },{ target := 7, region := (rows 3 2 511 8 16 511 511 0 511), good := (rows 359 359 356 364 372 356 356 356 356) }] }

theorem profile2_node11 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,288] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,288] 6 449 profile2_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,288] 6 449 profile2_node11_cert).mp (by decide +kernel))

def profile2_node12_cert : CutBound 9 := { lost := (rows 192 32 160 64 64 0 0 0 0), upper := (rows 35 194 324 425 433 32 64 128 256), lower := (rows 35 194 324 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 511 8 16 0 511 511 511), good := (rows 455 454 454 462 470 454 454 454 454) },{ target := 6, region := (rows 3 2 4 11 19 511 0 511 511), good := (rows 443 443 420 424 432 416 416 416 416) },{ target := 7, region := (rows 3 2 511 8 16 511 511 0 511), good := (rows 359 359 356 364 372 356 356 356 356) }] }

theorem profile2_node12 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,320] 6 417 profile2_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192,320] 6 417 profile2_node12_cert).mp (by decide +kernel))

def profile2_node5_column : Nat → Fin 9 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile2_node5_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile2_node5 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34,192] 6 (by decide) (choices 2) [33,65,96,192,257,288,320] profile2_node5_route profile2_node5_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node6
  · exact profile2_node7
  · exact profile2_node8
  · exact profile2_node9
  · exact profile2_node10
  · exact profile2_node11
  · exact profile2_node12

def profile2_node1_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile2_node1_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile2_node1 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [34] 6 (by decide) (choices 2) [33,65,96,192] profile2_node1_route profile2_node1_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node2
  · exact profile2_node3
  · exact profile2_node4
  · exact profile2_node5

def profile2_node14_cert : CutBound 9 := { lost := (rows 128 192 32 32 32 0 0 0 0), upper := (rows 97 35 454 458 466 32 64 128 256), lower := (rows 97 35 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 511 511 511), good := (rows 449 479 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 3 4 8 16 511 0 511 511), good := (rows 419 419 420 424 432 416 416 416 416) },{ target := 7, region := (rows 511 511 4 8 16 511 511 0 511), good := (rows 355 355 359 363 371 355 355 355 355) }] }

theorem profile2_node14 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,33] 6 450 profile2_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,33] 6 450 profile2_node14_cert).mp (by decide +kernel))

def profile2_node16_cert : CutBound 9 := { lost := (rows 128 128 128 96 96 0 0 0 0), upper := (rows 97 98 7 392 400 32 64 128 256), lower := (rows 97 98 7 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 511 511 0 511 511 511), good := (rows 473 474 479 472 472 472 472 472 472) },{ target := 6, region := (rows 1 2 4 511 511 511 0 511 511), good := (rows 441 442 447 440 440 440 440 440 440) },{ target := 7, region := (rows 511 511 511 8 16 511 511 0 511), good := (rows 359 359 359 367 375 359 359 359 359) }] }

theorem profile2_node16 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96,3] 6 384 profile2_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96,3] 6 384 profile2_node16_cert).mp (by decide +kernel))

def profile2_node17_cert : CutBound 9 := { lost := (rows 0 0 96 96 96 0 0 0 0), upper := (rows 97 98 133 394 402 32 64 128 256), lower := (rows 97 98 133 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 10 18 0 511 511 511), good := (rows 453 474 453 456 464 448 448 448 448) },{ target := 6, region := (rows 1 2 5 10 18 511 0 511 511), good := (rows 421 442 421 424 432 416 416 416 416) }] }

theorem profile2_node17 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96,129] 6 386 profile2_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96,129] 6 386 profile2_node17_cert).mp (by decide +kernel))

def profile2_node18_cert : CutBound 9 := { lost := (rows 0 0 96 96 96 0 0 0 0), upper := (rows 97 98 134 393 401 32 64 128 256), lower := (rows 97 98 134 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 9 17 0 511 511 511), good := (rows 473 454 454 456 464 448 448 448 448) },{ target := 6, region := (rows 1 2 6 9 17 511 0 511 511), good := (rows 441 422 422 424 432 416 416 416 416) }] }

theorem profile2_node18 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96,130] 6 385 profile2_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96,130] 6 385 profile2_node18_cert).mp (by decide +kernel))

def profile2_node19_cert : CutBound 9 := { lost := (rows 384 384 96 0 0 0 0 0 0), upper := (rows 97 98 388 395 403 32 64 128 256), lower := (rows 97 98 388 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 511 8 16 0 511 511 511), good := (rows 453 454 452 460 468 452 452 452 452) },{ target := 6, region := (rows 1 2 511 8 16 511 0 511 511), good := (rows 421 422 420 428 436 420 420 420 420) },{ target := 7, region := (rows 511 511 4 8 16 511 511 0 511), good := (rows 355 355 359 363 371 355 355 355 355) },{ target := 8, region := (rows 511 511 4 8 16 511 511 511 0), good := (rows 227 227 231 235 243 227 227 227 227) }] }

theorem profile2_node19 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96,384] 6 387 profile2_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96,384] 6 387 profile2_node19_cert).mp (by decide +kernel))

def profile2_node15_column : Nat → Fin 9 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 65 => 6 | 10 => 3 | 18 => 4 | 34 => 5 | 66 => 6 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0

def profile2_node15_route : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile2_node15 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,96] 6 (by decide) (choices 2) [3,129,130,384] profile2_node15_route profile2_node15_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node16
  · exact profile2_node17
  · exact profile2_node18
  · exact profile2_node19

def profile2_node21_cert : CutBound 9 := { lost := (rows 128 96 192 32 32 0 0 0 0), upper := (rows 97 131 38 456 464 32 64 128 256), lower := (rows 97 131 38 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 511 511 0 511 511 511), good := (rows 475 475 478 472 472 472 472 472 472) },{ target := 6, region := (rows 1 3 7 8 16 511 0 511 511), good := (rows 423 423 422 424 432 416 416 416 416) },{ target := 7, region := (rows 511 2 6 8 16 511 511 0 511), good := (rows 353 359 359 361 369 353 353 353 353) }] }

theorem profile2_node21 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,34] 6 448 profile2_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,34] 6 448 profile2_node21_cert).mp (by decide +kernel))

def profile2_node22_cert : CutBound 9 := { lost := (rows 0 96 0 96 96 0 0 0 0), upper := (rows 97 131 100 394 402 32 64 128 256), lower := (rows 97 131 100 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 11 19 0 511 511 511), good := (rows 475 475 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 3 4 11 19 511 0 511 511), good := (rows 443 443 420 424 432 416 416 416 416) }] }

theorem profile2_node22 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,96] 6 386 profile2_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,96] 6 386 profile2_node22_cert).mp (by decide +kernel))

def profile2_node23_cert : CutBound 9 := { lost := (rows 128 96 96 128 128 0 0 0 0), upper := (rows 97 131 134 360 368 32 64 128 256), lower := (rows 97 131 134 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 7 8 16 0 511 511 511), good := (rows 455 455 454 456 464 448 448 448 448) },{ target := 6, region := (rows 1 3 7 8 16 511 0 511 511), good := (rows 423 423 422 424 432 416 416 416 416) },{ target := 7, region := (rows 511 2 4 511 511 511 511 0 511), good := (rows 377 379 383 377 377 377 377 377 377) }] }

theorem profile2_node23 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,130] 6 352 profile2_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,130] 6 352 profile2_node23_cert).mp (by decide +kernel))

def profile2_node24_cert : CutBound 9 := { lost := (rows 128 96 64 160 160 0 0 0 0), upper := (rows 97 131 164 330 338 32 64 128 256), lower := (rows 97 131 164 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 11 19 0 511 511 511), good := (rows 475 475 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 3 511 8 16 511 0 511 511), good := (rows 423 423 420 428 436 420 420 420 420) },{ target := 7, region := (rows 511 2 4 10 18 511 511 0 511), good := (rows 353 379 357 361 369 353 353 353 353) }] }

theorem profile2_node24 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,160] 6 322 profile2_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,160] 6 322 profile2_node24_cert).mp (by decide +kernel))

def profile2_node25_cert : CutBound 9 := { lost := (rows 128 96 224 0 0 0 0 0 0), upper := (rows 97 131 262 488 496 32 64 128 256), lower := (rows 97 131 262 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 7 8 16 0 511 511 511), good := (rows 455 455 454 456 464 448 448 448 448) },{ target := 6, region := (rows 1 3 7 8 16 511 0 511 511), good := (rows 423 423 422 424 432 416 416 416 416) },{ target := 7, region := (rows 511 2 6 8 16 511 511 0 511), good := (rows 353 359 359 361 369 353 353 353 353) }] }

theorem profile2_node25 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,258] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,258] 6 480 profile2_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,258] 6 480 profile2_node25_cert).mp (by decide +kernel))

def profile2_node26_cert : CutBound 9 := { lost := (rows 128 96 192 32 32 0 0 0 0), upper := (rows 97 131 292 458 466 32 64 128 256), lower := (rows 97 131 292 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 11 19 0 511 511 511), good := (rows 475 475 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 3 511 8 16 511 0 511 511), good := (rows 423 423 420 428 436 420 420 420 420) },{ target := 7, region := (rows 511 2 511 8 16 511 511 0 511), good := (rows 357 359 357 365 373 357 357 357 357) }] }

theorem profile2_node26 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,288] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,288] 6 450 profile2_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,288] 6 450 profile2_node26_cert).mp (by decide +kernel))

def profile2_node27_cert : CutBound 9 := { lost := (rows 128 96 96 128 128 0 0 0 0), upper := (rows 97 131 388 362 370 32 64 128 256), lower := (rows 97 131 388 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 511 8 16 0 511 511 511), good := (rows 455 455 452 460 468 452 452 452 452) },{ target := 6, region := (rows 1 3 511 8 16 511 0 511 511), good := (rows 423 423 420 428 436 420 420 420 420) },{ target := 7, region := (rows 511 2 4 10 18 511 511 0 511), good := (rows 353 379 357 361 369 353 353 353 353) }] }

theorem profile2_node27 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,384] 6 354 profile2_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129,384] 6 354 profile2_node27_cert).mp (by decide +kernel))

def profile2_node20_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile2_node20_route : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile2_node20 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,129] 6 (by decide) (choices 2) [34,96,130,160,258,288,384] profile2_node20_route profile2_node20_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node21
  · exact profile2_node22
  · exact profile2_node23
  · exact profile2_node24
  · exact profile2_node25
  · exact profile2_node26
  · exact profile2_node27

def profile2_node29_cert : CutBound 9 := { lost := (rows 128 64 192 32 32 0 0 0 0), upper := (rows 97 162 7 456 464 32 64 128 256), lower := (rows 97 162 7 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 511 511 0 511 511 511), good := (rows 473 474 479 472 472 472 472 472 472) },{ target := 6, region := (rows 1 511 5 8 16 511 0 511 511), good := (rows 423 418 423 426 434 418 418 418 418) },{ target := 7, region := (rows 511 2 6 8 16 511 511 0 511), good := (rows 353 359 359 361 369 353 353 353 353) }] }

theorem profile2_node29 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,3] 6 448 profile2_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,3] 6 448 profile2_node29_cert).mp (by decide +kernel))

def profile2_node30_cert : CutBound 9 := { lost := (rows 0 64 32 96 96 0 0 0 0), upper := (rows 97 162 69 394 402 32 64 128 256), lower := (rows 97 162 69 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 10 18 0 511 511 511), good := (rows 453 474 453 456 464 448 448 448 448) },{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 447 442 442 442 442 442 442) }] }

theorem profile2_node30 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,65] 6 386 profile2_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,65] 6 386 profile2_node30_cert).mp (by decide +kernel))

def profile2_node31_cert : CutBound 9 := { lost := (rows 0 64 32 96 96 0 0 0 0), upper := (rows 97 162 70 393 401 32 64 128 256), lower := (rows 97 162 70 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 9 17 0 511 511 511), good := (rows 473 454 454 456 464 448 448 448 448) },{ target := 6, region := (rows 1 511 4 9 17 511 0 511 511), good := (rows 443 418 422 426 434 418 418 418 418) }] }

theorem profile2_node31 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,66] 6 385 profile2_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,66] 6 385 profile2_node31_cert).mp (by decide +kernel))

def profile2_node32_cert : CutBound 9 := { lost := (rows 128 64 96 160 160 0 0 0 0), upper := (rows 97 162 133 330 338 32 64 128 256), lower := (rows 97 162 133 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 10 18 0 511 511 511), good := (rows 453 474 453 456 464 448 448 448 448) },{ target := 6, region := (rows 1 511 5 8 16 511 0 511 511), good := (rows 423 418 423 426 434 418 418 418 418) },{ target := 7, region := (rows 511 2 4 10 18 511 511 0 511), good := (rows 353 379 357 361 369 353 353 353 353) }] }

theorem profile2_node32 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,129] 6 322 profile2_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,129] 6 322 profile2_node32_cert).mp (by decide +kernel))

def profile2_node33_cert : CutBound 9 := { lost := (rows 128 64 96 160 160 0 0 0 0), upper := (rows 97 162 134 329 337 32 64 128 256), lower := (rows 97 162 134 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 9 17 0 511 511 511), good := (rows 473 454 454 456 464 448 448 448 448) },{ target := 6, region := (rows 1 511 511 8 16 511 0 511 511), good := (rows 423 422 422 430 438 422 422 422 422) },{ target := 7, region := (rows 511 2 4 511 511 511 511 0 511), good := (rows 377 379 383 377 377 377 377 377 377) }] }

theorem profile2_node33 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,130] 6 321 profile2_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,130] 6 321 profile2_node33_cert).mp (by decide +kernel))

def profile2_node34_cert : CutBound 9 := { lost := (rows 128 64 32 192 192 0 0 0 0), upper := (rows 97 162 196 267 275 32 64 128 256), lower := (rows 97 162 196 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 511 8 16 0 511 511 511), good := (rows 453 454 452 460 468 452 452 452 452) },{ target := 6, region := (rows 1 511 4 9 17 511 0 511 511), good := (rows 443 418 422 426 434 418 418 418 418) },{ target := 7, region := (rows 511 2 4 10 18 511 511 0 511), good := (rows 353 379 357 361 369 353 353 353 353) }] }

theorem profile2_node34 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,192] 6 259 profile2_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,192] 6 259 profile2_node34_cert).mp (by decide +kernel))

def profile2_node35_cert : CutBound 9 := { lost := (rows 128 64 224 32 32 0 0 0 0), upper := (rows 97 162 261 458 466 32 64 128 256), lower := (rows 97 162 261 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 10 18 0 511 511 511), good := (rows 453 474 453 456 464 448 448 448 448) },{ target := 6, region := (rows 1 511 5 8 16 511 0 511 511), good := (rows 423 418 423 426 434 418 418 418 418) },{ target := 7, region := (rows 511 2 511 8 16 511 511 0 511), good := (rows 357 359 357 365 373 357 357 357 357) }] }

theorem profile2_node35 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,257] 6 450 profile2_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,257] 6 450 profile2_node35_cert).mp (by decide +kernel))

def profile2_node36_cert : CutBound 9 := { lost := (rows 128 64 224 32 32 0 0 0 0), upper := (rows 97 162 262 457 465 32 64 128 256), lower := (rows 97 162 262 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 9 17 0 511 511 511), good := (rows 473 454 454 456 464 448 448 448 448) },{ target := 6, region := (rows 1 511 511 8 16 511 0 511 511), good := (rows 423 422 422 430 438 422 422 422 422) },{ target := 7, region := (rows 511 2 6 8 16 511 511 0 511), good := (rows 353 359 359 361 369 353 353 353 353) }] }

theorem profile2_node36 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,258] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,258] 6 449 profile2_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,258] 6 449 profile2_node36_cert).mp (by decide +kernel))

def profile2_node37_cert : CutBound 9 := { lost := (rows 128 64 160 64 64 0 0 0 0), upper := (rows 97 162 324 395 403 32 64 128 256), lower := (rows 97 162 324 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 511 8 16 0 511 511 511), good := (rows 453 454 452 460 468 452 452 452 452) },{ target := 6, region := (rows 1 511 4 9 17 511 0 511 511), good := (rows 443 418 422 426 434 418 418 418 418) },{ target := 7, region := (rows 511 2 511 8 16 511 511 0 511), good := (rows 357 359 357 365 373 357 357 357 357) }] }

theorem profile2_node37 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,320] 6 387 profile2_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,320] 6 387 profile2_node37_cert).mp (by decide +kernel))

def profile2_node38_cert : CutBound 9 := { lost := (rows 128 64 96 128 128 0 0 0 0), upper := (rows 97 162 388 331 339 32 64 128 256), lower := (rows 97 162 388 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 511 8 16 0 511 511 511), good := (rows 453 454 452 460 468 452 452 452 452) },{ target := 6, region := (rows 1 511 511 8 16 511 0 511 511), good := (rows 423 422 422 430 438 422 422 422 422) },{ target := 7, region := (rows 511 2 4 10 18 511 511 0 511), good := (rows 353 379 357 361 369 353 353 353 353) }] }

theorem profile2_node38 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,384] 6 323 profile2_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160,384] 6 323 profile2_node38_cert).mp (by decide +kernel))

def profile2_node28_column : Nat → Fin 9 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile2_node28_route : Route 9 := (fun mask => (mask,id))

theorem profile2_node28 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,160] 6 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] profile2_node28_route profile2_node28_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node29
  · exact profile2_node30
  · exact profile2_node31
  · exact profile2_node32
  · exact profile2_node33
  · exact profile2_node34
  · exact profile2_node35
  · exact profile2_node36
  · exact profile2_node37
  · exact profile2_node38

def profile2_node40_cert : CutBound 9 := { lost := (rows 128 96 224 0 0 0 0 0 0), upper := (rows 97 386 7 488 496 32 64 128 256), lower := (rows 97 386 7 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 5 8 16 0 511 511 511), good := (rows 455 450 455 458 466 450 450 450 450) },{ target := 6, region := (rows 1 511 5 8 16 511 0 511 511), good := (rows 423 418 423 426 434 418 418 418 418) },{ target := 7, region := (rows 511 2 6 8 16 511 511 0 511), good := (rows 353 359 359 361 369 353 353 353 353) }] }

theorem profile2_node40 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,3] 6 480 profile2_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,3] 6 480 profile2_node40_cert).mp (by decide +kernel))

def profile2_node41_cert : CutBound 9 := { lost := (rows 128 96 192 32 32 0 0 0 0), upper := (rows 97 386 37 458 466 32 64 128 256), lower := (rows 97 386 37 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 4 511 511 0 511 511 511), good := (rows 475 474 479 474 474 474 474 474 474) },{ target := 6, region := (rows 1 511 5 8 16 511 0 511 511), good := (rows 423 418 423 426 434 418 418 418 418) },{ target := 7, region := (rows 511 2 511 8 16 511 511 0 511), good := (rows 357 359 357 365 373 357 357 357 357) }] }

theorem profile2_node41 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,33] 6 450 profile2_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,33] 6 450 profile2_node41_cert).mp (by decide +kernel))

def profile2_node42_cert : CutBound 9 := { lost := (rows 128 96 192 32 32 0 0 0 0), upper := (rows 97 386 38 457 465 32 64 128 256), lower := (rows 97 386 38 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 4 9 17 0 511 511 511), good := (rows 475 450 454 458 466 450 450 450 450) },{ target := 6, region := (rows 1 511 511 8 16 511 0 511 511), good := (rows 423 422 422 430 438 422 422 422 422) },{ target := 7, region := (rows 511 2 6 8 16 511 511 0 511), good := (rows 353 359 359 361 369 353 353 353 353) }] }

theorem profile2_node42 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,34] 6 449 profile2_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,34] 6 449 profile2_node42_cert).mp (by decide +kernel))

def profile2_node43_cert : CutBound 9 := { lost := (rows 0 96 0 96 96 0 0 0 0), upper := (rows 97 386 100 395 403 32 64 128 256), lower := (rows 97 386 100 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 4 9 17 0 511 511 511), good := (rows 475 450 454 458 466 450 450 450 450) },{ target := 6, region := (rows 1 511 4 9 17 511 0 511 511), good := (rows 443 418 422 426 434 418 418 418 418) }] }

theorem profile2_node43 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,96] 6 387 profile2_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,96] 6 387 profile2_node43_cert).mp (by decide +kernel))

def profile2_node44_cert : CutBound 9 := { lost := (rows 128 96 96 128 128 0 0 0 0), upper := (rows 97 386 133 362 370 32 64 128 256), lower := (rows 97 386 133 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 5 8 16 0 511 511 511), good := (rows 455 450 455 458 466 450 450 450 450) },{ target := 6, region := (rows 1 511 5 8 16 511 0 511 511), good := (rows 423 418 423 426 434 418 418 418 418) },{ target := 7, region := (rows 511 2 4 10 18 511 511 0 511), good := (rows 353 379 357 361 369 353 353 353 353) }] }

theorem profile2_node44 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,129] 6 354 profile2_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,129] 6 354 profile2_node44_cert).mp (by decide +kernel))

def profile2_node45_cert : CutBound 9 := { lost := (rows 128 96 96 128 128 0 0 0 0), upper := (rows 97 386 134 361 369 32 64 128 256), lower := (rows 97 386 134 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 511 8 16 0 511 511 511), good := (rows 455 454 454 462 470 454 454 454 454) },{ target := 6, region := (rows 1 511 511 8 16 511 0 511 511), good := (rows 423 422 422 430 438 422 422 422 422) },{ target := 7, region := (rows 511 2 4 511 511 511 511 0 511), good := (rows 377 379 383 377 377 377 377 377 377) }] }

theorem profile2_node45 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,130] 6 353 profile2_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,130] 6 353 profile2_node45_cert).mp (by decide +kernel))

def profile2_node46_cert : CutBound 9 := { lost := (rows 128 96 64 160 160 0 0 0 0), upper := (rows 97 386 164 331 339 32 64 128 256), lower := (rows 97 386 164 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 4 9 17 0 511 511 511), good := (rows 475 450 454 458 466 450 450 450 450) },{ target := 6, region := (rows 1 511 511 8 16 511 0 511 511), good := (rows 423 422 422 430 438 422 422 422 422) },{ target := 7, region := (rows 511 2 4 10 18 511 511 0 511), good := (rows 353 379 357 361 369 353 353 353 353) }] }

theorem profile2_node46 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,160] 6 323 profile2_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,160] 6 323 profile2_node46_cert).mp (by decide +kernel))

def profile2_node47_cert : CutBound 9 := { lost := (rows 128 96 96 128 128 0 0 0 0), upper := (rows 97 386 388 107 115 32 64 128 256), lower := (rows 97 386 388 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 511 8 16 0 511 511 511), good := (rows 455 454 454 462 470 454 454 454 454) },{ target := 6, region := (rows 1 511 511 8 16 511 0 511 511), good := (rows 423 422 422 430 438 422 422 422 422) },{ target := 7, region := (rows 511 2 4 10 18 511 511 0 511), good := (rows 353 379 357 361 369 353 353 353 353) }] }

theorem profile2_node47 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,384] 6 99 profile2_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384,384] 6 99 profile2_node47_cert).mp (by decide +kernel))

def profile2_node39_column : Nat → Fin 9 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile2_node39_route : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile2_node39 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96,384] 6 (by decide) (choices 2) [3,33,34,96,129,130,160,384] profile2_node39_route profile2_node39_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node40
  · exact profile2_node41
  · exact profile2_node42
  · exact profile2_node43
  · exact profile2_node44
  · exact profile2_node45
  · exact profile2_node46
  · exact profile2_node47

def profile2_node13_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile2_node13_route : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile2_node13 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [96] 6 (by decide) (choices 2) [33,96,129,160,384] profile2_node13_route profile2_node13_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile2_node14
  · exact profile2_node15
  · exact profile2_node20
  · exact profile2_node28
  · exact profile2_node39

def profile2_node0_column : Nat → Fin 9 := fun mask => match mask with | 6 => 2 | 10 => 3 | 18 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile2_node0_route : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 258 => (34,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (96,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 384 => (96,(fun i => match i.val with | 5 => 7 | 6 => 8 | 7 => 5 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile2_node0 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [] 6 (by decide) (choices 2) [34,96] profile2_node0_route profile2_node0_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile2_node1
  · exact profile2_node13

theorem profile2 : Upper (D (n:=9) [33,33,32,32,32,2,2,2,2]) (R (n:=9) [33,33,32,32,32,2,2,2,2]) [] 6 := profile2_node0


#print axioms profile2
end Delivery.SmallBudgetTenFinite9
