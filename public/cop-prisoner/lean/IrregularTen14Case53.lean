import IrregularTen14Base

namespace Delivery.IrregularTen14.Case53
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 530 7 44 248 232 232 232 488 744), lower := (rows 273 530 7 44 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [272,528,3,36] 13 :=
  bound_sound D R [272,528,3,36] 13 bound_2
    ((Boolean.boundCheck_true D R [272,528,3,36] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 273 530 7 104 252 236 236 236 492 748), lower := (rows 273 530 7 104 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [272,528,3,96] 13 :=
  bound_sound D R [272,528,3,96] 13 bound_3
    ((Boolean.boundCheck_true D R [272,528,3,96] 13 bound_3).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [272,528,3] 13 := by
  apply routed_branch D R [272,528,3] 13 (by decide) (choices 2) [36,96] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,528,3] (choices 2) [36,96] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_2
  · exact upper_3

def bound_8 : Bound 10 := { allowed := (rows 192 192 208 208 0 0 0 0 0 0), upper := (rows 273 530 13 14 48 96 96 192 448 704), lower := (rows 273 530 13 14 48 96 96 128 256 512), losses := [{ target := 5, region := (rows 17 18 23 27 16 0 64 224 352 608), good := (rows 287 543 13 14 927 960 960 128 256 512) }] }

theorem upper_8 : Upper D R [272,528,9,6,32,64,32] 13 :=
  bound_sound D R [272,528,9,6,32,64,32] 13 bound_8
    ((Boolean.boundCheck_true D R [272,528,9,6,32,64,32] 13 bound_8).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 192 224 208 208 0 0 0 0 0 0), upper := (rows 273 530 13 14 48 96 192 160 320 640), lower := (rows 273 530 13 14 48 96 192 160 320 512), losses := [{ target := 5, region := (rows 17 2 6 10 16 0 192 128 480 704), good := (rows 273 543 13 14 273 832 960 960 832 512) }] }

theorem upper_11 : Upper D R [272,528,9,6,32,64,128,32,64] 13 :=
  bound_sound D R [272,528,9,6,32,64,128,32,64] 13 bound_11
    ((Boolean.boundCheck_true D R [272,528,9,6,32,64,128,32,64] 13 bound_11).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 192 208 208 0 0 0 0 0 0), upper := (rows 273 530 13 14 48 96 192 160 384 576), lower := (rows 273 530 13 14 48 96 192 160 384 512), losses := [{ target := 5, region := (rows 1 19 5 13 16 0 448 128 448 993), good := (rows 863 530 527 14 530 832 960 960 960 512) }] }

theorem upper_12 : Upper D R [272,528,9,6,32,64,128,32,128] 13 :=
  bound_sound D R [272,528,9,6,32,64,128,32,128] 13 bound_12
    ((Boolean.boundCheck_true D R [272,528,9,6,32,64,128,32,128] 13 bound_12).mp (by decide +kernel))

def route_10 : Route 10 := (fun mask => (mask,id))

theorem upper_10 : Upper D R [272,528,9,6,32,64,128,32] 13 := by
  apply routed_branch D R [272,528,9,6,32,64,128,32] 13 (by decide) (choices 1) [64,128] route_10
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,528,9,6,32,64,128,32] (choices 1) [64,128] route_10).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_11
  · exact upper_12

def bound_14 : Bound 10 := { allowed := (rows 224 192 208 208 0 0 0 0 0 0), upper := (rows 273 530 13 14 48 96 192 192 288 640), lower := (rows 273 530 13 14 48 96 192 192 288 512), losses := [{ target := 5, region := (rows 1 19 5 13 16 0 1023 1023 256 1023), good := (rows 991 722 719 718 722 704 704 704 960 704) }] }

theorem upper_14 : Upper D R [272,528,9,6,32,64,128,64,32] 13 :=
  bound_sound D R [272,528,9,6,32,64,128,64,32] 13 bound_14
    ((Boolean.boundCheck_true D R [272,528,9,6,32,64,128,64,32] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 192 224 208 208 0 0 0 0 0 0), upper := (rows 273 530 13 14 48 96 192 192 384 544), lower := (rows 273 530 13 14 48 96 192 192 384 512), losses := [{ target := 5, region := (rows 19 2 14 10 16 0 1023 1023 1023 512), good := (rows 465 991 461 463 465 448 448 448 448 960) }] }

theorem upper_15 : Upper D R [272,528,9,6,32,64,128,64,128] 13 :=
  bound_sound D R [272,528,9,6,32,64,128,64,128] 13 bound_15
    ((Boolean.boundCheck_true D R [272,528,9,6,32,64,128,64,128] 13 bound_15).mp (by decide +kernel))

def route_13 : Route 10 := (fun mask => (mask,id))

theorem upper_13 : Upper D R [272,528,9,6,32,64,128,64] 13 := by
  apply routed_branch D R [272,528,9,6,32,64,128,64] 13 (by decide) (choices 1) [32,128] route_13
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,528,9,6,32,64,128,64] (choices 1) [32,128] route_13).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_14
  · exact upper_15

def route_9 : Route 10 := (fun mask => (mask,id))

theorem upper_9 : Upper D R [272,528,9,6,32,64,128] 13 := by
  apply routed_branch D R [272,528,9,6,32,64,128] 13 (by decide) (choices 1) [32,64] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,528,9,6,32,64,128] (choices 1) [32,64] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_10
  · exact upper_13

def route_7 : Route 10 := (fun mask => (mask,id))

theorem upper_7 : Upper D R [272,528,9,6,32,64] 13 := by
  apply routed_branch D R [272,528,9,6,32,64] 13 (by decide) (choices 1) [32,128] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,528,9,6,32,64] (choices 1) [32,128] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_8
  · exact upper_9

def route_6 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_6 : Upper D R [272,528,9,6,32] 13 := by
  apply routed_branch D R [272,528,9,6,32] 13 (by decide) (choices 1) [64] route_6
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,528,9,6,32] (choices 1) [64] route_6).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_7

def route_5 : Route 10 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 128 => (32,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_5 : Upper D R [272,528,9,6] 13 := by
  apply routed_branch D R [272,528,9,6] 13 (by decide) (choices 1) [32] route_5
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,528,9,6] (choices 1) [32] route_5).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_6

def bound_16 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 530 13 42 244 228 228 228 484 740), lower := (rows 273 530 13 42 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [272,528,9,34] 13 :=
  bound_sound D R [272,528,9,34] 13 bound_16
    ((Boolean.boundCheck_true D R [272,528,9,34] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 530 13 44 242 226 226 226 482 738), lower := (rows 273 530 13 44 16 32 64 128 256 512), losses := [] }

theorem upper_17 : Upper D R [272,528,9,36] 13 :=
  bound_sound D R [272,528,9,36] 13 bound_17
    ((Boolean.boundCheck_true D R [272,528,9,36] 13 bound_17).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 273 530 13 104 246 230 230 230 486 742), lower := (rows 273 530 13 104 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [272,528,9,96] 13 :=
  bound_sound D R [272,528,9,96] 13 bound_18
    ((Boolean.boundCheck_true D R [272,528,9,96] 13 bound_18).mp (by decide +kernel))

def route_4 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_4 : Upper D R [272,528,9] 13 := by
  apply routed_branch D R [272,528,9] 13 (by decide) (choices 2) [6,34,36,96] route_4
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,528,9] (choices 2) [6,34,36,96] route_4).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_5
  · exact upper_16
  · exact upper_17
  · exact upper_18

def bound_23 : Bound 10 := { allowed := (rows 192 192 208 208 0 0 0 0 0 0), upper := (rows 273 530 14 13 48 96 96 192 448 704), lower := (rows 273 530 14 13 48 96 96 128 256 512), losses := [{ target := 5, region := (rows 17 18 23 27 16 0 64 224 352 608), good := (rows 287 543 14 13 927 960 960 128 256 512) }] }

theorem upper_23 : Upper D R [272,528,10,5,32,64,32] 13 :=
  bound_sound D R [272,528,10,5,32,64,32] 13 bound_23
    ((Boolean.boundCheck_true D R [272,528,10,5,32,64,32] 13 bound_23).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 192 224 208 208 0 0 0 0 0 0), upper := (rows 273 530 14 13 48 96 192 160 320 640), lower := (rows 273 530 14 13 48 96 192 160 320 512), losses := [{ target := 5, region := (rows 17 2 6 10 16 0 192 128 480 704), good := (rows 273 543 14 13 273 832 960 960 832 512) }] }

theorem upper_26 : Upper D R [272,528,10,5,32,64,128,32,64] 13 :=
  bound_sound D R [272,528,10,5,32,64,128,32,64] 13 bound_26
    ((Boolean.boundCheck_true D R [272,528,10,5,32,64,128,32,64] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 224 192 208 208 0 0 0 0 0 0), upper := (rows 273 530 14 13 48 96 192 160 384 576), lower := (rows 273 530 14 13 48 96 192 160 384 512), losses := [{ target := 5, region := (rows 1 19 13 9 16 0 448 128 448 993), good := (rows 863 530 14 527 530 832 960 960 960 512) }] }

theorem upper_27 : Upper D R [272,528,10,5,32,64,128,32,128] 13 :=
  bound_sound D R [272,528,10,5,32,64,128,32,128] 13 bound_27
    ((Boolean.boundCheck_true D R [272,528,10,5,32,64,128,32,128] 13 bound_27).mp (by decide +kernel))

def route_25 : Route 10 := (fun mask => (mask,id))

theorem upper_25 : Upper D R [272,528,10,5,32,64,128,32] 13 := by
  apply routed_branch D R [272,528,10,5,32,64,128,32] 13 (by decide) (choices 1) [64,128] route_25
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,528,10,5,32,64,128,32] (choices 1) [64,128] route_25).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_26
  · exact upper_27

def bound_29 : Bound 10 := { allowed := (rows 224 192 208 208 0 0 0 0 0 0), upper := (rows 273 530 14 13 48 96 192 192 288 640), lower := (rows 273 530 14 13 48 96 192 192 288 512), losses := [{ target := 5, region := (rows 1 19 13 9 16 0 1023 1023 256 1023), good := (rows 991 722 718 719 722 704 704 704 960 704) }] }

theorem upper_29 : Upper D R [272,528,10,5,32,64,128,64,32] 13 :=
  bound_sound D R [272,528,10,5,32,64,128,64,32] 13 bound_29
    ((Boolean.boundCheck_true D R [272,528,10,5,32,64,128,64,32] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 192 224 208 208 0 0 0 0 0 0), upper := (rows 273 530 14 13 48 96 192 192 384 544), lower := (rows 273 530 14 13 48 96 192 192 384 512), losses := [{ target := 5, region := (rows 19 2 6 14 16 0 1023 1023 1023 512), good := (rows 465 991 463 461 465 448 448 448 448 960) }] }

theorem upper_30 : Upper D R [272,528,10,5,32,64,128,64,128] 13 :=
  bound_sound D R [272,528,10,5,32,64,128,64,128] 13 bound_30
    ((Boolean.boundCheck_true D R [272,528,10,5,32,64,128,64,128] 13 bound_30).mp (by decide +kernel))

def route_28 : Route 10 := (fun mask => (mask,id))

theorem upper_28 : Upper D R [272,528,10,5,32,64,128,64] 13 := by
  apply routed_branch D R [272,528,10,5,32,64,128,64] 13 (by decide) (choices 1) [32,128] route_28
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,528,10,5,32,64,128,64] (choices 1) [32,128] route_28).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_29
  · exact upper_30

def route_24 : Route 10 := (fun mask => (mask,id))

theorem upper_24 : Upper D R [272,528,10,5,32,64,128] 13 := by
  apply routed_branch D R [272,528,10,5,32,64,128] 13 (by decide) (choices 1) [32,64] route_24
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,528,10,5,32,64,128] (choices 1) [32,64] route_24).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_25
  · exact upper_28

def route_22 : Route 10 := (fun mask => (mask,id))

theorem upper_22 : Upper D R [272,528,10,5,32,64] 13 := by
  apply routed_branch D R [272,528,10,5,32,64] 13 (by decide) (choices 1) [32,128] route_22
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,528,10,5,32,64] (choices 1) [32,128] route_22).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_23
  · exact upper_24

def route_21 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_21 : Upper D R [272,528,10,5,32] 13 := by
  apply routed_branch D R [272,528,10,5,32] 13 (by decide) (choices 1) [64] route_21
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,528,10,5,32] (choices 1) [64] route_21).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_22

def route_20 : Route 10 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 128 => (32,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_20 : Upper D R [272,528,10,5] 13 := by
  apply routed_branch D R [272,528,10,5] 13 (by decide) (choices 1) [32] route_20
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,528,10,5] (choices 1) [32] route_20).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_21

def bound_31 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 530 14 41 244 228 228 228 484 740), lower := (rows 273 530 14 41 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [272,528,10,33] 13 :=
  bound_sound D R [272,528,10,33] 13 bound_31
    ((Boolean.boundCheck_true D R [272,528,10,33] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 530 14 44 241 225 225 225 481 737), lower := (rows 273 530 14 44 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [272,528,10,36] 13 :=
  bound_sound D R [272,528,10,36] 13 bound_32
    ((Boolean.boundCheck_true D R [272,528,10,36] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 273 530 14 104 245 229 229 229 485 741), lower := (rows 273 530 14 104 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [272,528,10,96] 13 :=
  bound_sound D R [272,528,10,96] 13 bound_33
    ((Boolean.boundCheck_true D R [272,528,10,96] 13 bound_33).mp (by decide +kernel))

def route_19 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_19 : Upper D R [272,528,10] 13 := by
  apply routed_branch D R [272,528,10] 13 (by decide) (choices 2) [5,33,36,96] route_19
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,528,10] (choices 2) [5,33,36,96] route_19).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_20
  · exact upper_31
  · exact upper_32
  · exact upper_33

def bound_34 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 273 530 37 238 254 238 238 238 494 750), lower := (rows 273 530 37 8 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [272,528,33] 13 :=
  bound_sound D R [272,528,33] 13 bound_34
    ((Boolean.boundCheck_true D R [272,528,33] 13 bound_34).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 273 530 38 237 253 237 237 237 493 749), lower := (rows 273 530 38 8 16 32 64 128 256 512), losses := [] }

theorem upper_35 : Upper D R [272,528,34] 13 :=
  bound_sound D R [272,528,34] 13 bound_35
    ((Boolean.boundCheck_true D R [272,528,34] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 273 530 44 239 247 231 231 231 487 743), lower := (rows 273 530 44 8 16 32 64 128 256 512), losses := [] }

theorem upper_36 : Upper D R [272,528,40] 13 :=
  bound_sound D R [272,528,40] 13 bound_36
    ((Boolean.boundCheck_true D R [272,528,40] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 224 224 144 240 0 0 0 0 0 0), upper := (rows 273 530 100 239 255 239 239 239 495 751), lower := (rows 273 530 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_37 : Upper D R [272,528,96] 13 :=
  bound_sound D R [272,528,96] 13 bound_37
    ((Boolean.boundCheck_true D R [272,528,96] 13 bound_37).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [272,528] 13 := by
  apply routed_branch D R [272,528] 13 (by decide) (choices 2) [3,9,10,33,34,40,96] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,528] (choices 2) [3,9,10,33,34,40,96] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_4
  · exact upper_19
  · exact upper_34
  · exact upper_35
  · exact upper_36
  · exact upper_37

theorem upper : Upper D R [272,528] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case53
