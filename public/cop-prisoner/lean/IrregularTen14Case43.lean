import IrregularTen14Base

namespace Delivery.IrregularTen14.Case43
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 7 14 56 752 736 736 736 992 736), lower := (rows 273 7 14 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [272,5,10,48] 13 :=
  bound_sound D R [272,5,10,48] 13 bound_2
    ((Boolean.boundCheck_true D R [272,5,10,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 273 7 14 104 752 752 752 752 1008 752), lower := (rows 273 7 14 104 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [272,5,10,96] 13 :=
  bound_sound D R [272,5,10,96] 13 bound_3
    ((Boolean.boundCheck_true D R [272,5,10,96] 13 bound_3).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 192 208 208 192 0 0 0 0 0 0), upper := (rows 273 7 14 536 48 96 96 192 448 704), lower := (rows 273 7 14 536 48 96 96 128 256 512), losses := [{ target := 5, region := (rows 17 27 29 24 16 0 64 224 352 608), good := (rows 287 7 14 543 927 960 960 128 256 512) }] }

theorem upper_7 : Upper D R [272,5,10,528,32,64,32] 13 :=
  bound_sound D R [272,5,10,528,32,64,32] 13 bound_7
    ((Boolean.boundCheck_true D R [272,5,10,528,32,64,32] 13 bound_7).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 192 208 208 224 0 0 0 0 0 0), upper := (rows 273 7 14 536 48 96 192 160 320 640), lower := (rows 273 7 14 536 48 96 192 160 320 512), losses := [{ target := 5, region := (rows 17 10 12 8 16 0 192 128 480 704), good := (rows 273 7 14 543 273 832 960 960 832 512) }] }

theorem upper_10 : Upper D R [272,5,10,528,32,64,128,32,64] 13 :=
  bound_sound D R [272,5,10,528,32,64,128,32,64] 13 bound_10
    ((Boolean.boundCheck_true D R [272,5,10,528,32,64,128,32,64] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 224 208 208 192 0 0 0 0 0 0), upper := (rows 273 7 14 536 48 96 192 160 384 576), lower := (rows 273 7 14 536 48 96 192 160 384 512), losses := [{ target := 5, region := (rows 1 3 7 25 16 0 448 128 448 993), good := (rows 863 527 14 536 536 832 960 960 960 512) }] }

theorem upper_11 : Upper D R [272,5,10,528,32,64,128,32,128] 13 :=
  bound_sound D R [272,5,10,528,32,64,128,32,128] 13 bound_11
    ((Boolean.boundCheck_true D R [272,5,10,528,32,64,128,32,128] 13 bound_11).mp (by decide +kernel))

def route_9 : Route 10 := (fun mask => (mask,id))

theorem upper_9 : Upper D R [272,5,10,528,32,64,128,32] 13 := by
  apply routed_branch D R [272,5,10,528,32,64,128,32] 13 (by decide) (choices 1) [64,128] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,10,528,32,64,128,32] (choices 1) [64,128] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_10
  · exact upper_11

def bound_13 : Bound 10 := { allowed := (rows 224 208 208 192 0 0 0 0 0 0), upper := (rows 273 7 14 536 48 96 192 192 288 640), lower := (rows 273 7 14 536 48 96 192 192 288 512), losses := [{ target := 5, region := (rows 1 3 7 25 16 0 1023 1023 256 1023), good := (rows 991 719 718 728 728 704 704 704 960 704) }] }

theorem upper_13 : Upper D R [272,5,10,528,32,64,128,64,32] 13 :=
  bound_sound D R [272,5,10,528,32,64,128,64,32] 13 bound_13
    ((Boolean.boundCheck_true D R [272,5,10,528,32,64,128,64,32] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 192 208 208 224 0 0 0 0 0 0), upper := (rows 273 7 14 536 48 96 192 192 384 544), lower := (rows 273 7 14 536 48 96 192 192 384 512), losses := [{ target := 5, region := (rows 25 14 12 8 16 0 1023 1023 1023 512), good := (rows 465 455 463 991 465 448 448 448 448 960) }] }

theorem upper_14 : Upper D R [272,5,10,528,32,64,128,64,128] 13 :=
  bound_sound D R [272,5,10,528,32,64,128,64,128] 13 bound_14
    ((Boolean.boundCheck_true D R [272,5,10,528,32,64,128,64,128] 13 bound_14).mp (by decide +kernel))

def route_12 : Route 10 := (fun mask => (mask,id))

theorem upper_12 : Upper D R [272,5,10,528,32,64,128,64] 13 := by
  apply routed_branch D R [272,5,10,528,32,64,128,64] 13 (by decide) (choices 1) [32,128] route_12
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,10,528,32,64,128,64] (choices 1) [32,128] route_12).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_13
  · exact upper_14

def route_8 : Route 10 := (fun mask => (mask,id))

theorem upper_8 : Upper D R [272,5,10,528,32,64,128] 13 := by
  apply routed_branch D R [272,5,10,528,32,64,128] 13 (by decide) (choices 1) [32,64] route_8
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,10,528,32,64,128] (choices 1) [32,64] route_8).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_9
  · exact upper_12

def route_6 : Route 10 := (fun mask => (mask,id))

theorem upper_6 : Upper D R [272,5,10,528,32,64] 13 := by
  apply routed_branch D R [272,5,10,528,32,64] 13 (by decide) (choices 1) [32,128] route_6
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,10,528,32,64] (choices 1) [32,128] route_6).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_7
  · exact upper_8

def route_5 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_5 : Upper D R [272,5,10,528,32] 13 := by
  apply routed_branch D R [272,5,10,528,32] 13 (by decide) (choices 1) [64] route_5
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,10,528,32] (choices 1) [64] route_5).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_6

def route_4 : Route 10 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 128 => (32,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_4 : Upper D R [272,5,10,528] 13 := by
  apply routed_branch D R [272,5,10,528] 13 (by decide) (choices 1) [32] route_4
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,10,528] (choices 1) [32] route_4).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_5

def bound_16 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 273 7 14 552 48 240 208 208 464 720), lower := (rows 273 7 14 552 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 4 8 16 0 81 145 273 529), good := (rows 977 967 14 520 977 0 64 128 256 512) }] }

theorem upper_16 : Upper D R [272,5,10,544,32] 13 :=
  bound_sound D R [272,5,10,544,32] 13 bound_16
    ((Boolean.boundCheck_true D R [272,5,10,544,32] 13 bound_16).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 7 14 552 80 48 224 224 480 736), lower := (rows 273 7 14 552 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 40 0 32 104 168 296 552), good := (rows 257 7 974 1000 64 1000 64 128 256 512) }] }

theorem upper_18 : Upper D R [272,5,10,544,64,16] 13 :=
  bound_sound D R [272,5,10,544,64,16] 13 bound_18
    ((Boolean.boundCheck_true D R [272,5,10,544,64,16] 13 bound_18).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 7 14 552 80 96 80 160 416 672), lower := (rows 273 7 14 552 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 7 121 0 112 64 249 377 633), good := (rows 943 911 910 936 1000 1000 1000 128 256 512) }] }

theorem upper_20 : Upper D R [272,5,10,544,64,64,16] 13 :=
  bound_sound D R [272,5,10,544,64,64,16] 13 bound_20
    ((Boolean.boundCheck_true D R [272,5,10,544,64,64,16] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 7 14 552 80 96 96 144 400 656), lower := (rows 273 7 14 552 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 128 256 512), good := (rows 353 103 110 616 96 96 96 224 352 616) }] }

theorem upper_21 : Upper D R [272,5,10,544,64,64,32] 13 :=
  bound_sound D R [272,5,10,544,64,64,32] 13 bound_21
    ((Boolean.boundCheck_true D R [272,5,10,544,64,64,32] 13 bound_21).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 7 14 552 80 96 192 144 416 672), lower := (rows 273 7 14 552 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 1 3 5 248 0 240 192 128 448 704), good := (rows 303 7 14 552 872 872 1000 1000 256 512) }] }

theorem upper_23 : Upper D R [272,5,10,544,64,64,128,16] 13 :=
  bound_sound D R [272,5,10,544,64,64,128,16] 13 bound_23
    ((Boolean.boundCheck_true D R [272,5,10,544,64,64,128,16] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 7 14 552 80 96 192 160 400 656), lower := (rows 273 7 14 552 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 481 231 238 744 224 224 224 224 480 744) }] }

theorem upper_24 : Upper D R [272,5,10,544,64,64,128,32] 13 :=
  bound_sound D R [272,5,10,544,64,64,128,32] 13 bound_24
    ((Boolean.boundCheck_true D R [272,5,10,544,64,64,128,32] 13 bound_24).mp (by decide +kernel))

def route_22 : Route 10 := (fun mask => (mask,id))

theorem upper_22 : Upper D R [272,5,10,544,64,64,128] 13 := by
  apply routed_branch D R [272,5,10,544,64,64,128] 13 (by decide) (choices 1) [16,32] route_22
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,10,544,64,64,128] (choices 1) [16,32] route_22).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_23
  · exact upper_24

def route_19 : Route 10 := (fun mask => (mask,id))

theorem upper_19 : Upper D R [272,5,10,544,64,64] 13 := by
  apply routed_branch D R [272,5,10,544,64,64] 13 (by decide) (choices 1) [16,32,128] route_19
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,10,544,64,64] (choices 1) [16,32,128] route_19).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_20
  · exact upper_21
  · exact upper_22

def bound_26 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 7 14 552 80 160 80 224 480 736), lower := (rows 273 7 14 552 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 7 89 0 241 64 208 336 592), good := (rows 943 47 14 552 1000 160 1000 160 256 512) }] }

theorem upper_26 : Upper D R [272,5,10,544,64,128,16] 13 :=
  bound_sound D R [272,5,10,544,64,128,16] 13 bound_26
    ((Boolean.boundCheck_true D R [272,5,10,544,64,128,16] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 273 7 14 552 80 160 96 208 464 720), lower := (rows 273 7 14 552 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 7 14 520 977 128 977 128 256 512) }] }

theorem upper_27 : Upper D R [272,5,10,544,64,128,32] 13 :=
  bound_sound D R [272,5,10,544,64,128,32] 13 bound_27
    ((Boolean.boundCheck_true D R [272,5,10,544,64,128,32] 13 bound_27).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 7 14 552 80 160 192 144 352 608), lower := (rows 273 7 14 552 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 3 5 248 0 224 224 128 504 760), good := (rows 783 7 782 872 872 1000 1000 1000 256 512) }] }

theorem upper_29 : Upper D R [272,5,10,544,64,128,128,16] 13 :=
  bound_sound D R [272,5,10,544,64,128,128,16] 13 bound_29
    ((Boolean.boundCheck_true D R [272,5,10,544,64,128,128,16] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 7 14 552 80 160 192 160 336 592), lower := (rows 273 7 14 552 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 481 231 238 744 224 224 224 224 480 744) }] }

theorem upper_30 : Upper D R [272,5,10,544,64,128,128,32] 13 :=
  bound_sound D R [272,5,10,544,64,128,128,32] 13 bound_30
    ((Boolean.boundCheck_true D R [272,5,10,544,64,128,128,32] 13 bound_30).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 7 14 552 80 160 192 192 304 560), lower := (rows 273 7 14 552 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 481 231 238 744 224 224 224 224 480 744) }] }

theorem upper_31 : Upper D R [272,5,10,544,64,128,128,64] 13 :=
  bound_sound D R [272,5,10,544,64,128,128,64] 13 bound_31
    ((Boolean.boundCheck_true D R [272,5,10,544,64,128,128,64] 13 bound_31).mp (by decide +kernel))

def route_28 : Route 10 := (fun mask => (mask,id))

theorem upper_28 : Upper D R [272,5,10,544,64,128,128] 13 := by
  apply routed_branch D R [272,5,10,544,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_28
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,10,544,64,128,128] (choices 1) [16,32,64] route_28).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_29
  · exact upper_30
  · exact upper_31

def route_25 : Route 10 := (fun mask => (mask,id))

theorem upper_25 : Upper D R [272,5,10,544,64,128] 13 := by
  apply routed_branch D R [272,5,10,544,64,128] 13 (by decide) (choices 1) [16,32,128] route_25
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,10,544,64,128] (choices 1) [16,32,128] route_25).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_26
  · exact upper_27
  · exact upper_28

def route_17 : Route 10 := (fun mask => (mask,id))

theorem upper_17 : Upper D R [272,5,10,544,64] 13 := by
  apply routed_branch D R [272,5,10,544,64] 13 (by decide) (choices 1) [16,64,128] route_17
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,10,544,64] (choices 1) [16,64,128] route_17).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_18
  · exact upper_19
  · exact upper_25

def route_15 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_15 : Upper D R [272,5,10,544] 13 := by
  apply routed_branch D R [272,5,10,544] 13 (by decide) (choices 1) [32,64] route_15
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,10,544] (choices 1) [32,64] route_15).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_16
  · exact upper_17

def route_1 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [272,5,10] 13 := by
  apply routed_branch D R [272,5,10] 13 (by decide) (choices 2) [48,96,528,544] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,5,10] (choices 2) [48,96,528,544] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_15

def bound_33 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 273 7 22 104 760 744 744 744 1000 744), lower := (rows 273 7 22 104 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [272,5,18,96] 13 :=
  bound_sound D R [272,5,18,96] 13 bound_33
    ((Boolean.boundCheck_true D R [272,5,18,96] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 7 22 552 248 232 232 232 488 744), lower := (rows 273 7 22 552 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [272,5,18,544] 13 :=
  bound_sound D R [272,5,18,544] 13 bound_34
    ((Boolean.boundCheck_true D R [272,5,18,544] 13 bound_34).mp (by decide +kernel))

def route_32 : Route 10 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_32 : Upper D R [272,5,18] 13 := by
  apply routed_branch D R [272,5,18] 13 (by decide) (choices 2) [96,544] route_32
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,5,18] (choices 2) [96,544] route_32).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_33
  · exact upper_34

def bound_36 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 7 28 42 752 736 736 736 992 736), lower := (rows 273 7 28 42 16 32 64 128 256 512), losses := [] }

theorem upper_36 : Upper D R [272,5,24,34] 13 :=
  bound_sound D R [272,5,24,34] 13 bound_36
    ((Boolean.boundCheck_true D R [272,5,24,34] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 273 7 28 104 754 738 738 738 994 738), lower := (rows 273 7 28 104 16 32 64 128 256 512), losses := [] }

theorem upper_37 : Upper D R [272,5,24,96] 13 :=
  bound_sound D R [272,5,24,96] 13 bound_37
    ((Boolean.boundCheck_true D R [272,5,24,96] 13 bound_37).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 224 240 224 224 0 0 0 0 0 0), upper := (rows 273 7 28 522 240 224 224 224 480 736), lower := (rows 273 7 28 522 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 1023 1023 1023 1023 1023), good := (rows 993 1007 1004 1002 992 992 992 992 992 992) }] }

theorem upper_38 : Upper D R [272,5,24,514] 13 :=
  bound_sound D R [272,5,24,514] 13 bound_38
    ((Boolean.boundCheck_true D R [272,5,24,514] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 7 28 552 242 226 226 226 482 738), lower := (rows 273 7 28 552 16 32 64 128 256 512), losses := [] }

theorem upper_39 : Upper D R [272,5,24,544] 13 :=
  bound_sound D R [272,5,24,544] 13 bound_39
    ((Boolean.boundCheck_true D R [272,5,24,544] 13 bound_39).mp (by decide +kernel))

def route_35 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_35 : Upper D R [272,5,24] 13 := by
  apply routed_branch D R [272,5,24] 13 (by decide) (choices 2) [34,96,514,544] route_35
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,5,24] (choices 2) [34,96,514,544] route_35).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_36
  · exact upper_37
  · exact upper_38
  · exact upper_39

def bound_41 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 273 7 38 56 728 744 712 712 968 712), lower := (rows 273 7 38 56 16 32 64 128 256 512), losses := [] }

theorem upper_41 : Upper D R [272,5,34,48] 13 :=
  bound_sound D R [272,5,34,48] 13 bound_41
    ((Boolean.boundCheck_true D R [272,5,34,48] 13 bound_41).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 273 7 38 88 760 744 744 744 1000 744), lower := (rows 273 7 38 88 16 32 64 128 256 512), losses := [] }

theorem upper_42 : Upper D R [272,5,34,80] 13 :=
  bound_sound D R [272,5,34,80] 13 bound_42
    ((Boolean.boundCheck_true D R [272,5,34,80] 13 bound_42).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 273 7 38 104 728 760 728 728 984 728), lower := (rows 273 7 38 104 16 32 64 128 256 512), losses := [] }

theorem upper_43 : Upper D R [272,5,34,96] 13 :=
  bound_sound D R [272,5,34,96] 13 bound_43
    ((Boolean.boundCheck_true D R [272,5,34,96] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 273 7 38 200 760 760 760 760 1016 760), lower := (rows 273 7 38 200 16 32 64 128 256 512), losses := [] }

theorem upper_44 : Upper D R [272,5,34,192] 13 :=
  bound_sound D R [272,5,34,192] 13 bound_44
    ((Boolean.boundCheck_true D R [272,5,34,192] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 7 38 536 248 232 232 232 488 744), lower := (rows 273 7 38 536 16 32 64 128 256 512), losses := [] }

theorem upper_45 : Upper D R [272,5,34,528] 13 :=
  bound_sound D R [272,5,34,528] 13 bound_45
    ((Boolean.boundCheck_true D R [272,5,34,528] 13 bound_45).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 7 38 552 216 248 216 216 472 728), lower := (rows 273 7 38 552 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [272,5,34,544] 13 :=
  bound_sound D R [272,5,34,544] 13 bound_46
    ((Boolean.boundCheck_true D R [272,5,34,544] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 7 38 584 248 248 248 248 504 760), lower := (rows 273 7 38 584 16 32 64 128 256 512), losses := [] }

theorem upper_47 : Upper D R [272,5,34,576] 13 :=
  bound_sound D R [272,5,34,576] 13 bound_47
    ((Boolean.boundCheck_true D R [272,5,34,576] 13 bound_47).mp (by decide +kernel))

def route_40 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_40 : Upper D R [272,5,34] 13 := by
  apply routed_branch D R [272,5,34] 13 (by decide) (choices 2) [48,80,96,192,528,544,576] route_40
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,5,34] (choices 2) [48,80,96,192,528,544,576] route_40).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_41
  · exact upper_42
  · exact upper_43
  · exact upper_44
  · exact upper_45
  · exact upper_46
  · exact upper_47

def bound_49 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 7 44 26 752 736 736 736 992 736), lower := (rows 273 7 44 26 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [272,5,40,18] 13 :=
  bound_sound D R [272,5,40,18] 13 bound_49
    ((Boolean.boundCheck_true D R [272,5,40,18] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 7 44 42 720 752 720 720 976 720), lower := (rows 273 7 44 42 16 32 64 128 256 512), losses := [] }

theorem upper_50 : Upper D R [272,5,40,34] 13 :=
  bound_sound D R [272,5,40,34] 13 bound_50
    ((Boolean.boundCheck_true D R [272,5,40,34] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 273 7 44 56 722 738 706 706 962 706), lower := (rows 273 7 44 56 16 32 64 128 256 512), losses := [] }

theorem upper_51 : Upper D R [272,5,40,48] 13 :=
  bound_sound D R [272,5,40,48] 13 bound_51
    ((Boolean.boundCheck_true D R [272,5,40,48] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 7 44 74 752 752 752 752 1008 752), lower := (rows 273 7 44 74 16 32 64 128 256 512), losses := [] }

theorem upper_52 : Upper D R [272,5,40,66] 13 :=
  bound_sound D R [272,5,40,66] 13 bound_52
    ((Boolean.boundCheck_true D R [272,5,40,66] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 273 7 44 88 754 738 738 738 994 738), lower := (rows 273 7 44 88 16 32 64 128 256 512), losses := [] }

theorem upper_53 : Upper D R [272,5,40,80] 13 :=
  bound_sound D R [272,5,40,80] 13 bound_53
    ((Boolean.boundCheck_true D R [272,5,40,80] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 273 7 44 104 722 754 722 722 978 722), lower := (rows 273 7 44 104 16 32 64 128 256 512), losses := [] }

theorem upper_54 : Upper D R [272,5,40,96] 13 :=
  bound_sound D R [272,5,40,96] 13 bound_54
    ((Boolean.boundCheck_true D R [272,5,40,96] 13 bound_54).mp (by decide +kernel))

def bound_55 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 273 7 44 200 754 754 754 754 1010 754), lower := (rows 273 7 44 200 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [272,5,40,192] 13 :=
  bound_sound D R [272,5,40,192] 13 bound_55
    ((Boolean.boundCheck_true D R [272,5,40,192] 13 bound_55).mp (by decide +kernel))

def bound_57 : Bound 10 := { allowed := (rows 192 240 208 208 0 0 0 0 0 0), upper := (rows 273 7 44 522 48 240 208 208 464 720), lower := (rows 273 7 44 522 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 4 10 16 0 81 145 273 529), good := (rows 977 975 12 522 977 0 64 128 256 512) }] }

theorem upper_57 : Upper D R [272,5,40,514,32] 13 :=
  bound_sound D R [272,5,40,514,32] 13 bound_57
    ((Boolean.boundCheck_true D R [272,5,40,514,32] 13 bound_57).mp (by decide +kernel))

def bound_59 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 7 44 522 80 48 224 224 480 736), lower := (rows 273 7 44 522 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 32 100 164 292 548), good := (rows 257 975 1004 522 64 992 64 128 256 512) }] }

theorem upper_59 : Upper D R [272,5,40,514,64,16] 13 :=
  bound_sound D R [272,5,40,514,64,16] 13 bound_59
    ((Boolean.boundCheck_true D R [272,5,40,514,64,16] 13 bound_59).mp (by decide +kernel))

def bound_61 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 273 7 44 522 80 96 80 160 416 672), lower := (rows 273 7 44 522 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 5 11 0 112 64 245 373 629), good := (rows 943 911 940 522 992 992 992 128 256 512) }] }

theorem upper_61 : Upper D R [272,5,40,514,64,64,16] 13 :=
  bound_sound D R [272,5,40,514,64,64,16] 13 bound_61
    ((Boolean.boundCheck_true D R [272,5,40,514,64,64,16] 13 bound_61).mp (by decide +kernel))

def bound_62 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 7 44 522 80 96 96 144 400 656), lower := (rows 273 7 44 522 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 1023 1023 128 256 512), good := (rows 353 103 108 622 96 96 96 224 352 608) }] }

theorem upper_62 : Upper D R [272,5,40,514,64,64,32] 13 :=
  bound_sound D R [272,5,40,514,64,64,32] 13 bound_62
    ((Boolean.boundCheck_true D R [272,5,40,514,64,64,32] 13 bound_62).mp (by decide +kernel))

def bound_64 : Bound 10 := { allowed := (rows 192 240 208 240 0 0 0 0 0 0), upper := (rows 273 7 44 522 80 96 192 144 416 672), lower := (rows 273 7 44 522 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 257 2 4 8 1023 0 1023 1023 256 512), good := (rows 465 215 220 730 208 208 208 208 465 720) }] }

theorem upper_64 : Upper D R [272,5,40,514,64,64,128,16] 13 :=
  bound_sound D R [272,5,40,514,64,64,128,16] 13 bound_64
    ((Boolean.boundCheck_true D R [272,5,40,514,64,64,128,16] 13 bound_64).mp (by decide +kernel))

def bound_65 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 7 44 522 80 96 192 160 400 656), lower := (rows 273 7 44 522 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 1023 1023 1023 256 512), good := (rows 481 231 236 750 224 224 224 224 480 736) }] }

theorem upper_65 : Upper D R [272,5,40,514,64,64,128,32] 13 :=
  bound_sound D R [272,5,40,514,64,64,128,32] 13 bound_65
    ((Boolean.boundCheck_true D R [272,5,40,514,64,64,128,32] 13 bound_65).mp (by decide +kernel))

def route_63 : Route 10 := (fun mask => (mask,id))

theorem upper_63 : Upper D R [272,5,40,514,64,64,128] 13 := by
  apply routed_branch D R [272,5,40,514,64,64,128] 13 (by decide) (choices 1) [16,32] route_63
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,40,514,64,64,128] (choices 1) [16,32] route_63).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_64
  · exact upper_65

def route_60 : Route 10 := (fun mask => (mask,id))

theorem upper_60 : Upper D R [272,5,40,514,64,64] 13 := by
  apply routed_branch D R [272,5,40,514,64,64] 13 (by decide) (choices 1) [16,32,128] route_60
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,40,514,64,64] (choices 1) [16,32,128] route_60).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_61
  · exact upper_62
  · exact upper_63

def bound_67 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 273 7 44 522 80 160 80 224 480 736), lower := (rows 273 7 44 522 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 7 9 0 241 64 208 336 592), good := (rows 943 47 44 526 992 160 992 160 256 512) }] }

theorem upper_67 : Upper D R [272,5,40,514,64,128,16] 13 :=
  bound_sound D R [272,5,40,514,64,128,16] 13 bound_67
    ((Boolean.boundCheck_true D R [272,5,40,514,64,128,16] 13 bound_67).mp (by decide +kernel))

def bound_68 : Bound 10 := { allowed := (rows 192 240 208 240 0 0 0 0 0 0), upper := (rows 273 7 44 522 80 160 96 208 464 720), lower := (rows 273 7 44 522 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 7 12 522 977 128 977 128 256 512) }] }

theorem upper_68 : Upper D R [272,5,40,514,64,128,32] 13 :=
  bound_sound D R [272,5,40,514,64,128,32] 13 bound_68
    ((Boolean.boundCheck_true D R [272,5,40,514,64,128,32] 13 bound_68).mp (by decide +kernel))

def bound_70 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 7 44 522 80 160 192 144 352 608), lower := (rows 273 7 44 522 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 224 224 128 500 756), good := (rows 769 783 876 522 864 992 992 992 256 512) }] }

theorem upper_70 : Upper D R [272,5,40,514,64,128,128,16] 13 :=
  bound_sound D R [272,5,40,514,64,128,128,16] 13 bound_70
    ((Boolean.boundCheck_true D R [272,5,40,514,64,128,128,16] 13 bound_70).mp (by decide +kernel))

def bound_71 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 7 44 522 80 160 192 160 336 592), lower := (rows 273 7 44 522 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 1023 1023 1023 256 512), good := (rows 481 231 236 750 224 224 224 224 480 736) }] }

theorem upper_71 : Upper D R [272,5,40,514,64,128,128,32] 13 :=
  bound_sound D R [272,5,40,514,64,128,128,32] 13 bound_71
    ((Boolean.boundCheck_true D R [272,5,40,514,64,128,128,32] 13 bound_71).mp (by decide +kernel))

def bound_72 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 7 44 522 80 160 192 192 304 560), lower := (rows 273 7 44 522 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 1023 1023 1023 256 512), good := (rows 481 231 236 750 224 224 224 224 480 736) }] }

theorem upper_72 : Upper D R [272,5,40,514,64,128,128,64] 13 :=
  bound_sound D R [272,5,40,514,64,128,128,64] 13 bound_72
    ((Boolean.boundCheck_true D R [272,5,40,514,64,128,128,64] 13 bound_72).mp (by decide +kernel))

def route_69 : Route 10 := (fun mask => (mask,id))

theorem upper_69 : Upper D R [272,5,40,514,64,128,128] 13 := by
  apply routed_branch D R [272,5,40,514,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_69
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,40,514,64,128,128] (choices 1) [16,32,64] route_69).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_70
  · exact upper_71
  · exact upper_72

def route_66 : Route 10 := (fun mask => (mask,id))

theorem upper_66 : Upper D R [272,5,40,514,64,128] 13 := by
  apply routed_branch D R [272,5,40,514,64,128] 13 (by decide) (choices 1) [16,32,128] route_66
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,40,514,64,128] (choices 1) [16,32,128] route_66).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_67
  · exact upper_68
  · exact upper_69

def route_58 : Route 10 := (fun mask => (mask,id))

theorem upper_58 : Upper D R [272,5,40,514,64] 13 := by
  apply routed_branch D R [272,5,40,514,64] 13 (by decide) (choices 1) [16,64,128] route_58
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,40,514,64] (choices 1) [16,64,128] route_58).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_59
  · exact upper_60
  · exact upper_66

def route_56 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_56 : Upper D R [272,5,40,514] 13 := by
  apply routed_branch D R [272,5,40,514] 13 (by decide) (choices 1) [32,64] route_56
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,40,514] (choices 1) [32,64] route_56).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_57
  · exact upper_58

def bound_73 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 7 44 536 242 226 226 226 482 738), lower := (rows 273 7 44 536 16 32 64 128 256 512), losses := [] }

theorem upper_73 : Upper D R [272,5,40,528] 13 :=
  bound_sound D R [272,5,40,528] 13 bound_73
    ((Boolean.boundCheck_true D R [272,5,40,528] 13 bound_73).mp (by decide +kernel))

def bound_74 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 7 44 552 210 242 210 210 466 722), lower := (rows 273 7 44 552 16 32 64 128 256 512), losses := [] }

theorem upper_74 : Upper D R [272,5,40,544] 13 :=
  bound_sound D R [272,5,40,544] 13 bound_74
    ((Boolean.boundCheck_true D R [272,5,40,544] 13 bound_74).mp (by decide +kernel))

def bound_75 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 7 44 584 242 242 242 242 498 754), lower := (rows 273 7 44 584 16 32 64 128 256 512), losses := [] }

theorem upper_75 : Upper D R [272,5,40,576] 13 :=
  bound_sound D R [272,5,40,576] 13 bound_75
    ((Boolean.boundCheck_true D R [272,5,40,576] 13 bound_75).mp (by decide +kernel))

def route_48 : Route 10 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_48 : Upper D R [272,5,40] 13 := by
  apply routed_branch D R [272,5,40] 13 (by decide) (choices 2) [18,34,48,66,80,96,192,514,528,544,576] route_48
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,5,40] (choices 2) [18,34,48,66,80,96,192,514,528,544,576] route_48).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_49
  · exact upper_50
  · exact upper_51
  · exact upper_52
  · exact upper_53
  · exact upper_54
  · exact upper_55
  · exact upper_56
  · exact upper_73
  · exact upper_74
  · exact upper_75

def bound_76 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 7 52 746 762 746 746 746 1002 746), lower := (rows 273 7 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_76 : Upper D R [272,5,48] 13 :=
  bound_sound D R [272,5,48] 13 bound_76
    ((Boolean.boundCheck_true D R [272,5,48] 13 bound_76).mp (by decide +kernel))

def bound_77 : Bound 10 := { allowed := (rows 224 240 144 240 0 0 0 0 0 0), upper := (rows 273 7 100 762 762 762 762 762 1018 762), lower := (rows 273 7 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_77 : Upper D R [272,5,96] 13 :=
  bound_sound D R [272,5,96] 13 bound_77
    ((Boolean.boundCheck_true D R [272,5,96] 13 bound_77).mp (by decide +kernel))

def bound_79 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 7 518 56 248 232 232 232 488 744), lower := (rows 273 7 518 56 16 32 64 128 256 512), losses := [] }

theorem upper_79 : Upper D R [272,5,514,48] 13 :=
  bound_sound D R [272,5,514,48] 13 bound_79
    ((Boolean.boundCheck_true D R [272,5,514,48] 13 bound_79).mp (by decide +kernel))

def bound_80 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 273 7 518 104 248 248 248 248 504 760), lower := (rows 273 7 518 104 16 32 64 128 256 512), losses := [] }

theorem upper_80 : Upper D R [272,5,514,96] 13 :=
  bound_sound D R [272,5,514,96] 13 bound_80
    ((Boolean.boundCheck_true D R [272,5,514,96] 13 bound_80).mp (by decide +kernel))

def route_78 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_78 : Upper D R [272,5,514] 13 := by
  apply routed_branch D R [272,5,514] 13 (by decide) (choices 2) [48,96] route_78
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,5,514] (choices 2) [48,96] route_78).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_79
  · exact upper_80

def bound_82 : Bound 10 := { allowed := (rows 224 240 224 224 0 0 0 0 0 0), upper := (rows 273 7 524 26 240 224 224 224 480 736), lower := (rows 273 7 524 26 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 1023 1023 1023 1023 1023), good := (rows 993 999 1004 1006 992 992 992 992 992 992) }] }

theorem upper_82 : Upper D R [272,5,520,18] 13 :=
  bound_sound D R [272,5,520,18] 13 bound_82
    ((Boolean.boundCheck_true D R [272,5,520,18] 13 bound_82).mp (by decide +kernel))

def bound_84 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 273 7 524 42 48 240 208 208 464 720), lower := (rows 273 7 524 42 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 4 8 16 0 81 145 273 529), good := (rows 977 967 524 10 977 0 64 128 256 512) }] }

theorem upper_84 : Upper D R [272,5,520,34,32] 13 :=
  bound_sound D R [272,5,520,34,32] 13 bound_84
    ((Boolean.boundCheck_true D R [272,5,520,34,32] 13 bound_84).mp (by decide +kernel))

def bound_86 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 7 524 42 80 48 224 224 480 736), lower := (rows 273 7 524 42 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 104 168 296 552), good := (rows 257 7 972 1006 64 992 64 128 256 512) }] }

theorem upper_86 : Upper D R [272,5,520,34,64,16] 13 :=
  bound_sound D R [272,5,520,34,64,16] 13 bound_86
    ((Boolean.boundCheck_true D R [272,5,520,34,64,16] 13 bound_86).mp (by decide +kernel))

def bound_88 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 7 524 42 80 96 80 160 416 672), lower := (rows 273 7 524 42 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 15 9 0 112 64 249 377 633), good := (rows 943 911 908 942 992 992 992 128 256 512) }] }

theorem upper_88 : Upper D R [272,5,520,34,64,64,16] 13 :=
  bound_sound D R [272,5,520,34,64,64,16] 13 bound_88
    ((Boolean.boundCheck_true D R [272,5,520,34,64,64,16] 13 bound_88).mp (by decide +kernel))

def bound_89 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 7 524 42 80 96 96 144 400 656), lower := (rows 273 7 524 42 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 1023 1023 128 256 512), good := (rows 353 111 620 106 96 96 96 224 352 608) }] }

theorem upper_89 : Upper D R [272,5,520,34,64,64,32] 13 :=
  bound_sound D R [272,5,520,34,64,64,32] 13 bound_89
    ((Boolean.boundCheck_true D R [272,5,520,34,64,64,32] 13 bound_89).mp (by decide +kernel))

def bound_91 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 273 7 524 42 80 96 192 144 416 672), lower := (rows 273 7 524 42 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 257 2 4 8 1023 0 1023 1023 256 512), good := (rows 465 215 732 218 208 208 208 208 465 720) }] }

theorem upper_91 : Upper D R [272,5,520,34,64,64,128,16] 13 :=
  bound_sound D R [272,5,520,34,64,64,128,16] 13 bound_91
    ((Boolean.boundCheck_true D R [272,5,520,34,64,64,128,16] 13 bound_91).mp (by decide +kernel))

def bound_92 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 7 524 42 80 96 192 160 400 656), lower := (rows 273 7 524 42 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 1023 1023 1023 256 512), good := (rows 481 239 748 234 224 224 224 224 480 736) }] }

theorem upper_92 : Upper D R [272,5,520,34,64,64,128,32] 13 :=
  bound_sound D R [272,5,520,34,64,64,128,32] 13 bound_92
    ((Boolean.boundCheck_true D R [272,5,520,34,64,64,128,32] 13 bound_92).mp (by decide +kernel))

def route_90 : Route 10 := (fun mask => (mask,id))

theorem upper_90 : Upper D R [272,5,520,34,64,64,128] 13 := by
  apply routed_branch D R [272,5,520,34,64,64,128] 13 (by decide) (choices 1) [16,32] route_90
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,520,34,64,64,128] (choices 1) [16,32] route_90).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_91
  · exact upper_92

def route_87 : Route 10 := (fun mask => (mask,id))

theorem upper_87 : Upper D R [272,5,520,34,64,64] 13 := by
  apply routed_branch D R [272,5,520,34,64,64] 13 (by decide) (choices 1) [16,32,128] route_87
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,520,34,64,64] (choices 1) [16,32,128] route_87).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_88
  · exact upper_89
  · exact upper_90

def bound_94 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 7 524 42 80 160 80 224 480 736), lower := (rows 273 7 524 42 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 5 11 0 241 64 208 336 592), good := (rows 943 47 524 42 992 160 992 160 256 512) }] }

theorem upper_94 : Upper D R [272,5,520,34,64,128,16] 13 :=
  bound_sound D R [272,5,520,34,64,128,16] 13 bound_94
    ((Boolean.boundCheck_true D R [272,5,520,34,64,128,16] 13 bound_94).mp (by decide +kernel))

def bound_95 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 273 7 524 42 80 160 96 208 464 720), lower := (rows 273 7 524 42 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 7 524 10 977 128 977 128 256 512) }] }

theorem upper_95 : Upper D R [272,5,520,34,64,128,32] 13 :=
  bound_sound D R [272,5,520,34,64,128,32] 13 bound_95
    ((Boolean.boundCheck_true D R [272,5,520,34,64,128,32] 13 bound_95).mp (by decide +kernel))

def bound_97 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 7 524 42 80 160 192 144 352 608), lower := (rows 273 7 524 42 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 224 224 128 504 760), good := (rows 769 7 780 878 864 992 992 992 256 512) }] }

theorem upper_97 : Upper D R [272,5,520,34,64,128,128,16] 13 :=
  bound_sound D R [272,5,520,34,64,128,128,16] 13 bound_97
    ((Boolean.boundCheck_true D R [272,5,520,34,64,128,128,16] 13 bound_97).mp (by decide +kernel))

def bound_98 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 7 524 42 80 160 192 160 336 592), lower := (rows 273 7 524 42 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 1023 1023 1023 256 512), good := (rows 481 239 748 234 224 224 224 224 480 736) }] }

theorem upper_98 : Upper D R [272,5,520,34,64,128,128,32] 13 :=
  bound_sound D R [272,5,520,34,64,128,128,32] 13 bound_98
    ((Boolean.boundCheck_true D R [272,5,520,34,64,128,128,32] 13 bound_98).mp (by decide +kernel))

def bound_99 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 7 524 42 80 160 192 192 304 560), lower := (rows 273 7 524 42 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 1023 1023 1023 256 512), good := (rows 481 239 748 234 224 224 224 224 480 736) }] }

theorem upper_99 : Upper D R [272,5,520,34,64,128,128,64] 13 :=
  bound_sound D R [272,5,520,34,64,128,128,64] 13 bound_99
    ((Boolean.boundCheck_true D R [272,5,520,34,64,128,128,64] 13 bound_99).mp (by decide +kernel))

def route_96 : Route 10 := (fun mask => (mask,id))

theorem upper_96 : Upper D R [272,5,520,34,64,128,128] 13 := by
  apply routed_branch D R [272,5,520,34,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_96
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,520,34,64,128,128] (choices 1) [16,32,64] route_96).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_97
  · exact upper_98
  · exact upper_99

def route_93 : Route 10 := (fun mask => (mask,id))

theorem upper_93 : Upper D R [272,5,520,34,64,128] 13 := by
  apply routed_branch D R [272,5,520,34,64,128] 13 (by decide) (choices 1) [16,32,128] route_93
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,520,34,64,128] (choices 1) [16,32,128] route_93).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_94
  · exact upper_95
  · exact upper_96

def route_85 : Route 10 := (fun mask => (mask,id))

theorem upper_85 : Upper D R [272,5,520,34,64] 13 := by
  apply routed_branch D R [272,5,520,34,64] 13 (by decide) (choices 1) [16,64,128] route_85
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,520,34,64] (choices 1) [16,64,128] route_85).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_86
  · exact upper_87
  · exact upper_93

def route_83 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_83 : Upper D R [272,5,520,34] 13 := by
  apply routed_branch D R [272,5,520,34] 13 (by decide) (choices 1) [32,64] route_83
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,5,520,34] (choices 1) [32,64] route_83).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_84
  · exact upper_85

def bound_100 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 7 524 56 242 226 226 226 482 738), lower := (rows 273 7 524 56 16 32 64 128 256 512), losses := [] }

theorem upper_100 : Upper D R [272,5,520,48] 13 :=
  bound_sound D R [272,5,520,48] 13 bound_100
    ((Boolean.boundCheck_true D R [272,5,520,48] 13 bound_100).mp (by decide +kernel))

def bound_101 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 273 7 524 104 242 242 242 242 498 754), lower := (rows 273 7 524 104 16 32 64 128 256 512), losses := [] }

theorem upper_101 : Upper D R [272,5,520,96] 13 :=
  bound_sound D R [272,5,520,96] 13 bound_101
    ((Boolean.boundCheck_true D R [272,5,520,96] 13 bound_101).mp (by decide +kernel))

def route_81 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_81 : Upper D R [272,5,520] 13 := by
  apply routed_branch D R [272,5,520] 13 (by decide) (choices 2) [18,34,48,96] route_81
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,5,520] (choices 2) [18,34,48,96] route_81).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_82
  · exact upper_83
  · exact upper_100
  · exact upper_101

def bound_103 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 7 532 42 248 232 232 232 488 744), lower := (rows 273 7 532 42 16 32 64 128 256 512), losses := [] }

theorem upper_103 : Upper D R [272,5,528,34] 13 :=
  bound_sound D R [272,5,528,34] 13 bound_103
    ((Boolean.boundCheck_true D R [272,5,528,34] 13 bound_103).mp (by decide +kernel))

def bound_104 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 273 7 532 104 250 234 234 234 490 746), lower := (rows 273 7 532 104 16 32 64 128 256 512), losses := [] }

theorem upper_104 : Upper D R [272,5,528,96] 13 :=
  bound_sound D R [272,5,528,96] 13 bound_104
    ((Boolean.boundCheck_true D R [272,5,528,96] 13 bound_104).mp (by decide +kernel))

def route_102 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_102 : Upper D R [272,5,528] 13 := by
  apply routed_branch D R [272,5,528] 13 (by decide) (choices 2) [34,96] route_102
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,5,528] (choices 2) [34,96] route_102).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_103
  · exact upper_104

def bound_106 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 7 548 26 248 232 232 232 488 744), lower := (rows 273 7 548 26 16 32 64 128 256 512), losses := [] }

theorem upper_106 : Upper D R [272,5,544,18] 13 :=
  bound_sound D R [272,5,544,18] 13 bound_106
    ((Boolean.boundCheck_true D R [272,5,544,18] 13 bound_106).mp (by decide +kernel))

def bound_107 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 7 548 42 216 248 216 216 472 728), lower := (rows 273 7 548 42 16 32 64 128 256 512), losses := [] }

theorem upper_107 : Upper D R [272,5,544,34] 13 :=
  bound_sound D R [272,5,544,34] 13 bound_107
    ((Boolean.boundCheck_true D R [272,5,544,34] 13 bound_107).mp (by decide +kernel))

def bound_108 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 273 7 548 56 218 234 202 202 458 714), lower := (rows 273 7 548 56 16 32 64 128 256 512), losses := [] }

theorem upper_108 : Upper D R [272,5,544,48] 13 :=
  bound_sound D R [272,5,544,48] 13 bound_108
    ((Boolean.boundCheck_true D R [272,5,544,48] 13 bound_108).mp (by decide +kernel))

def bound_109 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 7 548 74 248 248 248 248 504 760), lower := (rows 273 7 548 74 16 32 64 128 256 512), losses := [] }

theorem upper_109 : Upper D R [272,5,544,66] 13 :=
  bound_sound D R [272,5,544,66] 13 bound_109
    ((Boolean.boundCheck_true D R [272,5,544,66] 13 bound_109).mp (by decide +kernel))

def bound_110 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 273 7 548 88 250 234 234 234 490 746), lower := (rows 273 7 548 88 16 32 64 128 256 512), losses := [] }

theorem upper_110 : Upper D R [272,5,544,80] 13 :=
  bound_sound D R [272,5,544,80] 13 bound_110
    ((Boolean.boundCheck_true D R [272,5,544,80] 13 bound_110).mp (by decide +kernel))

def bound_111 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 273 7 548 104 218 250 218 218 474 730), lower := (rows 273 7 548 104 16 32 64 128 256 512), losses := [] }

theorem upper_111 : Upper D R [272,5,544,96] 13 :=
  bound_sound D R [272,5,544,96] 13 bound_111
    ((Boolean.boundCheck_true D R [272,5,544,96] 13 bound_111).mp (by decide +kernel))

def bound_112 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 273 7 548 200 250 250 250 250 506 762), lower := (rows 273 7 548 200 16 32 64 128 256 512), losses := [] }

theorem upper_112 : Upper D R [272,5,544,192] 13 :=
  bound_sound D R [272,5,544,192] 13 bound_112
    ((Boolean.boundCheck_true D R [272,5,544,192] 13 bound_112).mp (by decide +kernel))

def route_105 : Route 10 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_105 : Upper D R [272,5,544] 13 := by
  apply routed_branch D R [272,5,544] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] route_105
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,5,544] (choices 2) [18,34,48,66,80,96,192] route_105).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_106
  · exact upper_107
  · exact upper_108
  · exact upper_109
  · exact upper_110
  · exact upper_111
  · exact upper_112

def route_0 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [272,5] 13 := by
  apply routed_branch D R [272,5] 13 (by decide) (choices 2) [10,18,24,34,40,48,96,514,520,528,544] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,5] (choices 2) [10,18,24,34,40,48,96,514,520,528,544] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_32
  · exact upper_35
  · exact upper_40
  · exact upper_48
  · exact upper_76
  · exact upper_77
  · exact upper_78
  · exact upper_81
  · exact upper_102
  · exact upper_105

theorem upper : Upper D R [272,5] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case43
