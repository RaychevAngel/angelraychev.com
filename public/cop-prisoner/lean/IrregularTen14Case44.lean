import IrregularTen14Base

namespace Delivery.IrregularTen14.Case44
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 14 7 56 752 736 736 736 992 736), lower := (rows 273 14 7 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [272,12,3,48] 13 :=
  bound_sound D R [272,12,3,48] 13 bound_2
    ((Boolean.boundCheck_true D R [272,12,3,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 273 14 7 104 752 752 752 752 1008 752), lower := (rows 273 14 7 104 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [272,12,3,96] 13 :=
  bound_sound D R [272,12,3,96] 13 bound_3
    ((Boolean.boundCheck_true D R [272,12,3,96] 13 bound_3).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 192 208 208 192 0 0 0 0 0 0), upper := (rows 273 14 7 536 48 96 96 192 448 704), lower := (rows 273 14 7 536 48 96 96 128 256 512), losses := [{ target := 5, region := (rows 17 27 29 24 16 0 64 224 352 608), good := (rows 287 14 7 543 927 960 960 128 256 512) }] }

theorem upper_7 : Upper D R [272,12,3,528,32,64,32] 13 :=
  bound_sound D R [272,12,3,528,32,64,32] 13 bound_7
    ((Boolean.boundCheck_true D R [272,12,3,528,32,64,32] 13 bound_7).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 192 208 208 224 0 0 0 0 0 0), upper := (rows 273 14 7 536 48 96 192 160 320 640), lower := (rows 273 14 7 536 48 96 192 160 320 512), losses := [{ target := 5, region := (rows 17 10 12 8 16 0 192 128 480 704), good := (rows 273 14 7 543 273 832 960 960 832 512) }] }

theorem upper_10 : Upper D R [272,12,3,528,32,64,128,32,64] 13 :=
  bound_sound D R [272,12,3,528,32,64,128,32,64] 13 bound_10
    ((Boolean.boundCheck_true D R [272,12,3,528,32,64,128,32,64] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 224 208 208 192 0 0 0 0 0 0), upper := (rows 273 14 7 536 48 96 192 160 384 576), lower := (rows 273 14 7 536 48 96 192 160 384 512), losses := [{ target := 5, region := (rows 1 7 5 25 16 0 448 128 448 993), good := (rows 863 14 527 536 536 832 960 960 960 512) }] }

theorem upper_11 : Upper D R [272,12,3,528,32,64,128,32,128] 13 :=
  bound_sound D R [272,12,3,528,32,64,128,32,128] 13 bound_11
    ((Boolean.boundCheck_true D R [272,12,3,528,32,64,128,32,128] 13 bound_11).mp (by decide +kernel))

def route_9 : Route 10 := (fun mask => (mask,id))

theorem upper_9 : Upper D R [272,12,3,528,32,64,128,32] 13 := by
  apply routed_branch D R [272,12,3,528,32,64,128,32] 13 (by decide) (choices 1) [64,128] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,3,528,32,64,128,32] (choices 1) [64,128] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_10
  · exact upper_11

def bound_13 : Bound 10 := { allowed := (rows 224 208 208 192 0 0 0 0 0 0), upper := (rows 273 14 7 536 48 96 192 192 288 640), lower := (rows 273 14 7 536 48 96 192 192 288 512), losses := [{ target := 5, region := (rows 1 7 5 25 16 0 1023 1023 256 1023), good := (rows 991 718 719 728 728 704 704 704 960 704) }] }

theorem upper_13 : Upper D R [272,12,3,528,32,64,128,64,32] 13 :=
  bound_sound D R [272,12,3,528,32,64,128,64,32] 13 bound_13
    ((Boolean.boundCheck_true D R [272,12,3,528,32,64,128,64,32] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 192 208 208 224 0 0 0 0 0 0), upper := (rows 273 14 7 536 48 96 192 192 384 544), lower := (rows 273 14 7 536 48 96 192 192 384 512), losses := [{ target := 5, region := (rows 25 10 14 8 16 0 1023 1023 1023 512), good := (rows 465 463 455 991 465 448 448 448 448 960) }] }

theorem upper_14 : Upper D R [272,12,3,528,32,64,128,64,128] 13 :=
  bound_sound D R [272,12,3,528,32,64,128,64,128] 13 bound_14
    ((Boolean.boundCheck_true D R [272,12,3,528,32,64,128,64,128] 13 bound_14).mp (by decide +kernel))

def route_12 : Route 10 := (fun mask => (mask,id))

theorem upper_12 : Upper D R [272,12,3,528,32,64,128,64] 13 := by
  apply routed_branch D R [272,12,3,528,32,64,128,64] 13 (by decide) (choices 1) [32,128] route_12
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,3,528,32,64,128,64] (choices 1) [32,128] route_12).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_13
  · exact upper_14

def route_8 : Route 10 := (fun mask => (mask,id))

theorem upper_8 : Upper D R [272,12,3,528,32,64,128] 13 := by
  apply routed_branch D R [272,12,3,528,32,64,128] 13 (by decide) (choices 1) [32,64] route_8
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,3,528,32,64,128] (choices 1) [32,64] route_8).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_9
  · exact upper_12

def route_6 : Route 10 := (fun mask => (mask,id))

theorem upper_6 : Upper D R [272,12,3,528,32,64] 13 := by
  apply routed_branch D R [272,12,3,528,32,64] 13 (by decide) (choices 1) [32,128] route_6
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,3,528,32,64] (choices 1) [32,128] route_6).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_7
  · exact upper_8

def route_5 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_5 : Upper D R [272,12,3,528,32] 13 := by
  apply routed_branch D R [272,12,3,528,32] 13 (by decide) (choices 1) [64] route_5
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,3,528,32] (choices 1) [64] route_5).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_6

def route_4 : Route 10 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 128 => (32,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_4 : Upper D R [272,12,3,528] 13 := by
  apply routed_branch D R [272,12,3,528] 13 (by decide) (choices 1) [32] route_4
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,3,528] (choices 1) [32] route_4).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_5

def bound_16 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 273 14 7 552 48 240 208 208 464 720), lower := (rows 273 14 7 552 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 4 8 16 0 81 145 273 529), good := (rows 977 14 967 520 977 0 64 128 256 512) }] }

theorem upper_16 : Upper D R [272,12,3,544,32] 13 :=
  bound_sound D R [272,12,3,544,32] 13 bound_16
    ((Boolean.boundCheck_true D R [272,12,3,544,32] 13 bound_16).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 14 7 552 80 48 224 224 480 736), lower := (rows 273 14 7 552 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 40 0 32 104 168 296 552), good := (rows 257 974 7 1000 64 1000 64 128 256 512) }] }

theorem upper_18 : Upper D R [272,12,3,544,64,16] 13 :=
  bound_sound D R [272,12,3,544,64,16] 13 bound_18
    ((Boolean.boundCheck_true D R [272,12,3,544,64,16] 13 bound_18).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 14 7 552 80 96 80 160 416 672), lower := (rows 273 14 7 552 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 121 0 112 64 249 377 633), good := (rows 943 910 911 936 1000 1000 1000 128 256 512) }] }

theorem upper_20 : Upper D R [272,12,3,544,64,64,16] 13 :=
  bound_sound D R [272,12,3,544,64,64,16] 13 bound_20
    ((Boolean.boundCheck_true D R [272,12,3,544,64,64,16] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 14 7 552 80 96 96 144 400 656), lower := (rows 273 14 7 552 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 128 256 512), good := (rows 353 110 103 616 96 96 96 224 352 616) }] }

theorem upper_21 : Upper D R [272,12,3,544,64,64,32] 13 :=
  bound_sound D R [272,12,3,544,64,64,32] 13 bound_21
    ((Boolean.boundCheck_true D R [272,12,3,544,64,64,32] 13 bound_21).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 14 7 552 80 96 192 144 416 672), lower := (rows 273 14 7 552 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 1 3 5 248 0 240 192 128 448 704), good := (rows 303 14 7 552 872 872 1000 1000 256 512) }] }

theorem upper_23 : Upper D R [272,12,3,544,64,64,128,16] 13 :=
  bound_sound D R [272,12,3,544,64,64,128,16] 13 bound_23
    ((Boolean.boundCheck_true D R [272,12,3,544,64,64,128,16] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 14 7 552 80 96 192 160 400 656), lower := (rows 273 14 7 552 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 481 238 231 744 224 224 224 224 480 744) }] }

theorem upper_24 : Upper D R [272,12,3,544,64,64,128,32] 13 :=
  bound_sound D R [272,12,3,544,64,64,128,32] 13 bound_24
    ((Boolean.boundCheck_true D R [272,12,3,544,64,64,128,32] 13 bound_24).mp (by decide +kernel))

def route_22 : Route 10 := (fun mask => (mask,id))

theorem upper_22 : Upper D R [272,12,3,544,64,64,128] 13 := by
  apply routed_branch D R [272,12,3,544,64,64,128] 13 (by decide) (choices 1) [16,32] route_22
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,3,544,64,64,128] (choices 1) [16,32] route_22).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_23
  · exact upper_24

def route_19 : Route 10 := (fun mask => (mask,id))

theorem upper_19 : Upper D R [272,12,3,544,64,64] 13 := by
  apply routed_branch D R [272,12,3,544,64,64] 13 (by decide) (choices 1) [16,32,128] route_19
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,3,544,64,64] (choices 1) [16,32,128] route_19).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_20
  · exact upper_21
  · exact upper_22

def bound_26 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 14 7 552 80 160 80 224 480 736), lower := (rows 273 14 7 552 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 89 0 241 64 208 336 592), good := (rows 943 14 47 552 1000 160 1000 160 256 512) }] }

theorem upper_26 : Upper D R [272,12,3,544,64,128,16] 13 :=
  bound_sound D R [272,12,3,544,64,128,16] 13 bound_26
    ((Boolean.boundCheck_true D R [272,12,3,544,64,128,16] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 273 14 7 552 80 160 96 208 464 720), lower := (rows 273 14 7 552 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 14 7 520 977 128 977 128 256 512) }] }

theorem upper_27 : Upper D R [272,12,3,544,64,128,32] 13 :=
  bound_sound D R [272,12,3,544,64,128,32] 13 bound_27
    ((Boolean.boundCheck_true D R [272,12,3,544,64,128,32] 13 bound_27).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 14 7 552 80 160 192 144 352 608), lower := (rows 273 14 7 552 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 3 5 248 0 224 224 128 504 760), good := (rows 783 782 7 872 872 1000 1000 1000 256 512) }] }

theorem upper_29 : Upper D R [272,12,3,544,64,128,128,16] 13 :=
  bound_sound D R [272,12,3,544,64,128,128,16] 13 bound_29
    ((Boolean.boundCheck_true D R [272,12,3,544,64,128,128,16] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 14 7 552 80 160 192 160 336 592), lower := (rows 273 14 7 552 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 481 238 231 744 224 224 224 224 480 744) }] }

theorem upper_30 : Upper D R [272,12,3,544,64,128,128,32] 13 :=
  bound_sound D R [272,12,3,544,64,128,128,32] 13 bound_30
    ((Boolean.boundCheck_true D R [272,12,3,544,64,128,128,32] 13 bound_30).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 14 7 552 80 160 192 192 304 560), lower := (rows 273 14 7 552 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 481 238 231 744 224 224 224 224 480 744) }] }

theorem upper_31 : Upper D R [272,12,3,544,64,128,128,64] 13 :=
  bound_sound D R [272,12,3,544,64,128,128,64] 13 bound_31
    ((Boolean.boundCheck_true D R [272,12,3,544,64,128,128,64] 13 bound_31).mp (by decide +kernel))

def route_28 : Route 10 := (fun mask => (mask,id))

theorem upper_28 : Upper D R [272,12,3,544,64,128,128] 13 := by
  apply routed_branch D R [272,12,3,544,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_28
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,3,544,64,128,128] (choices 1) [16,32,64] route_28).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_29
  · exact upper_30
  · exact upper_31

def route_25 : Route 10 := (fun mask => (mask,id))

theorem upper_25 : Upper D R [272,12,3,544,64,128] 13 := by
  apply routed_branch D R [272,12,3,544,64,128] 13 (by decide) (choices 1) [16,32,128] route_25
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,3,544,64,128] (choices 1) [16,32,128] route_25).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_26
  · exact upper_27
  · exact upper_28

def route_17 : Route 10 := (fun mask => (mask,id))

theorem upper_17 : Upper D R [272,12,3,544,64] 13 := by
  apply routed_branch D R [272,12,3,544,64] 13 (by decide) (choices 1) [16,64,128] route_17
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,3,544,64] (choices 1) [16,64,128] route_17).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_18
  · exact upper_19
  · exact upper_25

def route_15 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_15 : Upper D R [272,12,3,544] 13 := by
  apply routed_branch D R [272,12,3,544] 13 (by decide) (choices 1) [32,64] route_15
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,3,544] (choices 1) [32,64] route_15).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_16
  · exact upper_17

def route_1 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [272,12,3] 13 := by
  apply routed_branch D R [272,12,3] 13 (by decide) (choices 2) [48,96,528,544] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,12,3] (choices 2) [48,96,528,544] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_15

def bound_33 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 14 21 42 752 736 736 736 992 736), lower := (rows 273 14 21 42 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [272,12,17,34] 13 :=
  bound_sound D R [272,12,17,34] 13 bound_33
    ((Boolean.boundCheck_true D R [272,12,17,34] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 273 14 21 104 754 738 738 738 994 738), lower := (rows 273 14 21 104 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [272,12,17,96] 13 :=
  bound_sound D R [272,12,17,96] 13 bound_34
    ((Boolean.boundCheck_true D R [272,12,17,96] 13 bound_34).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 273 14 21 522 240 224 224 224 480 736), lower := (rows 273 14 21 522 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 6 4 14 0 1023 1023 1023 1023 1023), good := (rows 993 1006 1007 1002 992 992 992 992 992 992) }] }

theorem upper_35 : Upper D R [272,12,17,514] 13 :=
  bound_sound D R [272,12,17,514] 13 bound_35
    ((Boolean.boundCheck_true D R [272,12,17,514] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 14 21 552 242 226 226 226 482 738), lower := (rows 273 14 21 552 16 32 64 128 256 512), losses := [] }

theorem upper_36 : Upper D R [272,12,17,544] 13 :=
  bound_sound D R [272,12,17,544] 13 bound_36
    ((Boolean.boundCheck_true D R [272,12,17,544] 13 bound_36).mp (by decide +kernel))

def route_32 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_32 : Upper D R [272,12,17] 13 := by
  apply routed_branch D R [272,12,17] 13 (by decide) (choices 2) [34,96,514,544] route_32
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,12,17] (choices 2) [34,96,514,544] route_32).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_33
  · exact upper_34
  · exact upper_35
  · exact upper_36

def bound_38 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 14 22 41 752 736 736 736 992 736), lower := (rows 273 14 22 41 16 32 64 128 256 512), losses := [] }

theorem upper_38 : Upper D R [272,12,18,33] 13 :=
  bound_sound D R [272,12,18,33] 13 bound_38
    ((Boolean.boundCheck_true D R [272,12,18,33] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 273 14 22 104 753 737 737 737 993 737), lower := (rows 273 14 22 104 16 32 64 128 256 512), losses := [] }

theorem upper_39 : Upper D R [272,12,18,96] 13 :=
  bound_sound D R [272,12,18,96] 13 bound_39
    ((Boolean.boundCheck_true D R [272,12,18,96] 13 bound_39).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 224 240 224 224 0 0 0 0 0 0), upper := (rows 273 14 22 521 240 224 224 224 480 736), lower := (rows 273 14 22 521 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 1023 1023 1023), good := (rows 1001 1006 998 1001 992 992 992 992 992 992) }] }

theorem upper_40 : Upper D R [272,12,18,513] 13 :=
  bound_sound D R [272,12,18,513] 13 bound_40
    ((Boolean.boundCheck_true D R [272,12,18,513] 13 bound_40).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 14 22 552 241 225 225 225 481 737), lower := (rows 273 14 22 552 16 32 64 128 256 512), losses := [] }

theorem upper_41 : Upper D R [272,12,18,544] 13 :=
  bound_sound D R [272,12,18,544] 13 bound_41
    ((Boolean.boundCheck_true D R [272,12,18,544] 13 bound_41).mp (by decide +kernel))

def route_37 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_37 : Upper D R [272,12,18] 13 := by
  apply routed_branch D R [272,12,18] 13 (by decide) (choices 2) [33,96,513,544] route_37
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,12,18] (choices 2) [33,96,513,544] route_37).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_38
  · exact upper_39
  · exact upper_40
  · exact upper_41

def bound_43 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 14 37 26 752 736 736 736 992 736), lower := (rows 273 14 37 26 16 32 64 128 256 512), losses := [] }

theorem upper_43 : Upper D R [272,12,33,18] 13 :=
  bound_sound D R [272,12,33,18] 13 bound_43
    ((Boolean.boundCheck_true D R [272,12,33,18] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 14 37 42 720 752 720 720 976 720), lower := (rows 273 14 37 42 16 32 64 128 256 512), losses := [] }

theorem upper_44 : Upper D R [272,12,33,34] 13 :=
  bound_sound D R [272,12,33,34] 13 bound_44
    ((Boolean.boundCheck_true D R [272,12,33,34] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 273 14 37 56 722 738 706 706 962 706), lower := (rows 273 14 37 56 16 32 64 128 256 512), losses := [] }

theorem upper_45 : Upper D R [272,12,33,48] 13 :=
  bound_sound D R [272,12,33,48] 13 bound_45
    ((Boolean.boundCheck_true D R [272,12,33,48] 13 bound_45).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 14 37 74 752 752 752 752 1008 752), lower := (rows 273 14 37 74 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [272,12,33,66] 13 :=
  bound_sound D R [272,12,33,66] 13 bound_46
    ((Boolean.boundCheck_true D R [272,12,33,66] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 273 14 37 88 754 738 738 738 994 738), lower := (rows 273 14 37 88 16 32 64 128 256 512), losses := [] }

theorem upper_47 : Upper D R [272,12,33,80] 13 :=
  bound_sound D R [272,12,33,80] 13 bound_47
    ((Boolean.boundCheck_true D R [272,12,33,80] 13 bound_47).mp (by decide +kernel))

def bound_48 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 273 14 37 104 722 754 722 722 978 722), lower := (rows 273 14 37 104 16 32 64 128 256 512), losses := [] }

theorem upper_48 : Upper D R [272,12,33,96] 13 :=
  bound_sound D R [272,12,33,96] 13 bound_48
    ((Boolean.boundCheck_true D R [272,12,33,96] 13 bound_48).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 273 14 37 200 754 754 754 754 1010 754), lower := (rows 273 14 37 200 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [272,12,33,192] 13 :=
  bound_sound D R [272,12,33,192] 13 bound_49
    ((Boolean.boundCheck_true D R [272,12,33,192] 13 bound_49).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 273 14 37 522 48 240 208 208 464 720), lower := (rows 273 14 37 522 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 6 4 12 16 0 81 145 273 529), good := (rows 977 14 975 522 977 0 64 128 256 512) }] }

theorem upper_51 : Upper D R [272,12,33,514,32] 13 :=
  bound_sound D R [272,12,33,514,32] 13 bound_51
    ((Boolean.boundCheck_true D R [272,12,33,514,32] 13 bound_51).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 224 224 208 224 0 0 0 0 0 0), upper := (rows 273 14 37 522 80 48 224 224 480 736), lower := (rows 273 14 37 522 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 6 4 14 0 32 100 164 292 548), good := (rows 257 974 1007 522 64 992 64 128 256 512) }] }

theorem upper_53 : Upper D R [272,12,33,514,64,16] 13 :=
  bound_sound D R [272,12,33,514,64,16] 13 bound_53
    ((Boolean.boundCheck_true D R [272,12,33,514,64,16] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 14 37 522 80 96 240 176 432 688), lower := (rows 273 14 37 522 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 5 8 0 112 64 128 256 512), good := (rows 293 14 37 522 96 96 96 128 256 512) }] }

theorem upper_54 : Upper D R [272,12,33,514,64,64] 13 :=
  bound_sound D R [272,12,33,514,64,64] 13 bound_54
    ((Boolean.boundCheck_true D R [272,12,33,514,64,64] 13 bound_54).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 273 14 37 522 80 160 80 224 480 736), lower := (rows 273 14 37 522 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 9 0 241 64 208 336 592), good := (rows 943 14 47 522 992 160 992 160 256 512) }] }

theorem upper_56 : Upper D R [272,12,33,514,64,128,16] 13 :=
  bound_sound D R [272,12,33,514,64,128,16] 13 bound_56
    ((Boolean.boundCheck_true D R [272,12,33,514,64,128,16] 13 bound_56).mp (by decide +kernel))

def bound_57 : Bound 10 := { allowed := (rows 192 240 208 240 0 0 0 0 0 0), upper := (rows 273 14 37 522 80 160 96 208 464 720), lower := (rows 273 14 37 522 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 14 5 522 977 128 977 128 256 512) }] }

theorem upper_57 : Upper D R [272,12,33,514,64,128,32] 13 :=
  bound_sound D R [272,12,33,514,64,128,32] 13 bound_57
    ((Boolean.boundCheck_true D R [272,12,33,514,64,128,32] 13 bound_57).mp (by decide +kernel))

def bound_59 : Bound 10 := { allowed := (rows 224 224 208 224 0 0 0 0 0 0), upper := (rows 273 14 37 522 80 160 192 144 352 608), lower := (rows 273 14 37 522 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 6 4 14 0 224 224 128 500 756), good := (rows 769 782 879 522 864 992 992 992 256 512) }] }

theorem upper_59 : Upper D R [272,12,33,514,64,128,128,16] 13 :=
  bound_sound D R [272,12,33,514,64,128,128,16] 13 bound_59
    ((Boolean.boundCheck_true D R [272,12,33,514,64,128,128,16] 13 bound_59).mp (by decide +kernel))

def bound_60 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 14 37 522 80 160 192 160 336 592), lower := (rows 273 14 37 522 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 5 8 0 1023 1023 1023 256 512), good := (rows 485 238 229 746 224 224 224 224 480 736) }] }

theorem upper_60 : Upper D R [272,12,33,514,64,128,128,32] 13 :=
  bound_sound D R [272,12,33,514,64,128,128,32] 13 bound_60
    ((Boolean.boundCheck_true D R [272,12,33,514,64,128,128,32] 13 bound_60).mp (by decide +kernel))

def bound_61 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 14 37 522 80 160 192 192 304 560), lower := (rows 273 14 37 522 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 5 8 0 1023 1023 1023 256 512), good := (rows 485 238 229 746 224 224 224 224 480 736) }] }

theorem upper_61 : Upper D R [272,12,33,514,64,128,128,64] 13 :=
  bound_sound D R [272,12,33,514,64,128,128,64] 13 bound_61
    ((Boolean.boundCheck_true D R [272,12,33,514,64,128,128,64] 13 bound_61).mp (by decide +kernel))

def route_58 : Route 10 := (fun mask => (mask,id))

theorem upper_58 : Upper D R [272,12,33,514,64,128,128] 13 := by
  apply routed_branch D R [272,12,33,514,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_58
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,33,514,64,128,128] (choices 1) [16,32,64] route_58).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_59
  · exact upper_60
  · exact upper_61

def route_55 : Route 10 := (fun mask => (mask,id))

theorem upper_55 : Upper D R [272,12,33,514,64,128] 13 := by
  apply routed_branch D R [272,12,33,514,64,128] 13 (by decide) (choices 1) [16,32,128] route_55
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,33,514,64,128] (choices 1) [16,32,128] route_55).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_56
  · exact upper_57
  · exact upper_58

def route_52 : Route 10 := (fun mask => (mask,id))

theorem upper_52 : Upper D R [272,12,33,514,64] 13 := by
  apply routed_branch D R [272,12,33,514,64] 13 (by decide) (choices 1) [16,64,128] route_52
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,33,514,64] (choices 1) [16,64,128] route_52).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_53
  · exact upper_54
  · exact upper_55

def route_50 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_50 : Upper D R [272,12,33,514] 13 := by
  apply routed_branch D R [272,12,33,514] 13 (by decide) (choices 1) [32,64] route_50
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,33,514] (choices 1) [32,64] route_50).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_51
  · exact upper_52

def bound_62 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 14 37 536 242 226 226 226 482 738), lower := (rows 273 14 37 536 16 32 64 128 256 512), losses := [] }

theorem upper_62 : Upper D R [272,12,33,528] 13 :=
  bound_sound D R [272,12,33,528] 13 bound_62
    ((Boolean.boundCheck_true D R [272,12,33,528] 13 bound_62).mp (by decide +kernel))

def bound_63 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 14 37 552 210 242 210 210 466 722), lower := (rows 273 14 37 552 16 32 64 128 256 512), losses := [] }

theorem upper_63 : Upper D R [272,12,33,544] 13 :=
  bound_sound D R [272,12,33,544] 13 bound_63
    ((Boolean.boundCheck_true D R [272,12,33,544] 13 bound_63).mp (by decide +kernel))

def bound_64 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 14 37 584 242 242 242 242 498 754), lower := (rows 273 14 37 584 16 32 64 128 256 512), losses := [] }

theorem upper_64 : Upper D R [272,12,33,576] 13 :=
  bound_sound D R [272,12,33,576] 13 bound_64
    ((Boolean.boundCheck_true D R [272,12,33,576] 13 bound_64).mp (by decide +kernel))

def route_42 : Route 10 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_42 : Upper D R [272,12,33] 13 := by
  apply routed_branch D R [272,12,33] 13 (by decide) (choices 2) [18,34,48,66,80,96,192,514,528,544,576] route_42
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,12,33] (choices 2) [18,34,48,66,80,96,192,514,528,544,576] route_42).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_43
  · exact upper_44
  · exact upper_45
  · exact upper_46
  · exact upper_47
  · exact upper_48
  · exact upper_49
  · exact upper_50
  · exact upper_62
  · exact upper_63
  · exact upper_64

def bound_66 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 14 38 25 752 736 736 736 992 736), lower := (rows 273 14 38 25 16 32 64 128 256 512), losses := [] }

theorem upper_66 : Upper D R [272,12,34,17] 13 :=
  bound_sound D R [272,12,34,17] 13 bound_66
    ((Boolean.boundCheck_true D R [272,12,34,17] 13 bound_66).mp (by decide +kernel))

def bound_67 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 14 38 41 720 752 720 720 976 720), lower := (rows 273 14 38 41 16 32 64 128 256 512), losses := [] }

theorem upper_67 : Upper D R [272,12,34,33] 13 :=
  bound_sound D R [272,12,34,33] 13 bound_67
    ((Boolean.boundCheck_true D R [272,12,34,33] 13 bound_67).mp (by decide +kernel))

def bound_68 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 273 14 38 56 721 737 705 705 961 705), lower := (rows 273 14 38 56 16 32 64 128 256 512), losses := [] }

theorem upper_68 : Upper D R [272,12,34,48] 13 :=
  bound_sound D R [272,12,34,48] 13 bound_68
    ((Boolean.boundCheck_true D R [272,12,34,48] 13 bound_68).mp (by decide +kernel))

def bound_69 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 14 38 73 752 752 752 752 1008 752), lower := (rows 273 14 38 73 16 32 64 128 256 512), losses := [] }

theorem upper_69 : Upper D R [272,12,34,65] 13 :=
  bound_sound D R [272,12,34,65] 13 bound_69
    ((Boolean.boundCheck_true D R [272,12,34,65] 13 bound_69).mp (by decide +kernel))

def bound_70 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 273 14 38 88 753 737 737 737 993 737), lower := (rows 273 14 38 88 16 32 64 128 256 512), losses := [] }

theorem upper_70 : Upper D R [272,12,34,80] 13 :=
  bound_sound D R [272,12,34,80] 13 bound_70
    ((Boolean.boundCheck_true D R [272,12,34,80] 13 bound_70).mp (by decide +kernel))

def bound_71 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 273 14 38 104 721 753 721 721 977 721), lower := (rows 273 14 38 104 16 32 64 128 256 512), losses := [] }

theorem upper_71 : Upper D R [272,12,34,96] 13 :=
  bound_sound D R [272,12,34,96] 13 bound_71
    ((Boolean.boundCheck_true D R [272,12,34,96] 13 bound_71).mp (by decide +kernel))

def bound_72 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 273 14 38 200 753 753 753 753 1009 753), lower := (rows 273 14 38 200 16 32 64 128 256 512), losses := [] }

theorem upper_72 : Upper D R [272,12,34,192] 13 :=
  bound_sound D R [272,12,34,192] 13 bound_72
    ((Boolean.boundCheck_true D R [272,12,34,192] 13 bound_72).mp (by decide +kernel))

def bound_74 : Bound 10 := { allowed := (rows 192 240 208 208 0 0 0 0 0 0), upper := (rows 273 14 38 521 48 240 208 208 464 720), lower := (rows 273 14 38 521 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 4 25 16 0 81 145 273 529), good := (rows 985 14 6 969 985 0 64 128 256 512) }] }

theorem upper_74 : Upper D R [272,12,34,513,32] 13 :=
  bound_sound D R [272,12,34,513,32] 13 bound_74
    ((Boolean.boundCheck_true D R [272,12,34,513,32] 13 bound_74).mp (by decide +kernel))

def bound_76 : Bound 10 := { allowed := (rows 224 176 144 240 0 0 0 0 0 0), upper := (rows 273 14 38 521 80 48 224 224 480 736), lower := (rows 273 14 38 521 80 48 64 128 256 512), losses := [{ target := 6, region := (rows 1 10 12 8 16 49 0 128 256 512), good := (rows 305 14 38 559 48 48 0 128 256 512) }] }

theorem upper_76 : Upper D R [272,12,34,513,64,16] 13 :=
  bound_sound D R [272,12,34,513,64,16] 13 bound_76
    ((Boolean.boundCheck_true D R [272,12,34,513,64,16] 13 bound_76).mp (by decide +kernel))

def bound_78 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 273 14 38 521 80 96 80 160 416 672), lower := (rows 273 14 38 521 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 5 9 0 112 64 245 373 629), good := (rows 943 910 934 911 992 992 992 128 256 512) }] }

theorem upper_78 : Upper D R [272,12,34,513,64,64,16] 13 :=
  bound_sound D R [272,12,34,513,64,64,16] 13 bound_78
    ((Boolean.boundCheck_true D R [272,12,34,513,64,64,16] 13 bound_78).mp (by decide +kernel))

def bound_79 : Bound 10 := { allowed := (rows 224 224 192 240 0 0 0 0 0 0), upper := (rows 273 14 38 521 80 96 96 144 400 656), lower := (rows 273 14 38 521 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 10 14 8 0 1023 1023 128 256 512), good := (rows 353 110 102 623 96 96 96 224 352 608) }] }

theorem upper_79 : Upper D R [272,12,34,513,64,64,32] 13 :=
  bound_sound D R [272,12,34,513,64,64,32] 13 bound_79
    ((Boolean.boundCheck_true D R [272,12,34,513,64,64,32] 13 bound_79).mp (by decide +kernel))

def bound_81 : Bound 10 := { allowed := (rows 192 240 208 240 0 0 0 0 0 0), upper := (rows 273 14 38 521 80 96 192 144 416 672), lower := (rows 273 14 38 521 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 257 2 4 8 1023 0 1023 1023 256 512), good := (rows 465 222 214 729 208 208 208 208 465 720) }] }

theorem upper_81 : Upper D R [272,12,34,513,64,64,128,16] 13 :=
  bound_sound D R [272,12,34,513,64,64,128,16] 13 bound_81
    ((Boolean.boundCheck_true D R [272,12,34,513,64,64,128,16] 13 bound_81).mp (by decide +kernel))

def bound_82 : Bound 10 := { allowed := (rows 224 224 192 240 0 0 0 0 0 0), upper := (rows 273 14 38 521 80 96 192 160 400 656), lower := (rows 273 14 38 521 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 10 14 8 0 1023 1023 1023 256 512), good := (rows 481 238 230 751 224 224 224 224 480 736) }] }

theorem upper_82 : Upper D R [272,12,34,513,64,64,128,32] 13 :=
  bound_sound D R [272,12,34,513,64,64,128,32] 13 bound_82
    ((Boolean.boundCheck_true D R [272,12,34,513,64,64,128,32] 13 bound_82).mp (by decide +kernel))

def route_80 : Route 10 := (fun mask => (mask,id))

theorem upper_80 : Upper D R [272,12,34,513,64,64,128] 13 := by
  apply routed_branch D R [272,12,34,513,64,64,128] 13 (by decide) (choices 1) [16,32] route_80
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,34,513,64,64,128] (choices 1) [16,32] route_80).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_81
  · exact upper_82

def route_77 : Route 10 := (fun mask => (mask,id))

theorem upper_77 : Upper D R [272,12,34,513,64,64] 13 := by
  apply routed_branch D R [272,12,34,513,64,64] 13 (by decide) (choices 1) [16,32,128] route_77
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,34,513,64,64] (choices 1) [16,32,128] route_77).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_78
  · exact upper_79
  · exact upper_80

def bound_84 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 273 14 38 521 80 160 80 224 480 736), lower := (rows 273 14 38 521 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 13 9 0 241 64 208 336 592), good := (rows 943 14 38 559 992 160 992 160 256 512) }] }

theorem upper_84 : Upper D R [272,12,34,513,64,128,16] 13 :=
  bound_sound D R [272,12,34,513,64,128,16] 13 bound_84
    ((Boolean.boundCheck_true D R [272,12,34,513,64,128,16] 13 bound_84).mp (by decide +kernel))

def bound_85 : Bound 10 := { allowed := (rows 192 240 208 208 0 0 0 0 0 0), upper := (rows 273 14 38 521 80 160 96 208 464 720), lower := (rows 273 14 38 521 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 89 80 0 64 208 336 592), good := (rows 921 14 6 521 985 128 985 128 256 512) }] }

theorem upper_85 : Upper D R [272,12,34,513,64,128,32] 13 :=
  bound_sound D R [272,12,34,513,64,128,32] 13 bound_85
    ((Boolean.boundCheck_true D R [272,12,34,513,64,128,32] 13 bound_85).mp (by decide +kernel))

def bound_87 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 14 38 521 80 160 192 144 352 608), lower := (rows 273 14 38 521 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 224 224 128 500 756), good := (rows 777 782 870 521 864 992 992 992 256 512) }] }

theorem upper_87 : Upper D R [272,12,34,513,64,128,128,16] 13 :=
  bound_sound D R [272,12,34,513,64,128,128,16] 13 bound_87
    ((Boolean.boundCheck_true D R [272,12,34,513,64,128,128,16] 13 bound_87).mp (by decide +kernel))

def bound_88 : Bound 10 := { allowed := (rows 224 224 192 240 0 0 0 0 0 0), upper := (rows 273 14 38 521 80 160 192 160 336 592), lower := (rows 273 14 38 521 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 10 14 8 0 1023 1023 1023 256 512), good := (rows 481 238 230 751 224 224 224 224 480 736) }] }

theorem upper_88 : Upper D R [272,12,34,513,64,128,128,32] 13 :=
  bound_sound D R [272,12,34,513,64,128,128,32] 13 bound_88
    ((Boolean.boundCheck_true D R [272,12,34,513,64,128,128,32] 13 bound_88).mp (by decide +kernel))

def bound_89 : Bound 10 := { allowed := (rows 224 224 192 240 0 0 0 0 0 0), upper := (rows 273 14 38 521 80 160 192 192 304 560), lower := (rows 273 14 38 521 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 10 14 8 0 1023 1023 1023 256 512), good := (rows 481 238 230 751 224 224 224 224 480 736) }] }

theorem upper_89 : Upper D R [272,12,34,513,64,128,128,64] 13 :=
  bound_sound D R [272,12,34,513,64,128,128,64] 13 bound_89
    ((Boolean.boundCheck_true D R [272,12,34,513,64,128,128,64] 13 bound_89).mp (by decide +kernel))

def route_86 : Route 10 := (fun mask => (mask,id))

theorem upper_86 : Upper D R [272,12,34,513,64,128,128] 13 := by
  apply routed_branch D R [272,12,34,513,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_86
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,34,513,64,128,128] (choices 1) [16,32,64] route_86).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_87
  · exact upper_88
  · exact upper_89

def route_83 : Route 10 := (fun mask => (mask,id))

theorem upper_83 : Upper D R [272,12,34,513,64,128] 13 := by
  apply routed_branch D R [272,12,34,513,64,128] 13 (by decide) (choices 1) [16,32,128] route_83
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,34,513,64,128] (choices 1) [16,32,128] route_83).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_84
  · exact upper_85
  · exact upper_86

def route_75 : Route 10 := (fun mask => (mask,id))

theorem upper_75 : Upper D R [272,12,34,513,64] 13 := by
  apply routed_branch D R [272,12,34,513,64] 13 (by decide) (choices 1) [16,64,128] route_75
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,34,513,64] (choices 1) [16,64,128] route_75).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_76
  · exact upper_77
  · exact upper_83

def route_73 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_73 : Upper D R [272,12,34,513] 13 := by
  apply routed_branch D R [272,12,34,513] 13 (by decide) (choices 1) [32,64] route_73
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,34,513] (choices 1) [32,64] route_73).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_74
  · exact upper_75

def bound_90 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 14 38 536 241 225 225 225 481 737), lower := (rows 273 14 38 536 16 32 64 128 256 512), losses := [] }

theorem upper_90 : Upper D R [272,12,34,528] 13 :=
  bound_sound D R [272,12,34,528] 13 bound_90
    ((Boolean.boundCheck_true D R [272,12,34,528] 13 bound_90).mp (by decide +kernel))

def bound_91 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 14 38 552 209 241 209 209 465 721), lower := (rows 273 14 38 552 16 32 64 128 256 512), losses := [] }

theorem upper_91 : Upper D R [272,12,34,544] 13 :=
  bound_sound D R [272,12,34,544] 13 bound_91
    ((Boolean.boundCheck_true D R [272,12,34,544] 13 bound_91).mp (by decide +kernel))

def bound_92 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 14 38 584 241 241 241 241 497 753), lower := (rows 273 14 38 584 16 32 64 128 256 512), losses := [] }

theorem upper_92 : Upper D R [272,12,34,576] 13 :=
  bound_sound D R [272,12,34,576] 13 bound_92
    ((Boolean.boundCheck_true D R [272,12,34,576] 13 bound_92).mp (by decide +kernel))

def route_65 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_65 : Upper D R [272,12,34] 13 := by
  apply routed_branch D R [272,12,34] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,513,528,544,576] route_65
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,12,34] (choices 2) [17,33,48,65,80,96,192,513,528,544,576] route_65).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_66
  · exact upper_67
  · exact upper_68
  · exact upper_69
  · exact upper_70
  · exact upper_71
  · exact upper_72
  · exact upper_73
  · exact upper_90
  · exact upper_91
  · exact upper_92

def bound_93 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 14 52 747 755 739 739 739 995 739), lower := (rows 273 14 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_93 : Upper D R [272,12,48] 13 :=
  bound_sound D R [272,12,48] 13 bound_93
    ((Boolean.boundCheck_true D R [272,12,48] 13 bound_93).mp (by decide +kernel))

def bound_94 : Bound 10 := { allowed := (rows 224 240 144 240 0 0 0 0 0 0), upper := (rows 273 14 100 763 755 755 755 755 1011 755), lower := (rows 273 14 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_94 : Upper D R [272,12,96] 13 :=
  bound_sound D R [272,12,96] 13 bound_94
    ((Boolean.boundCheck_true D R [272,12,96] 13 bound_94).mp (by decide +kernel))

def bound_96 : Bound 10 := { allowed := (rows 224 240 224 224 0 0 0 0 0 0), upper := (rows 273 14 517 26 240 224 224 224 480 736), lower := (rows 273 14 517 26 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 5 8 0 1023 1023 1023 1023 1023), good := (rows 997 1006 997 1002 992 992 992 992 992 992) }] }

theorem upper_96 : Upper D R [272,12,513,18] 13 :=
  bound_sound D R [272,12,513,18] 13 bound_96
    ((Boolean.boundCheck_true D R [272,12,513,18] 13 bound_96).mp (by decide +kernel))

def bound_98 : Bound 10 := { allowed := (rows 192 240 208 208 0 0 0 0 0 0), upper := (rows 273 14 517 42 48 240 208 208 464 720), lower := (rows 273 14 517 42 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 21 8 16 0 81 145 273 529), good := (rows 981 14 965 10 981 0 64 128 256 512) }] }

theorem upper_98 : Upper D R [272,12,513,34,32] 13 :=
  bound_sound D R [272,12,513,34,32] 13 bound_98
    ((Boolean.boundCheck_true D R [272,12,513,34,32] 13 bound_98).mp (by decide +kernel))

def bound_100 : Bound 10 := { allowed := (rows 224 176 240 144 0 0 0 0 0 0), upper := (rows 273 14 517 42 80 48 224 224 480 736), lower := (rows 273 14 517 42 80 48 64 128 256 512), losses := [{ target := 6, region := (rows 1 6 4 12 16 49 0 128 256 512), good := (rows 305 14 559 42 48 48 0 128 256 512) }] }

theorem upper_100 : Upper D R [272,12,513,34,64,16] 13 :=
  bound_sound D R [272,12,513,34,64,16] 13 bound_100
    ((Boolean.boundCheck_true D R [272,12,513,34,64,16] 13 bound_100).mp (by decide +kernel))

def bound_102 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 14 517 42 80 96 80 160 416 672), lower := (rows 273 14 517 42 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 9 0 112 64 249 377 633), good := (rows 943 910 911 938 992 992 992 128 256 512) }] }

theorem upper_102 : Upper D R [272,12,513,34,64,64,16] 13 :=
  bound_sound D R [272,12,513,34,64,64,16] 13 bound_102
    ((Boolean.boundCheck_true D R [272,12,513,34,64,64,16] 13 bound_102).mp (by decide +kernel))

def bound_103 : Bound 10 := { allowed := (rows 224 224 240 192 0 0 0 0 0 0), upper := (rows 273 14 517 42 80 96 96 144 400 656), lower := (rows 273 14 517 42 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 6 4 14 0 1023 1023 128 256 512), good := (rows 353 110 623 106 96 96 96 224 352 608) }] }

theorem upper_103 : Upper D R [272,12,513,34,64,64,32] 13 :=
  bound_sound D R [272,12,513,34,64,64,32] 13 bound_103
    ((Boolean.boundCheck_true D R [272,12,513,34,64,64,32] 13 bound_103).mp (by decide +kernel))

def bound_105 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 273 14 517 42 80 96 192 144 416 672), lower := (rows 273 14 517 42 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 257 2 4 8 1023 0 1023 1023 256 512), good := (rows 465 222 725 218 208 208 208 208 465 720) }] }

theorem upper_105 : Upper D R [272,12,513,34,64,64,128,16] 13 :=
  bound_sound D R [272,12,513,34,64,64,128,16] 13 bound_105
    ((Boolean.boundCheck_true D R [272,12,513,34,64,64,128,16] 13 bound_105).mp (by decide +kernel))

def bound_106 : Bound 10 := { allowed := (rows 224 224 240 192 0 0 0 0 0 0), upper := (rows 273 14 517 42 80 96 192 160 400 656), lower := (rows 273 14 517 42 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 6 4 14 0 1023 1023 1023 256 512), good := (rows 481 238 751 234 224 224 224 224 480 736) }] }

theorem upper_106 : Upper D R [272,12,513,34,64,64,128,32] 13 :=
  bound_sound D R [272,12,513,34,64,64,128,32] 13 bound_106
    ((Boolean.boundCheck_true D R [272,12,513,34,64,64,128,32] 13 bound_106).mp (by decide +kernel))

def route_104 : Route 10 := (fun mask => (mask,id))

theorem upper_104 : Upper D R [272,12,513,34,64,64,128] 13 := by
  apply routed_branch D R [272,12,513,34,64,64,128] 13 (by decide) (choices 1) [16,32] route_104
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,513,34,64,64,128] (choices 1) [16,32] route_104).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_105
  · exact upper_106

def route_101 : Route 10 := (fun mask => (mask,id))

theorem upper_101 : Upper D R [272,12,513,34,64,64] 13 := by
  apply routed_branch D R [272,12,513,34,64,64] 13 (by decide) (choices 1) [16,32,128] route_101
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,513,34,64,64] (choices 1) [16,32,128] route_101).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_102
  · exact upper_103
  · exact upper_104

def bound_108 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 14 517 42 80 160 80 224 480 736), lower := (rows 273 14 517 42 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 13 0 241 64 208 336 592), good := (rows 943 14 559 42 992 160 992 160 256 512) }] }

theorem upper_108 : Upper D R [272,12,513,34,64,128,16] 13 :=
  bound_sound D R [272,12,513,34,64,128,16] 13 bound_108
    ((Boolean.boundCheck_true D R [272,12,513,34,64,128,16] 13 bound_108).mp (by decide +kernel))

def bound_109 : Bound 10 := { allowed := (rows 192 240 208 208 0 0 0 0 0 0), upper := (rows 273 14 517 42 80 160 96 208 464 720), lower := (rows 273 14 517 42 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 85 8 80 0 64 208 336 592), good := (rows 917 14 517 10 981 128 981 128 256 512) }] }

theorem upper_109 : Upper D R [272,12,513,34,64,128,32] 13 :=
  bound_sound D R [272,12,513,34,64,128,32] 13 bound_109
    ((Boolean.boundCheck_true D R [272,12,513,34,64,128,32] 13 bound_109).mp (by decide +kernel))

def bound_111 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 14 517 42 80 160 192 144 352 608), lower := (rows 273 14 517 42 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 5 8 0 224 224 128 504 760), good := (rows 773 782 517 874 864 992 992 992 256 512) }] }

theorem upper_111 : Upper D R [272,12,513,34,64,128,128,16] 13 :=
  bound_sound D R [272,12,513,34,64,128,128,16] 13 bound_111
    ((Boolean.boundCheck_true D R [272,12,513,34,64,128,128,16] 13 bound_111).mp (by decide +kernel))

def bound_112 : Bound 10 := { allowed := (rows 224 224 240 192 0 0 0 0 0 0), upper := (rows 273 14 517 42 80 160 192 160 336 592), lower := (rows 273 14 517 42 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 6 4 14 0 1023 1023 1023 256 512), good := (rows 481 238 751 234 224 224 224 224 480 736) }] }

theorem upper_112 : Upper D R [272,12,513,34,64,128,128,32] 13 :=
  bound_sound D R [272,12,513,34,64,128,128,32] 13 bound_112
    ((Boolean.boundCheck_true D R [272,12,513,34,64,128,128,32] 13 bound_112).mp (by decide +kernel))

def bound_113 : Bound 10 := { allowed := (rows 224 224 240 192 0 0 0 0 0 0), upper := (rows 273 14 517 42 80 160 192 192 304 560), lower := (rows 273 14 517 42 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 6 4 14 0 1023 1023 1023 256 512), good := (rows 481 238 751 234 224 224 224 224 480 736) }] }

theorem upper_113 : Upper D R [272,12,513,34,64,128,128,64] 13 :=
  bound_sound D R [272,12,513,34,64,128,128,64] 13 bound_113
    ((Boolean.boundCheck_true D R [272,12,513,34,64,128,128,64] 13 bound_113).mp (by decide +kernel))

def route_110 : Route 10 := (fun mask => (mask,id))

theorem upper_110 : Upper D R [272,12,513,34,64,128,128] 13 := by
  apply routed_branch D R [272,12,513,34,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_110
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,513,34,64,128,128] (choices 1) [16,32,64] route_110).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_111
  · exact upper_112
  · exact upper_113

def route_107 : Route 10 := (fun mask => (mask,id))

theorem upper_107 : Upper D R [272,12,513,34,64,128] 13 := by
  apply routed_branch D R [272,12,513,34,64,128] 13 (by decide) (choices 1) [16,32,128] route_107
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,513,34,64,128] (choices 1) [16,32,128] route_107).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_108
  · exact upper_109
  · exact upper_110

def route_99 : Route 10 := (fun mask => (mask,id))

theorem upper_99 : Upper D R [272,12,513,34,64] 13 := by
  apply routed_branch D R [272,12,513,34,64] 13 (by decide) (choices 1) [16,64,128] route_99
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,513,34,64] (choices 1) [16,64,128] route_99).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_100
  · exact upper_101
  · exact upper_107

def route_97 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_97 : Upper D R [272,12,513,34] 13 := by
  apply routed_branch D R [272,12,513,34] 13 (by decide) (choices 1) [32,64] route_97
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,513,34] (choices 1) [32,64] route_97).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_98
  · exact upper_99

def bound_114 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 14 517 56 242 226 226 226 482 738), lower := (rows 273 14 517 56 16 32 64 128 256 512), losses := [] }

theorem upper_114 : Upper D R [272,12,513,48] 13 :=
  bound_sound D R [272,12,513,48] 13 bound_114
    ((Boolean.boundCheck_true D R [272,12,513,48] 13 bound_114).mp (by decide +kernel))

def bound_115 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 273 14 517 104 242 242 242 242 498 754), lower := (rows 273 14 517 104 16 32 64 128 256 512), losses := [] }

theorem upper_115 : Upper D R [272,12,513,96] 13 :=
  bound_sound D R [272,12,513,96] 13 bound_115
    ((Boolean.boundCheck_true D R [272,12,513,96] 13 bound_115).mp (by decide +kernel))

def route_95 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_95 : Upper D R [272,12,513] 13 := by
  apply routed_branch D R [272,12,513] 13 (by decide) (choices 2) [18,34,48,96] route_95
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,12,513] (choices 2) [18,34,48,96] route_95).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_96
  · exact upper_97
  · exact upper_114
  · exact upper_115

def bound_117 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 273 14 518 25 240 224 224 224 480 736), lower := (rows 273 14 518 25 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 10 14 8 0 1023 1023 1023 1023 1023), good := (rows 993 1006 998 1007 992 992 992 992 992 992) }] }

theorem upper_117 : Upper D R [272,12,514,17] 13 :=
  bound_sound D R [272,12,514,17] 13 bound_117
    ((Boolean.boundCheck_true D R [272,12,514,17] 13 bound_117).mp (by decide +kernel))

def bound_119 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 273 14 518 41 48 240 208 208 464 720), lower := (rows 273 14 518 41 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 10 12 8 16 0 81 145 273 529), good := (rows 977 14 518 975 977 0 64 128 256 512) }] }

theorem upper_119 : Upper D R [272,12,514,33,32] 13 :=
  bound_sound D R [272,12,514,33,32] 13 bound_119
    ((Boolean.boundCheck_true D R [272,12,514,33,32] 13 bound_119).mp (by decide +kernel))

def bound_121 : Bound 10 := { allowed := (rows 224 224 224 208 0 0 0 0 0 0), upper := (rows 273 14 518 41 80 48 224 224 480 736), lower := (rows 273 14 518 41 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 10 14 8 0 32 104 168 296 552), good := (rows 257 974 518 1007 64 992 64 128 256 512) }] }

theorem upper_121 : Upper D R [272,12,514,33,64,16] 13 :=
  bound_sound D R [272,12,514,33,64,16] 13 bound_121
    ((Boolean.boundCheck_true D R [272,12,514,33,64,16] 13 bound_121).mp (by decide +kernel))

def bound_122 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 14 518 41 80 96 240 176 432 688), lower := (rows 273 14 518 41 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 112 64 128 256 512), good := (rows 297 14 518 41 96 96 96 128 256 512) }] }

theorem upper_122 : Upper D R [272,12,514,33,64,64] 13 :=
  bound_sound D R [272,12,514,33,64,64] 13 bound_122
    ((Boolean.boundCheck_true D R [272,12,514,33,64,64] 13 bound_122).mp (by decide +kernel))

def bound_124 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 273 14 518 41 80 160 80 224 480 736), lower := (rows 273 14 518 41 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 5 9 0 241 64 208 336 592), good := (rows 943 14 518 47 992 160 992 160 256 512) }] }

theorem upper_124 : Upper D R [272,12,514,33,64,128,16] 13 :=
  bound_sound D R [272,12,514,33,64,128,16] 13 bound_124
    ((Boolean.boundCheck_true D R [272,12,514,33,64,128,16] 13 bound_124).mp (by decide +kernel))

def bound_125 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 273 14 518 41 80 160 96 208 464 720), lower := (rows 273 14 518 41 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 14 518 9 977 128 977 128 256 512) }] }

theorem upper_125 : Upper D R [272,12,514,33,64,128,32] 13 :=
  bound_sound D R [272,12,514,33,64,128,32] 13 bound_125
    ((Boolean.boundCheck_true D R [272,12,514,33,64,128,32] 13 bound_125).mp (by decide +kernel))

def bound_127 : Bound 10 := { allowed := (rows 224 224 224 208 0 0 0 0 0 0), upper := (rows 273 14 518 41 80 160 192 144 352 608), lower := (rows 273 14 518 41 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 10 14 8 0 224 224 128 504 760), good := (rows 769 782 518 879 864 992 992 992 256 512) }] }

theorem upper_127 : Upper D R [272,12,514,33,64,128,128,16] 13 :=
  bound_sound D R [272,12,514,33,64,128,128,16] 13 bound_127
    ((Boolean.boundCheck_true D R [272,12,514,33,64,128,128,16] 13 bound_127).mp (by decide +kernel))

def bound_128 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 14 518 41 80 160 192 160 336 592), lower := (rows 273 14 518 41 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 1023 256 512), good := (rows 489 238 742 233 224 224 224 224 480 736) }] }

theorem upper_128 : Upper D R [272,12,514,33,64,128,128,32] 13 :=
  bound_sound D R [272,12,514,33,64,128,128,32] 13 bound_128
    ((Boolean.boundCheck_true D R [272,12,514,33,64,128,128,32] 13 bound_128).mp (by decide +kernel))

def bound_129 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 14 518 41 80 160 192 192 304 560), lower := (rows 273 14 518 41 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 1023 256 512), good := (rows 489 238 742 233 224 224 224 224 480 736) }] }

theorem upper_129 : Upper D R [272,12,514,33,64,128,128,64] 13 :=
  bound_sound D R [272,12,514,33,64,128,128,64] 13 bound_129
    ((Boolean.boundCheck_true D R [272,12,514,33,64,128,128,64] 13 bound_129).mp (by decide +kernel))

def route_126 : Route 10 := (fun mask => (mask,id))

theorem upper_126 : Upper D R [272,12,514,33,64,128,128] 13 := by
  apply routed_branch D R [272,12,514,33,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_126
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,514,33,64,128,128] (choices 1) [16,32,64] route_126).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_127
  · exact upper_128
  · exact upper_129

def route_123 : Route 10 := (fun mask => (mask,id))

theorem upper_123 : Upper D R [272,12,514,33,64,128] 13 := by
  apply routed_branch D R [272,12,514,33,64,128] 13 (by decide) (choices 1) [16,32,128] route_123
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,514,33,64,128] (choices 1) [16,32,128] route_123).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_124
  · exact upper_125
  · exact upper_126

def route_120 : Route 10 := (fun mask => (mask,id))

theorem upper_120 : Upper D R [272,12,514,33,64] 13 := by
  apply routed_branch D R [272,12,514,33,64] 13 (by decide) (choices 1) [16,64,128] route_120
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,514,33,64] (choices 1) [16,64,128] route_120).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_121
  · exact upper_122
  · exact upper_123

def route_118 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_118 : Upper D R [272,12,514,33] 13 := by
  apply routed_branch D R [272,12,514,33] 13 (by decide) (choices 1) [32,64] route_118
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,514,33] (choices 1) [32,64] route_118).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_119
  · exact upper_120

def bound_130 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 273 14 518 56 241 225 225 225 481 737), lower := (rows 273 14 518 56 16 32 64 128 256 512), losses := [] }

theorem upper_130 : Upper D R [272,12,514,48] 13 :=
  bound_sound D R [272,12,514,48] 13 bound_130
    ((Boolean.boundCheck_true D R [272,12,514,48] 13 bound_130).mp (by decide +kernel))

def bound_131 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 273 14 518 104 241 241 241 241 497 753), lower := (rows 273 14 518 104 16 32 64 128 256 512), losses := [] }

theorem upper_131 : Upper D R [272,12,514,96] 13 :=
  bound_sound D R [272,12,514,96] 13 bound_131
    ((Boolean.boundCheck_true D R [272,12,514,96] 13 bound_131).mp (by decide +kernel))

def route_116 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_116 : Upper D R [272,12,514] 13 := by
  apply routed_branch D R [272,12,514] 13 (by decide) (choices 2) [17,33,48,96] route_116
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,12,514] (choices 2) [17,33,48,96] route_116).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_117
  · exact upper_118
  · exact upper_130
  · exact upper_131

def bound_136 : Bound 10 := { allowed := (rows 192 208 192 208 0 0 0 0 0 0), upper := (rows 273 14 532 11 48 96 96 192 448 704), lower := (rows 273 14 532 11 48 96 96 128 256 512), losses := [{ target := 5, region := (rows 17 23 20 29 16 0 64 224 352 608), good := (rows 287 14 543 11 927 960 960 128 256 512) }] }

theorem upper_136 : Upper D R [272,12,528,3,32,64,32] 13 :=
  bound_sound D R [272,12,528,3,32,64,32] 13 bound_136
    ((Boolean.boundCheck_true D R [272,12,528,3,32,64,32] 13 bound_136).mp (by decide +kernel))

def bound_139 : Bound 10 := { allowed := (rows 192 208 224 208 0 0 0 0 0 0), upper := (rows 273 14 532 11 48 96 192 160 320 640), lower := (rows 273 14 532 11 48 96 192 160 320 512), losses := [{ target := 5, region := (rows 17 6 4 12 16 0 192 128 480 704), good := (rows 273 14 543 11 273 832 960 960 832 512) }] }

theorem upper_139 : Upper D R [272,12,528,3,32,64,128,32,64] 13 :=
  bound_sound D R [272,12,528,3,32,64,128,32,64] 13 bound_139
    ((Boolean.boundCheck_true D R [272,12,528,3,32,64,128,32,64] 13 bound_139).mp (by decide +kernel))

def bound_140 : Bound 10 := { allowed := (rows 224 208 192 208 0 0 0 0 0 0), upper := (rows 273 14 532 11 48 96 192 160 384 576), lower := (rows 273 14 532 11 48 96 192 160 384 512), losses := [{ target := 5, region := (rows 1 11 21 9 16 0 448 128 448 993), good := (rows 863 14 532 527 532 832 960 960 960 512) }] }

theorem upper_140 : Upper D R [272,12,528,3,32,64,128,32,128] 13 :=
  bound_sound D R [272,12,528,3,32,64,128,32,128] 13 bound_140
    ((Boolean.boundCheck_true D R [272,12,528,3,32,64,128,32,128] 13 bound_140).mp (by decide +kernel))

def route_138 : Route 10 := (fun mask => (mask,id))

theorem upper_138 : Upper D R [272,12,528,3,32,64,128,32] 13 := by
  apply routed_branch D R [272,12,528,3,32,64,128,32] 13 (by decide) (choices 1) [64,128] route_138
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,528,3,32,64,128,32] (choices 1) [64,128] route_138).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_139
  · exact upper_140

def bound_142 : Bound 10 := { allowed := (rows 224 208 192 208 0 0 0 0 0 0), upper := (rows 273 14 532 11 48 96 192 192 288 640), lower := (rows 273 14 532 11 48 96 192 192 288 512), losses := [{ target := 5, region := (rows 1 11 21 9 16 0 1023 1023 256 1023), good := (rows 991 718 724 719 724 704 704 704 960 704) }] }

theorem upper_142 : Upper D R [272,12,528,3,32,64,128,64,32] 13 :=
  bound_sound D R [272,12,528,3,32,64,128,64,32] 13 bound_142
    ((Boolean.boundCheck_true D R [272,12,528,3,32,64,128,64,32] 13 bound_142).mp (by decide +kernel))

def bound_143 : Bound 10 := { allowed := (rows 192 208 224 208 0 0 0 0 0 0), upper := (rows 273 14 532 11 48 96 192 192 384 544), lower := (rows 273 14 532 11 48 96 192 192 384 512), losses := [{ target := 5, region := (rows 21 6 4 14 16 0 1023 1023 1023 512), good := (rows 465 463 991 459 465 448 448 448 448 960) }] }

theorem upper_143 : Upper D R [272,12,528,3,32,64,128,64,128] 13 :=
  bound_sound D R [272,12,528,3,32,64,128,64,128] 13 bound_143
    ((Boolean.boundCheck_true D R [272,12,528,3,32,64,128,64,128] 13 bound_143).mp (by decide +kernel))

def route_141 : Route 10 := (fun mask => (mask,id))

theorem upper_141 : Upper D R [272,12,528,3,32,64,128,64] 13 := by
  apply routed_branch D R [272,12,528,3,32,64,128,64] 13 (by decide) (choices 1) [32,128] route_141
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,528,3,32,64,128,64] (choices 1) [32,128] route_141).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_142
  · exact upper_143

def route_137 : Route 10 := (fun mask => (mask,id))

theorem upper_137 : Upper D R [272,12,528,3,32,64,128] 13 := by
  apply routed_branch D R [272,12,528,3,32,64,128] 13 (by decide) (choices 1) [32,64] route_137
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,528,3,32,64,128] (choices 1) [32,64] route_137).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_138
  · exact upper_141

def route_135 : Route 10 := (fun mask => (mask,id))

theorem upper_135 : Upper D R [272,12,528,3,32,64] 13 := by
  apply routed_branch D R [272,12,528,3,32,64] 13 (by decide) (choices 1) [32,128] route_135
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,528,3,32,64] (choices 1) [32,128] route_135).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_136
  · exact upper_137

def route_134 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_134 : Upper D R [272,12,528,3,32] 13 := by
  apply routed_branch D R [272,12,528,3,32] 13 (by decide) (choices 1) [64] route_134
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,528,3,32] (choices 1) [64] route_134).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_135

def route_133 : Route 10 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 128 => (32,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_133 : Upper D R [272,12,528,3] 13 := by
  apply routed_branch D R [272,12,528,3] 13 (by decide) (choices 1) [32] route_133
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,528,3] (choices 1) [32] route_133).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_134

def bound_144 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 14 532 41 242 226 226 226 482 738), lower := (rows 273 14 532 41 16 32 64 128 256 512), losses := [] }

theorem upper_144 : Upper D R [272,12,528,33] 13 :=
  bound_sound D R [272,12,528,33] 13 bound_144
    ((Boolean.boundCheck_true D R [272,12,528,33] 13 bound_144).mp (by decide +kernel))

def bound_145 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 273 14 532 42 241 225 225 225 481 737), lower := (rows 273 14 532 42 16 32 64 128 256 512), losses := [] }

theorem upper_145 : Upper D R [272,12,528,34] 13 :=
  bound_sound D R [272,12,528,34] 13 bound_145
    ((Boolean.boundCheck_true D R [272,12,528,34] 13 bound_145).mp (by decide +kernel))

def bound_146 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 273 14 532 104 243 227 227 227 483 739), lower := (rows 273 14 532 104 16 32 64 128 256 512), losses := [] }

theorem upper_146 : Upper D R [272,12,528,96] 13 :=
  bound_sound D R [272,12,528,96] 13 bound_146
    ((Boolean.boundCheck_true D R [272,12,528,96] 13 bound_146).mp (by decide +kernel))

def route_132 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_132 : Upper D R [272,12,528] 13 := by
  apply routed_branch D R [272,12,528] 13 (by decide) (choices 2) [3,33,34,96] route_132
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,12,528] (choices 2) [3,33,34,96] route_132).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_133
  · exact upper_144
  · exact upper_145
  · exact upper_146

def bound_149 : Bound 10 := { allowed := (rows 192 240 208 240 0 0 0 0 0 0), upper := (rows 273 14 548 11 48 240 208 208 464 720), lower := (rows 273 14 548 11 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 2 4 8 16 0 81 145 273 529), good := (rows 977 14 516 971 977 0 64 128 256 512) }] }

theorem upper_149 : Upper D R [272,12,544,3,32] 13 :=
  bound_sound D R [272,12,544,3,32] 13 bound_149
    ((Boolean.boundCheck_true D R [272,12,544,3,32] 13 bound_149).mp (by decide +kernel))

def bound_151 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 14 548 11 80 48 224 224 480 736), lower := (rows 273 14 548 11 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 100 164 292 548), good := (rows 257 974 996 11 64 996 64 128 256 512) }] }

theorem upper_151 : Upper D R [272,12,544,3,64,16] 13 :=
  bound_sound D R [272,12,544,3,64,16] 13 bound_151
    ((Boolean.boundCheck_true D R [272,12,544,3,64,16] 13 bound_151).mp (by decide +kernel))

def bound_153 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 273 14 548 11 80 96 80 160 416 672), lower := (rows 273 14 548 11 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 117 9 0 112 64 245 373 629), good := (rows 943 910 932 911 996 996 996 128 256 512) }] }

theorem upper_153 : Upper D R [272,12,544,3,64,64,16] 13 :=
  bound_sound D R [272,12,544,3,64,64,16] 13 bound_153
    ((Boolean.boundCheck_true D R [272,12,544,3,64,64,16] 13 bound_153).mp (by decide +kernel))

def bound_154 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 14 548 11 80 96 96 144 400 656), lower := (rows 273 14 548 11 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 516 8 0 1023 1023 128 256 512), good := (rows 353 110 612 107 96 96 96 224 352 612) }] }

theorem upper_154 : Upper D R [272,12,544,3,64,64,32] 13 :=
  bound_sound D R [272,12,544,3,64,64,32] 13 bound_154
    ((Boolean.boundCheck_true D R [272,12,544,3,64,64,32] 13 bound_154).mp (by decide +kernel))

def bound_156 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 273 14 548 11 80 96 192 144 416 672), lower := (rows 273 14 548 11 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 1 3 244 9 0 240 192 128 448 704), good := (rows 303 14 548 11 868 868 996 996 256 512) }] }

theorem upper_156 : Upper D R [272,12,544,3,64,64,128,16] 13 :=
  bound_sound D R [272,12,544,3,64,64,128,16] 13 bound_156
    ((Boolean.boundCheck_true D R [272,12,544,3,64,64,128,16] 13 bound_156).mp (by decide +kernel))

def bound_157 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 14 548 11 80 96 192 160 400 656), lower := (rows 273 14 548 11 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 516 8 0 1023 1023 1023 256 512), good := (rows 481 238 740 235 224 224 224 224 480 740) }] }

theorem upper_157 : Upper D R [272,12,544,3,64,64,128,32] 13 :=
  bound_sound D R [272,12,544,3,64,64,128,32] 13 bound_157
    ((Boolean.boundCheck_true D R [272,12,544,3,64,64,128,32] 13 bound_157).mp (by decide +kernel))

def route_155 : Route 10 := (fun mask => (mask,id))

theorem upper_155 : Upper D R [272,12,544,3,64,64,128] 13 := by
  apply routed_branch D R [272,12,544,3,64,64,128] 13 (by decide) (choices 1) [16,32] route_155
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,544,3,64,64,128] (choices 1) [16,32] route_155).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_156
  · exact upper_157

def route_152 : Route 10 := (fun mask => (mask,id))

theorem upper_152 : Upper D R [272,12,544,3,64,64] 13 := by
  apply routed_branch D R [272,12,544,3,64,64] 13 (by decide) (choices 1) [16,32,128] route_152
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,544,3,64,64] (choices 1) [16,32,128] route_152).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_153
  · exact upper_154
  · exact upper_155

def bound_159 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 273 14 548 11 80 160 80 224 480 736), lower := (rows 273 14 548 11 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 85 9 0 241 64 208 336 592), good := (rows 943 14 548 47 996 160 996 160 256 512) }] }

theorem upper_159 : Upper D R [272,12,544,3,64,128,16] 13 :=
  bound_sound D R [272,12,544,3,64,128,16] 13 bound_159
    ((Boolean.boundCheck_true D R [272,12,544,3,64,128,16] 13 bound_159).mp (by decide +kernel))

def bound_160 : Bound 10 := { allowed := (rows 192 240 208 240 0 0 0 0 0 0), upper := (rows 273 14 548 11 80 160 96 208 464 720), lower := (rows 273 14 548 11 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 2 4 8 80 0 64 208 336 592), good := (rows 913 14 516 11 977 128 977 128 256 512) }] }

theorem upper_160 : Upper D R [272,12,544,3,64,128,32] 13 :=
  bound_sound D R [272,12,544,3,64,128,32] 13 bound_160
    ((Boolean.boundCheck_true D R [272,12,544,3,64,128,32] 13 bound_160).mp (by decide +kernel))

def bound_162 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 273 14 548 11 80 160 192 144 352 608), lower := (rows 273 14 548 11 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 3 244 9 0 224 224 128 500 756), good := (rows 783 782 868 11 868 996 996 996 256 512) }] }

theorem upper_162 : Upper D R [272,12,544,3,64,128,128,16] 13 :=
  bound_sound D R [272,12,544,3,64,128,128,16] 13 bound_162
    ((Boolean.boundCheck_true D R [272,12,544,3,64,128,128,16] 13 bound_162).mp (by decide +kernel))

def bound_163 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 14 548 11 80 160 192 160 336 592), lower := (rows 273 14 548 11 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 516 8 0 1023 1023 1023 256 512), good := (rows 481 238 740 235 224 224 224 224 480 740) }] }

theorem upper_163 : Upper D R [272,12,544,3,64,128,128,32] 13 :=
  bound_sound D R [272,12,544,3,64,128,128,32] 13 bound_163
    ((Boolean.boundCheck_true D R [272,12,544,3,64,128,128,32] 13 bound_163).mp (by decide +kernel))

def bound_164 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 273 14 548 11 80 160 192 192 304 560), lower := (rows 273 14 548 11 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 516 8 0 1023 1023 1023 256 512), good := (rows 481 238 740 235 224 224 224 224 480 740) }] }

theorem upper_164 : Upper D R [272,12,544,3,64,128,128,64] 13 :=
  bound_sound D R [272,12,544,3,64,128,128,64] 13 bound_164
    ((Boolean.boundCheck_true D R [272,12,544,3,64,128,128,64] 13 bound_164).mp (by decide +kernel))

def route_161 : Route 10 := (fun mask => (mask,id))

theorem upper_161 : Upper D R [272,12,544,3,64,128,128] 13 := by
  apply routed_branch D R [272,12,544,3,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_161
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,544,3,64,128,128] (choices 1) [16,32,64] route_161).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_162
  · exact upper_163
  · exact upper_164

def route_158 : Route 10 := (fun mask => (mask,id))

theorem upper_158 : Upper D R [272,12,544,3,64,128] 13 := by
  apply routed_branch D R [272,12,544,3,64,128] 13 (by decide) (choices 1) [16,32,128] route_158
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,544,3,64,128] (choices 1) [16,32,128] route_158).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_159
  · exact upper_160
  · exact upper_161

def route_150 : Route 10 := (fun mask => (mask,id))

theorem upper_150 : Upper D R [272,12,544,3,64] 13 := by
  apply routed_branch D R [272,12,544,3,64] 13 (by decide) (choices 1) [16,64,128] route_150
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,544,3,64] (choices 1) [16,64,128] route_150).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_151
  · exact upper_152
  · exact upper_158

def route_148 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_148 : Upper D R [272,12,544,3] 13 := by
  apply routed_branch D R [272,12,544,3] 13 (by decide) (choices 1) [32,64] route_148
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [272,12,544,3] (choices 1) [32,64] route_148).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_149
  · exact upper_150

def bound_165 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 14 548 25 242 226 226 226 482 738), lower := (rows 273 14 548 25 16 32 64 128 256 512), losses := [] }

theorem upper_165 : Upper D R [272,12,544,17] 13 :=
  bound_sound D R [272,12,544,17] 13 bound_165
    ((Boolean.boundCheck_true D R [272,12,544,17] 13 bound_165).mp (by decide +kernel))

def bound_166 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 273 14 548 26 241 225 225 225 481 737), lower := (rows 273 14 548 26 16 32 64 128 256 512), losses := [] }

theorem upper_166 : Upper D R [272,12,544,18] 13 :=
  bound_sound D R [272,12,544,18] 13 bound_166
    ((Boolean.boundCheck_true D R [272,12,544,18] 13 bound_166).mp (by decide +kernel))

def bound_167 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 14 548 41 210 242 210 210 466 722), lower := (rows 273 14 548 41 16 32 64 128 256 512), losses := [] }

theorem upper_167 : Upper D R [272,12,544,33] 13 :=
  bound_sound D R [272,12,544,33] 13 bound_167
    ((Boolean.boundCheck_true D R [272,12,544,33] 13 bound_167).mp (by decide +kernel))

def bound_168 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 273 14 548 42 209 241 209 209 465 721), lower := (rows 273 14 548 42 16 32 64 128 256 512), losses := [] }

theorem upper_168 : Upper D R [272,12,544,34] 13 :=
  bound_sound D R [272,12,544,34] 13 bound_168
    ((Boolean.boundCheck_true D R [272,12,544,34] 13 bound_168).mp (by decide +kernel))

def bound_169 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 273 14 548 56 211 227 195 195 451 707), lower := (rows 273 14 548 56 16 32 64 128 256 512), losses := [] }

theorem upper_169 : Upper D R [272,12,544,48] 13 :=
  bound_sound D R [272,12,544,48] 13 bound_169
    ((Boolean.boundCheck_true D R [272,12,544,48] 13 bound_169).mp (by decide +kernel))

def bound_170 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 14 548 73 242 242 242 242 498 754), lower := (rows 273 14 548 73 16 32 64 128 256 512), losses := [] }

theorem upper_170 : Upper D R [272,12,544,65] 13 :=
  bound_sound D R [272,12,544,65] 13 bound_170
    ((Boolean.boundCheck_true D R [272,12,544,65] 13 bound_170).mp (by decide +kernel))

def bound_171 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 273 14 548 74 241 241 241 241 497 753), lower := (rows 273 14 548 74 16 32 64 128 256 512), losses := [] }

theorem upper_171 : Upper D R [272,12,544,66] 13 :=
  bound_sound D R [272,12,544,66] 13 bound_171
    ((Boolean.boundCheck_true D R [272,12,544,66] 13 bound_171).mp (by decide +kernel))

def bound_172 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 273 14 548 88 243 227 227 227 483 739), lower := (rows 273 14 548 88 16 32 64 128 256 512), losses := [] }

theorem upper_172 : Upper D R [272,12,544,80] 13 :=
  bound_sound D R [272,12,544,80] 13 bound_172
    ((Boolean.boundCheck_true D R [272,12,544,80] 13 bound_172).mp (by decide +kernel))

def bound_173 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 273 14 548 104 211 243 211 211 467 723), lower := (rows 273 14 548 104 16 32 64 128 256 512), losses := [] }

theorem upper_173 : Upper D R [272,12,544,96] 13 :=
  bound_sound D R [272,12,544,96] 13 bound_173
    ((Boolean.boundCheck_true D R [272,12,544,96] 13 bound_173).mp (by decide +kernel))

def bound_174 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 273 14 548 200 243 243 243 243 499 755), lower := (rows 273 14 548 200 16 32 64 128 256 512), losses := [] }

theorem upper_174 : Upper D R [272,12,544,192] 13 :=
  bound_sound D R [272,12,544,192] 13 bound_174
    ((Boolean.boundCheck_true D R [272,12,544,192] 13 bound_174).mp (by decide +kernel))

def route_147 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_147 : Upper D R [272,12,544] 13 := by
  apply routed_branch D R [272,12,544] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] route_147
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,12,544] (choices 2) [3,17,18,33,34,48,65,66,80,96,192] route_147).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_148
  · exact upper_165
  · exact upper_166
  · exact upper_167
  · exact upper_168
  · exact upper_169
  · exact upper_170
  · exact upper_171
  · exact upper_172
  · exact upper_173
  · exact upper_174

def route_0 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [272,12] 13 := by
  apply routed_branch D R [272,12] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,513,514,528,544] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,12] (choices 2) [3,17,18,33,34,48,96,513,514,528,544] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_32
  · exact upper_37
  · exact upper_42
  · exact upper_65
  · exact upper_93
  · exact upper_94
  · exact upper_95
  · exact upper_116
  · exact upper_132
  · exact upper_147

theorem upper : Upper D R [272,12] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case44
