import IrregularTen14Base

namespace Delivery.IrregularTen14.Case38
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 259 22 13 56 752 736 736 736 992 736), lower := (rows 259 22 13 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [258,20,9,48] 13 :=
  bound_sound D R [258,20,9,48] 13 bound_2
    ((Boolean.boundCheck_true D R [258,20,9,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 240 224 240 144 0 0 0 0 0 0), upper := (rows 259 22 13 104 752 752 752 752 1008 752), lower := (rows 259 22 13 104 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [258,20,9,96] 13 :=
  bound_sound D R [258,20,9,96] 13 bound_3
    ((Boolean.boundCheck_true D R [258,20,9,96] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 224 240 224 0 0 0 0 0 0), upper := (rows 259 22 13 536 240 224 224 224 480 736), lower := (rows 259 22 13 536 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 4 8 0 1023 1023 1023 1023 1023), good := (rows 995 999 1005 1000 992 992 992 992 992 992) }] }

theorem upper_4 : Upper D R [258,20,9,528] 13 :=
  bound_sound D R [258,20,9,528] 13 bound_4
    ((Boolean.boundCheck_true D R [258,20,9,528] 13 bound_4).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 208 224 240 208 0 0 0 0 0 0), upper := (rows 259 22 13 552 48 240 208 208 464 720), lower := (rows 259 22 13 552 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 16 0 82 146 274 530), good := (rows 963 983 13 520 976 0 64 128 256 512) }] }

theorem upper_6 : Upper D R [258,20,9,544,32] 13 :=
  bound_sound D R [258,20,9,544,32] 13 bound_6
    ((Boolean.boundCheck_true D R [258,20,9,544,32] 13 bound_6).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 259 22 13 552 80 48 224 224 480 736), lower := (rows 259 22 13 552 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 40 0 32 104 168 296 552), good := (rows 259 6 973 1000 64 1000 64 128 256 512) }] }

theorem upper_8 : Upper D R [258,20,9,544,64,16] 13 :=
  bound_sound D R [258,20,9,544,64,16] 13 bound_8
    ((Boolean.boundCheck_true D R [258,20,9,544,64,16] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 259 22 13 552 80 96 80 160 416 672), lower := (rows 259 22 13 552 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 122 0 112 64 250 378 634), good := (rows 911 943 909 936 1000 1000 1000 128 256 512) }] }

theorem upper_10 : Upper D R [258,20,9,544,64,64,16] 13 :=
  bound_sound D R [258,20,9,544,64,64,16] 13 bound_10
    ((Boolean.boundCheck_true D R [258,20,9,544,64,64,16] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 259 22 13 552 80 96 96 144 400 656), lower := (rows 259 22 13 552 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 128 256 512), good := (rows 355 102 109 616 96 96 96 224 352 616) }] }

theorem upper_11 : Upper D R [258,20,9,544,64,64,32] 13 :=
  bound_sound D R [258,20,9,544,64,64,32] 13 bound_11
    ((Boolean.boundCheck_true D R [258,20,9,544,64,64,32] 13 bound_11).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 259 22 13 552 80 96 192 144 416 672), lower := (rows 259 22 13 552 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 4 248 0 240 192 128 448 704), good := (rows 259 46 13 552 872 872 1000 1000 256 512) }] }

theorem upper_13 : Upper D R [258,20,9,544,64,64,128,16] 13 :=
  bound_sound D R [258,20,9,544,64,64,128,16] 13 bound_13
    ((Boolean.boundCheck_true D R [258,20,9,544,64,64,128,16] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 259 22 13 552 80 96 192 160 400 656), lower := (rows 259 22 13 552 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 483 230 237 744 224 224 224 224 480 744) }] }

theorem upper_14 : Upper D R [258,20,9,544,64,64,128,32] 13 :=
  bound_sound D R [258,20,9,544,64,64,128,32] 13 bound_14
    ((Boolean.boundCheck_true D R [258,20,9,544,64,64,128,32] 13 bound_14).mp (by decide +kernel))

def route_12 : Route 10 := (fun mask => (mask,id))

theorem upper_12 : Upper D R [258,20,9,544,64,64,128] 13 := by
  apply routed_branch D R [258,20,9,544,64,64,128] 13 (by decide) (choices 1) [16,32] route_12
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,9,544,64,64,128] (choices 1) [16,32] route_12).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_13
  · exact upper_14

def route_9 : Route 10 := (fun mask => (mask,id))

theorem upper_9 : Upper D R [258,20,9,544,64,64] 13 := by
  apply routed_branch D R [258,20,9,544,64,64] 13 (by decide) (choices 1) [16,32,128] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,9,544,64,64] (choices 1) [16,32,128] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_10
  · exact upper_11
  · exact upper_12

def bound_16 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 259 22 13 552 80 160 80 224 480 736), lower := (rows 259 22 13 552 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 90 0 242 64 208 336 592), good := (rows 303 943 13 552 1000 160 1000 160 256 512) }] }

theorem upper_16 : Upper D R [258,20,9,544,64,128,16] 13 :=
  bound_sound D R [258,20,9,544,64,128,16] 13 bound_16
    ((Boolean.boundCheck_true D R [258,20,9,544,64,128,16] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 208 224 240 208 0 0 0 0 0 0), upper := (rows 259 22 13 552 80 160 96 208 464 720), lower := (rows 259 22 13 552 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 80 0 64 208 336 592), good := (rows 259 919 13 520 976 128 976 128 256 512) }] }

theorem upper_17 : Upper D R [258,20,9,544,64,128,32] 13 :=
  bound_sound D R [258,20,9,544,64,128,32] 13 bound_17
    ((Boolean.boundCheck_true D R [258,20,9,544,64,128,32] 13 bound_17).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 240 192 240 208 0 0 0 0 0 0), upper := (rows 259 22 13 552 80 160 192 240 368 624), lower := (rows 259 22 13 552 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 1 6 4 8 248 0 224 128 256 512), good := (rows 259 22 31 600 80 208 208 208 256 512) }] }

theorem upper_18 : Upper D R [258,20,9,544,64,128,128] 13 :=
  bound_sound D R [258,20,9,544,64,128,128] 13 bound_18
    ((Boolean.boundCheck_true D R [258,20,9,544,64,128,128] 13 bound_18).mp (by decide +kernel))

def route_15 : Route 10 := (fun mask => (mask,id))

theorem upper_15 : Upper D R [258,20,9,544,64,128] 13 := by
  apply routed_branch D R [258,20,9,544,64,128] 13 (by decide) (choices 1) [16,32,128] route_15
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,9,544,64,128] (choices 1) [16,32,128] route_15).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_16
  · exact upper_17
  · exact upper_18

def route_7 : Route 10 := (fun mask => (mask,id))

theorem upper_7 : Upper D R [258,20,9,544,64] 13 := by
  apply routed_branch D R [258,20,9,544,64] 13 (by decide) (choices 1) [16,64,128] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,9,544,64] (choices 1) [16,64,128] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_8
  · exact upper_9
  · exact upper_15

def route_5 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_5 : Upper D R [258,20,9,544] 13 := by
  apply routed_branch D R [258,20,9,544] 13 (by decide) (choices 1) [32,64] route_5
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,9,544] (choices 1) [32,64] route_5).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_6
  · exact upper_7

def route_1 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [258,20,9] 13 := by
  apply routed_branch D R [258,20,9] 13 (by decide) (choices 2) [48,96,528,544] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,20,9] (choices 2) [48,96,528,544] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5

def bound_20 : Bound 10 := { allowed := (rows 240 224 224 144 0 0 0 0 0 0), upper := (rows 259 22 21 104 760 744 744 744 1000 744), lower := (rows 259 22 21 104 16 32 64 128 256 512), losses := [] }

theorem upper_20 : Upper D R [258,20,17,96] 13 :=
  bound_sound D R [258,20,17,96] 13 bound_20
    ((Boolean.boundCheck_true D R [258,20,17,96] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 259 22 21 552 248 232 232 232 488 744), lower := (rows 259 22 21 552 16 32 64 128 256 512), losses := [] }

theorem upper_21 : Upper D R [258,20,17,544] 13 :=
  bound_sound D R [258,20,17,544] 13 bound_21
    ((Boolean.boundCheck_true D R [258,20,17,544] 13 bound_21).mp (by decide +kernel))

def route_19 : Route 10 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_19 : Upper D R [258,20,17] 13 := by
  apply routed_branch D R [258,20,17] 13 (by decide) (choices 2) [96,544] route_19
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,20,17] (choices 2) [96,544] route_19).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_20
  · exact upper_21

def bound_23 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 259 22 28 41 752 736 736 736 992 736), lower := (rows 259 22 28 41 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [258,20,24,33] 13 :=
  bound_sound D R [258,20,24,33] 13 bound_23
    ((Boolean.boundCheck_true D R [258,20,24,33] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 240 224 224 144 0 0 0 0 0 0), upper := (rows 259 22 28 104 753 737 737 737 993 737), lower := (rows 259 22 28 104 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [258,20,24,96] 13 :=
  bound_sound D R [258,20,24,96] 13 bound_24
    ((Boolean.boundCheck_true D R [258,20,24,96] 13 bound_24).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 259 22 28 521 240 224 224 224 480 736), lower := (rows 259 22 28 521 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 4 11 0 1023 1023 1023 1023 1023), good := (rows 1003 1007 1004 1001 992 992 992 992 992 992) }] }

theorem upper_25 : Upper D R [258,20,24,513] 13 :=
  bound_sound D R [258,20,24,513] 13 bound_25
    ((Boolean.boundCheck_true D R [258,20,24,513] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 259 22 28 552 241 225 225 225 481 737), lower := (rows 259 22 28 552 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [258,20,24,544] 13 :=
  bound_sound D R [258,20,24,544] 13 bound_26
    ((Boolean.boundCheck_true D R [258,20,24,544] 13 bound_26).mp (by decide +kernel))

def route_22 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_22 : Upper D R [258,20,24] 13 := by
  apply routed_branch D R [258,20,24] 13 (by decide) (choices 2) [33,96,513,544] route_22
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,20,24] (choices 2) [33,96,513,544] route_22).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_23
  · exact upper_24
  · exact upper_25
  · exact upper_26

def bound_28 : Bound 10 := { allowed := (rows 240 224 208 192 0 0 0 0 0 0), upper := (rows 259 22 37 56 728 744 712 712 968 712), lower := (rows 259 22 37 56 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [258,20,33,48] 13 :=
  bound_sound D R [258,20,33,48] 13 bound_28
    ((Boolean.boundCheck_true D R [258,20,33,48] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 240 224 208 160 0 0 0 0 0 0), upper := (rows 259 22 37 88 760 744 744 744 1000 744), lower := (rows 259 22 37 88 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [258,20,33,80] 13 :=
  bound_sound D R [258,20,33,80] 13 bound_29
    ((Boolean.boundCheck_true D R [258,20,33,80] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 240 224 208 144 0 0 0 0 0 0), upper := (rows 259 22 37 104 728 760 728 728 984 728), lower := (rows 259 22 37 104 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [258,20,33,96] 13 :=
  bound_sound D R [258,20,33,96] 13 bound_30
    ((Boolean.boundCheck_true D R [258,20,33,96] 13 bound_30).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 240 224 208 48 0 0 0 0 0 0), upper := (rows 259 22 37 200 760 760 760 760 1016 760), lower := (rows 259 22 37 200 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [258,20,33,192] 13 :=
  bound_sound D R [258,20,33,192] 13 bound_31
    ((Boolean.boundCheck_true D R [258,20,33,192] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 259 22 37 536 248 232 232 232 488 744), lower := (rows 259 22 37 536 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [258,20,33,528] 13 :=
  bound_sound D R [258,20,33,528] 13 bound_32
    ((Boolean.boundCheck_true D R [258,20,33,528] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 259 22 37 552 216 248 216 216 472 728), lower := (rows 259 22 37 552 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [258,20,33,544] 13 :=
  bound_sound D R [258,20,33,544] 13 bound_33
    ((Boolean.boundCheck_true D R [258,20,33,544] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 259 22 37 584 248 248 248 248 504 760), lower := (rows 259 22 37 584 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [258,20,33,576] 13 :=
  bound_sound D R [258,20,33,576] 13 bound_34
    ((Boolean.boundCheck_true D R [258,20,33,576] 13 bound_34).mp (by decide +kernel))

def route_27 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_27 : Upper D R [258,20,33] 13 := by
  apply routed_branch D R [258,20,33] 13 (by decide) (choices 2) [48,80,96,192,528,544,576] route_27
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,20,33] (choices 2) [48,80,96,192,528,544,576] route_27).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_28
  · exact upper_29
  · exact upper_30
  · exact upper_31
  · exact upper_32
  · exact upper_33
  · exact upper_34

def bound_36 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 259 22 44 25 752 736 736 736 992 736), lower := (rows 259 22 44 25 16 32 64 128 256 512), losses := [] }

theorem upper_36 : Upper D R [258,20,40,17] 13 :=
  bound_sound D R [258,20,40,17] 13 bound_36
    ((Boolean.boundCheck_true D R [258,20,40,17] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 259 22 44 41 720 752 720 720 976 720), lower := (rows 259 22 44 41 16 32 64 128 256 512), losses := [] }

theorem upper_37 : Upper D R [258,20,40,33] 13 :=
  bound_sound D R [258,20,40,33] 13 bound_37
    ((Boolean.boundCheck_true D R [258,20,40,33] 13 bound_37).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 240 224 208 192 0 0 0 0 0 0), upper := (rows 259 22 44 56 721 737 705 705 961 705), lower := (rows 259 22 44 56 16 32 64 128 256 512), losses := [] }

theorem upper_38 : Upper D R [258,20,40,48] 13 :=
  bound_sound D R [258,20,40,48] 13 bound_38
    ((Boolean.boundCheck_true D R [258,20,40,48] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 259 22 44 73 752 752 752 752 1008 752), lower := (rows 259 22 44 73 16 32 64 128 256 512), losses := [] }

theorem upper_39 : Upper D R [258,20,40,65] 13 :=
  bound_sound D R [258,20,40,65] 13 bound_39
    ((Boolean.boundCheck_true D R [258,20,40,65] 13 bound_39).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 240 224 208 160 0 0 0 0 0 0), upper := (rows 259 22 44 88 753 737 737 737 993 737), lower := (rows 259 22 44 88 16 32 64 128 256 512), losses := [] }

theorem upper_40 : Upper D R [258,20,40,80] 13 :=
  bound_sound D R [258,20,40,80] 13 bound_40
    ((Boolean.boundCheck_true D R [258,20,40,80] 13 bound_40).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 240 224 208 144 0 0 0 0 0 0), upper := (rows 259 22 44 104 721 753 721 721 977 721), lower := (rows 259 22 44 104 16 32 64 128 256 512), losses := [] }

theorem upper_41 : Upper D R [258,20,40,96] 13 :=
  bound_sound D R [258,20,40,96] 13 bound_41
    ((Boolean.boundCheck_true D R [258,20,40,96] 13 bound_41).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 240 224 208 48 0 0 0 0 0 0), upper := (rows 259 22 44 200 753 753 753 753 1009 753), lower := (rows 259 22 44 200 16 32 64 128 256 512), losses := [] }

theorem upper_42 : Upper D R [258,20,40,192] 13 :=
  bound_sound D R [258,20,40,192] 13 bound_42
    ((Boolean.boundCheck_true D R [258,20,40,192] 13 bound_42).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 208 224 208 208 0 0 0 0 0 0), upper := (rows 259 22 44 521 48 240 208 208 464 720), lower := (rows 259 22 44 521 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 11 16 0 82 146 274 530), good := (rows 971 991 12 521 976 0 64 128 256 512) }] }

theorem upper_44 : Upper D R [258,20,40,513,32] 13 :=
  bound_sound D R [258,20,40,513,32] 13 bound_44
    ((Boolean.boundCheck_true D R [258,20,40,513,32] 13 bound_44).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 224 224 208 224 0 0 0 0 0 0), upper := (rows 259 22 44 521 80 48 224 224 480 736), lower := (rows 259 22 44 521 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 4 10 0 32 100 164 292 548), good := (rows 267 975 1004 521 64 992 64 128 256 512) }] }

theorem upper_46 : Upper D R [258,20,40,513,64,16] 13 :=
  bound_sound D R [258,20,40,513,64,16] 13 bound_46
    ((Boolean.boundCheck_true D R [258,20,40,513,64,16] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 240 192 208 240 0 0 0 0 0 0), upper := (rows 259 22 44 521 80 96 240 176 432 688), lower := (rows 259 22 44 521 80 96 64 128 256 512), losses := [{ target := 5, region := (rows 1 6 4 8 112 0 64 128 256 512), good := (rows 259 22 30 521 80 80 80 128 256 512) }] }

theorem upper_47 : Upper D R [258,20,40,513,64,64] 13 :=
  bound_sound D R [258,20,40,513,64,64] 13 bound_47
    ((Boolean.boundCheck_true D R [258,20,40,513,64,64] 13 bound_47).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 259 22 44 521 80 160 80 224 480 736), lower := (rows 259 22 44 521 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 10 0 242 64 208 336 592), good := (rows 303 943 44 525 992 160 992 160 256 512) }] }

theorem upper_49 : Upper D R [258,20,40,513,64,128,16] 13 :=
  bound_sound D R [258,20,40,513,64,128,16] 13 bound_49
    ((Boolean.boundCheck_true D R [258,20,40,513,64,128,16] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 208 224 208 208 0 0 0 0 0 0), upper := (rows 259 22 44 521 80 160 96 208 464 720), lower := (rows 259 22 44 521 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 10 80 0 64 208 336 592), good := (rows 267 927 12 521 976 128 976 128 256 512) }] }

theorem upper_50 : Upper D R [258,20,40,513,64,128,32] 13 :=
  bound_sound D R [258,20,40,513,64,128,32] 13 bound_50
    ((Boolean.boundCheck_true D R [258,20,40,513,64,128,32] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 240 192 208 240 0 0 0 0 0 0), upper := (rows 259 22 44 521 80 160 192 240 368 624), lower := (rows 259 22 44 521 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 1 6 4 8 244 0 224 128 256 512), good := (rows 259 22 94 521 80 208 208 208 256 512) }] }

theorem upper_51 : Upper D R [258,20,40,513,64,128,128] 13 :=
  bound_sound D R [258,20,40,513,64,128,128] 13 bound_51
    ((Boolean.boundCheck_true D R [258,20,40,513,64,128,128] 13 bound_51).mp (by decide +kernel))

def route_48 : Route 10 := (fun mask => (mask,id))

theorem upper_48 : Upper D R [258,20,40,513,64,128] 13 := by
  apply routed_branch D R [258,20,40,513,64,128] 13 (by decide) (choices 1) [16,32,128] route_48
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,40,513,64,128] (choices 1) [16,32,128] route_48).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_49
  · exact upper_50
  · exact upper_51

def route_45 : Route 10 := (fun mask => (mask,id))

theorem upper_45 : Upper D R [258,20,40,513,64] 13 := by
  apply routed_branch D R [258,20,40,513,64] 13 (by decide) (choices 1) [16,64,128] route_45
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,40,513,64] (choices 1) [16,64,128] route_45).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_46
  · exact upper_47
  · exact upper_48

def route_43 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_43 : Upper D R [258,20,40,513] 13 := by
  apply routed_branch D R [258,20,40,513] 13 (by decide) (choices 1) [32,64] route_43
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,40,513] (choices 1) [32,64] route_43).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_44
  · exact upper_45

def bound_52 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 259 22 44 536 241 225 225 225 481 737), lower := (rows 259 22 44 536 16 32 64 128 256 512), losses := [] }

theorem upper_52 : Upper D R [258,20,40,528] 13 :=
  bound_sound D R [258,20,40,528] 13 bound_52
    ((Boolean.boundCheck_true D R [258,20,40,528] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 259 22 44 552 209 241 209 209 465 721), lower := (rows 259 22 44 552 16 32 64 128 256 512), losses := [] }

theorem upper_53 : Upper D R [258,20,40,544] 13 :=
  bound_sound D R [258,20,40,544] 13 bound_53
    ((Boolean.boundCheck_true D R [258,20,40,544] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 259 22 44 584 241 241 241 241 497 753), lower := (rows 259 22 44 584 16 32 64 128 256 512), losses := [] }

theorem upper_54 : Upper D R [258,20,40,576] 13 :=
  bound_sound D R [258,20,40,576] 13 bound_54
    ((Boolean.boundCheck_true D R [258,20,40,576] 13 bound_54).mp (by decide +kernel))

def route_35 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_35 : Upper D R [258,20,40] 13 := by
  apply routed_branch D R [258,20,40] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,513,528,544,576] route_35
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,20,40] (choices 2) [17,33,48,65,80,96,192,513,528,544,576] route_35).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_36
  · exact upper_37
  · exact upper_38
  · exact upper_39
  · exact upper_40
  · exact upper_41
  · exact upper_42
  · exact upper_43
  · exact upper_52
  · exact upper_53
  · exact upper_54

def bound_55 : Bound 10 := { allowed := (rows 240 224 192 240 0 0 0 0 0 0), upper := (rows 259 22 52 745 761 745 745 745 1001 745), lower := (rows 259 22 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [258,20,48] 13 :=
  bound_sound D R [258,20,48] 13 bound_55
    ((Boolean.boundCheck_true D R [258,20,48] 13 bound_55).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 240 224 144 240 0 0 0 0 0 0), upper := (rows 259 22 100 761 761 761 761 761 1017 761), lower := (rows 259 22 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_56 : Upper D R [258,20,96] 13 :=
  bound_sound D R [258,20,96] 13 bound_56
    ((Boolean.boundCheck_true D R [258,20,96] 13 bound_56).mp (by decide +kernel))

def bound_58 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 259 22 517 56 248 232 232 232 488 744), lower := (rows 259 22 517 56 16 32 64 128 256 512), losses := [] }

theorem upper_58 : Upper D R [258,20,513,48] 13 :=
  bound_sound D R [258,20,513,48] 13 bound_58
    ((Boolean.boundCheck_true D R [258,20,513,48] 13 bound_58).mp (by decide +kernel))

def bound_59 : Bound 10 := { allowed := (rows 240 224 240 144 0 0 0 0 0 0), upper := (rows 259 22 517 104 248 248 248 248 504 760), lower := (rows 259 22 517 104 16 32 64 128 256 512), losses := [] }

theorem upper_59 : Upper D R [258,20,513,96] 13 :=
  bound_sound D R [258,20,513,96] 13 bound_59
    ((Boolean.boundCheck_true D R [258,20,513,96] 13 bound_59).mp (by decide +kernel))

def route_57 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_57 : Upper D R [258,20,513] 13 := by
  apply routed_branch D R [258,20,513] 13 (by decide) (choices 2) [48,96] route_57
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,20,513] (choices 2) [48,96] route_57).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_58
  · exact upper_59

def bound_61 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 259 22 524 25 240 224 224 224 480 736), lower := (rows 259 22 524 25 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 12 8 0 1023 1023 1023 1023 1023), good := (rows 995 999 1004 1005 992 992 992 992 992 992) }] }

theorem upper_61 : Upper D R [258,20,520,17] 13 :=
  bound_sound D R [258,20,520,17] 13 bound_61
    ((Boolean.boundCheck_true D R [258,20,520,17] 13 bound_61).mp (by decide +kernel))

def bound_63 : Bound 10 := { allowed := (rows 208 224 240 208 0 0 0 0 0 0), upper := (rows 259 22 524 41 48 240 208 208 464 720), lower := (rows 259 22 524 41 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 16 0 82 146 274 530), good := (rows 963 983 524 9 976 0 64 128 256 512) }] }

theorem upper_63 : Upper D R [258,20,520,33,32] 13 :=
  bound_sound D R [258,20,520,33,32] 13 bound_63
    ((Boolean.boundCheck_true D R [258,20,520,33,32] 13 bound_63).mp (by decide +kernel))

def bound_65 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 259 22 524 41 80 48 224 224 480 736), lower := (rows 259 22 524 41 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 104 168 296 552), good := (rows 259 6 972 1005 64 992 64 128 256 512) }] }

theorem upper_65 : Upper D R [258,20,520,33,64,16] 13 :=
  bound_sound D R [258,20,520,33,64,16] 13 bound_65
    ((Boolean.boundCheck_true D R [258,20,520,33,64,16] 13 bound_65).mp (by decide +kernel))

def bound_67 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 259 22 524 41 80 96 80 160 416 672), lower := (rows 259 22 524 41 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 15 10 0 112 64 250 378 634), good := (rows 911 943 908 941 992 992 992 128 256 512) }] }

theorem upper_67 : Upper D R [258,20,520,33,64,64,16] 13 :=
  bound_sound D R [258,20,520,33,64,64,16] 13 bound_67
    ((Boolean.boundCheck_true D R [258,20,520,33,64,64,16] 13 bound_67).mp (by decide +kernel))

def bound_68 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 259 22 524 41 80 96 96 144 400 656), lower := (rows 259 22 524 41 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 128 256 512), good := (rows 363 102 620 105 96 96 96 224 352 608) }] }

theorem upper_68 : Upper D R [258,20,520,33,64,64,32] 13 :=
  bound_sound D R [258,20,520,33,64,64,32] 13 bound_68
    ((Boolean.boundCheck_true D R [258,20,520,33,64,64,32] 13 bound_68).mp (by decide +kernel))

def bound_70 : Bound 10 := { allowed := (rows 240 192 240 208 0 0 0 0 0 0), upper := (rows 259 22 524 41 80 96 192 144 416 672), lower := (rows 259 22 524 41 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 1 6 4 8 1023 0 1023 1023 256 512), good := (rows 467 214 734 217 208 208 208 208 464 720) }] }

theorem upper_70 : Upper D R [258,20,520,33,64,64,128,16] 13 :=
  bound_sound D R [258,20,520,33,64,64,128,16] 13 bound_70
    ((Boolean.boundCheck_true D R [258,20,520,33,64,64,128,16] 13 bound_70).mp (by decide +kernel))

def bound_71 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 259 22 524 41 80 96 192 160 400 656), lower := (rows 259 22 524 41 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 1023 256 512), good := (rows 491 230 748 233 224 224 224 224 480 736) }] }

theorem upper_71 : Upper D R [258,20,520,33,64,64,128,32] 13 :=
  bound_sound D R [258,20,520,33,64,64,128,32] 13 bound_71
    ((Boolean.boundCheck_true D R [258,20,520,33,64,64,128,32] 13 bound_71).mp (by decide +kernel))

def route_69 : Route 10 := (fun mask => (mask,id))

theorem upper_69 : Upper D R [258,20,520,33,64,64,128] 13 := by
  apply routed_branch D R [258,20,520,33,64,64,128] 13 (by decide) (choices 1) [16,32] route_69
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,520,33,64,64,128] (choices 1) [16,32] route_69).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_70
  · exact upper_71

def route_66 : Route 10 := (fun mask => (mask,id))

theorem upper_66 : Upper D R [258,20,520,33,64,64] 13 := by
  apply routed_branch D R [258,20,520,33,64,64] 13 (by decide) (choices 1) [16,32,128] route_66
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,520,33,64,64] (choices 1) [16,32,128] route_66).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_67
  · exact upper_68
  · exact upper_69

def bound_73 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 259 22 524 41 80 160 80 224 480 736), lower := (rows 259 22 524 41 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 6 11 0 242 64 208 336 592), good := (rows 303 943 524 41 992 160 992 160 256 512) }] }

theorem upper_73 : Upper D R [258,20,520,33,64,128,16] 13 :=
  bound_sound D R [258,20,520,33,64,128,16] 13 bound_73
    ((Boolean.boundCheck_true D R [258,20,520,33,64,128,16] 13 bound_73).mp (by decide +kernel))

def bound_74 : Bound 10 := { allowed := (rows 208 224 240 208 0 0 0 0 0 0), upper := (rows 259 22 524 41 80 160 96 208 464 720), lower := (rows 259 22 524 41 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 80 0 64 208 336 592), good := (rows 259 919 524 9 976 128 976 128 256 512) }] }

theorem upper_74 : Upper D R [258,20,520,33,64,128,32] 13 :=
  bound_sound D R [258,20,520,33,64,128,32] 13 bound_74
    ((Boolean.boundCheck_true D R [258,20,520,33,64,128,32] 13 bound_74).mp (by decide +kernel))

def bound_75 : Bound 10 := { allowed := (rows 240 192 240 208 0 0 0 0 0 0), upper := (rows 259 22 524 41 80 160 192 240 368 624), lower := (rows 259 22 524 41 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 1 6 4 8 248 0 224 128 256 512), good := (rows 259 22 542 89 80 208 208 208 256 512) }] }

theorem upper_75 : Upper D R [258,20,520,33,64,128,128] 13 :=
  bound_sound D R [258,20,520,33,64,128,128] 13 bound_75
    ((Boolean.boundCheck_true D R [258,20,520,33,64,128,128] 13 bound_75).mp (by decide +kernel))

def route_72 : Route 10 := (fun mask => (mask,id))

theorem upper_72 : Upper D R [258,20,520,33,64,128] 13 := by
  apply routed_branch D R [258,20,520,33,64,128] 13 (by decide) (choices 1) [16,32,128] route_72
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,520,33,64,128] (choices 1) [16,32,128] route_72).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_73
  · exact upper_74
  · exact upper_75

def route_64 : Route 10 := (fun mask => (mask,id))

theorem upper_64 : Upper D R [258,20,520,33,64] 13 := by
  apply routed_branch D R [258,20,520,33,64] 13 (by decide) (choices 1) [16,64,128] route_64
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,520,33,64] (choices 1) [16,64,128] route_64).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_65
  · exact upper_66
  · exact upper_72

def route_62 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_62 : Upper D R [258,20,520,33] 13 := by
  apply routed_branch D R [258,20,520,33] 13 (by decide) (choices 1) [32,64] route_62
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,20,520,33] (choices 1) [32,64] route_62).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_63
  · exact upper_64

def bound_76 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 259 22 524 56 241 225 225 225 481 737), lower := (rows 259 22 524 56 16 32 64 128 256 512), losses := [] }

theorem upper_76 : Upper D R [258,20,520,48] 13 :=
  bound_sound D R [258,20,520,48] 13 bound_76
    ((Boolean.boundCheck_true D R [258,20,520,48] 13 bound_76).mp (by decide +kernel))

def bound_77 : Bound 10 := { allowed := (rows 240 224 240 144 0 0 0 0 0 0), upper := (rows 259 22 524 104 241 241 241 241 497 753), lower := (rows 259 22 524 104 16 32 64 128 256 512), losses := [] }

theorem upper_77 : Upper D R [258,20,520,96] 13 :=
  bound_sound D R [258,20,520,96] 13 bound_77
    ((Boolean.boundCheck_true D R [258,20,520,96] 13 bound_77).mp (by decide +kernel))

def route_60 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_60 : Upper D R [258,20,520] 13 := by
  apply routed_branch D R [258,20,520] 13 (by decide) (choices 2) [17,33,48,96] route_60
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,20,520] (choices 2) [17,33,48,96] route_60).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_61
  · exact upper_62
  · exact upper_76
  · exact upper_77

def bound_79 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 259 22 532 41 248 232 232 232 488 744), lower := (rows 259 22 532 41 16 32 64 128 256 512), losses := [] }

theorem upper_79 : Upper D R [258,20,528,33] 13 :=
  bound_sound D R [258,20,528,33] 13 bound_79
    ((Boolean.boundCheck_true D R [258,20,528,33] 13 bound_79).mp (by decide +kernel))

def bound_80 : Bound 10 := { allowed := (rows 240 224 224 144 0 0 0 0 0 0), upper := (rows 259 22 532 104 249 233 233 233 489 745), lower := (rows 259 22 532 104 16 32 64 128 256 512), losses := [] }

theorem upper_80 : Upper D R [258,20,528,96] 13 :=
  bound_sound D R [258,20,528,96] 13 bound_80
    ((Boolean.boundCheck_true D R [258,20,528,96] 13 bound_80).mp (by decide +kernel))

def route_78 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_78 : Upper D R [258,20,528] 13 := by
  apply routed_branch D R [258,20,528] 13 (by decide) (choices 2) [33,96] route_78
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,20,528] (choices 2) [33,96] route_78).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_79
  · exact upper_80

def bound_82 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 259 22 548 25 248 232 232 232 488 744), lower := (rows 259 22 548 25 16 32 64 128 256 512), losses := [] }

theorem upper_82 : Upper D R [258,20,544,17] 13 :=
  bound_sound D R [258,20,544,17] 13 bound_82
    ((Boolean.boundCheck_true D R [258,20,544,17] 13 bound_82).mp (by decide +kernel))

def bound_83 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 259 22 548 41 216 248 216 216 472 728), lower := (rows 259 22 548 41 16 32 64 128 256 512), losses := [] }

theorem upper_83 : Upper D R [258,20,544,33] 13 :=
  bound_sound D R [258,20,544,33] 13 bound_83
    ((Boolean.boundCheck_true D R [258,20,544,33] 13 bound_83).mp (by decide +kernel))

def bound_84 : Bound 10 := { allowed := (rows 240 224 208 192 0 0 0 0 0 0), upper := (rows 259 22 548 56 217 233 201 201 457 713), lower := (rows 259 22 548 56 16 32 64 128 256 512), losses := [] }

theorem upper_84 : Upper D R [258,20,544,48] 13 :=
  bound_sound D R [258,20,544,48] 13 bound_84
    ((Boolean.boundCheck_true D R [258,20,544,48] 13 bound_84).mp (by decide +kernel))

def bound_85 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 259 22 548 73 248 248 248 248 504 760), lower := (rows 259 22 548 73 16 32 64 128 256 512), losses := [] }

theorem upper_85 : Upper D R [258,20,544,65] 13 :=
  bound_sound D R [258,20,544,65] 13 bound_85
    ((Boolean.boundCheck_true D R [258,20,544,65] 13 bound_85).mp (by decide +kernel))

def bound_86 : Bound 10 := { allowed := (rows 240 224 208 160 0 0 0 0 0 0), upper := (rows 259 22 548 88 249 233 233 233 489 745), lower := (rows 259 22 548 88 16 32 64 128 256 512), losses := [] }

theorem upper_86 : Upper D R [258,20,544,80] 13 :=
  bound_sound D R [258,20,544,80] 13 bound_86
    ((Boolean.boundCheck_true D R [258,20,544,80] 13 bound_86).mp (by decide +kernel))

def bound_87 : Bound 10 := { allowed := (rows 240 224 208 144 0 0 0 0 0 0), upper := (rows 259 22 548 104 217 249 217 217 473 729), lower := (rows 259 22 548 104 16 32 64 128 256 512), losses := [] }

theorem upper_87 : Upper D R [258,20,544,96] 13 :=
  bound_sound D R [258,20,544,96] 13 bound_87
    ((Boolean.boundCheck_true D R [258,20,544,96] 13 bound_87).mp (by decide +kernel))

def bound_88 : Bound 10 := { allowed := (rows 240 224 208 48 0 0 0 0 0 0), upper := (rows 259 22 548 200 249 249 249 249 505 761), lower := (rows 259 22 548 200 16 32 64 128 256 512), losses := [] }

theorem upper_88 : Upper D R [258,20,544,192] 13 :=
  bound_sound D R [258,20,544,192] 13 bound_88
    ((Boolean.boundCheck_true D R [258,20,544,192] 13 bound_88).mp (by decide +kernel))

def route_81 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_81 : Upper D R [258,20,544] 13 := by
  apply routed_branch D R [258,20,544] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] route_81
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,20,544] (choices 2) [17,33,48,65,80,96,192] route_81).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_82
  · exact upper_83
  · exact upper_84
  · exact upper_85
  · exact upper_86
  · exact upper_87
  · exact upper_88

def route_0 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [258,20] 13 := by
  apply routed_branch D R [258,20] 13 (by decide) (choices 2) [9,17,24,33,40,48,96,513,520,528,544] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,20] (choices 2) [9,17,24,33,40,48,96,513,520,528,544] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_19
  · exact upper_22
  · exact upper_27
  · exact upper_35
  · exact upper_55
  · exact upper_56
  · exact upper_57
  · exact upper_60
  · exact upper_78
  · exact upper_81

theorem upper : Upper D R [258,20] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case38
