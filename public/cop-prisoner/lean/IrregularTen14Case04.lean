import IrregularTen14Base

namespace Delivery.IrregularTen14.Case04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 259 28 56 752 736 736 736 992 736), lower := (rows 7 259 28 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [6,257,24,48] 13 :=
  bound_sound D R [6,257,24,48] 13 bound_2
    ((Boolean.boundCheck_true D R [6,257,24,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 240 240 224 144 0 0 0 0 0 0), upper := (rows 7 259 28 104 752 752 752 752 1008 752), lower := (rows 7 259 28 104 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [6,257,24,96] 13 :=
  bound_sound D R [6,257,24,96] 13 bound_3
    ((Boolean.boundCheck_true D R [6,257,24,96] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 7 259 28 536 240 224 224 224 480 736), lower := (rows 7 259 28 536 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 5 7 4 8 0 1023 1023 1023 1023 1023), good := (rows 999 995 1007 1000 992 992 992 992 992 992) }] }

theorem upper_4 : Upper D R [6,257,24,528] 13 :=
  bound_sound D R [6,257,24,528] 13 bound_4
    ((Boolean.boundCheck_true D R [6,257,24,528] 13 bound_4).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 208 208 224 208 0 0 0 0 0 0), upper := (rows 7 259 28 552 48 240 208 208 464 720), lower := (rows 7 259 28 552 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 5 7 4 8 16 0 84 148 276 532), good := (rows 967 259 991 520 976 0 64 128 256 512) }] }

theorem upper_6 : Upper D R [6,257,24,544,32] 13 :=
  bound_sound D R [6,257,24,544,32] 13 bound_6
    ((Boolean.boundCheck_true D R [6,257,24,544,32] 13 bound_6).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 259 28 552 80 48 224 224 480 736), lower := (rows 7 259 28 552 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 5 6 4 40 0 32 104 168 296 552), good := (rows 7 259 975 1000 64 1000 64 128 256 512) }] }

theorem upper_8 : Upper D R [6,257,24,544,64,16] 13 :=
  bound_sound D R [6,257,24,544,64,16] 13 bound_8
    ((Boolean.boundCheck_true D R [6,257,24,544,64,16] 13 bound_8).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 240 240 192 208 0 0 0 0 0 0), upper := (rows 7 259 28 552 80 96 240 176 432 688), lower := (rows 7 259 28 552 80 96 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 12 8 112 0 64 128 256 512), good := (rows 7 259 28 540 80 80 80 128 256 512) }] }

theorem upper_9 : Upper D R [6,257,24,544,64,64] 13 :=
  bound_sound D R [6,257,24,544,64,64] 13 bound_9
    ((Boolean.boundCheck_true D R [6,257,24,544,64,64] 13 bound_9).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 259 28 552 80 160 80 224 480 736), lower := (rows 7 259 28 552 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 5 6 4 92 0 244 64 208 336 592), good := (rows 47 259 943 552 1000 160 1000 160 256 512) }] }

theorem upper_11 : Upper D R [6,257,24,544,64,128,16] 13 :=
  bound_sound D R [6,257,24,544,64,128,16] 13 bound_11
    ((Boolean.boundCheck_true D R [6,257,24,544,64,128,16] 13 bound_11).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 208 208 224 208 0 0 0 0 0 0), upper := (rows 7 259 28 552 80 160 96 208 464 720), lower := (rows 7 259 28 552 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 5 6 4 8 80 0 64 208 336 592), good := (rows 7 259 927 520 976 128 976 128 256 512) }] }

theorem upper_12 : Upper D R [6,257,24,544,64,128,32] 13 :=
  bound_sound D R [6,257,24,544,64,128,32] 13 bound_12
    ((Boolean.boundCheck_true D R [6,257,24,544,64,128,32] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 240 240 192 208 0 0 0 0 0 0), upper := (rows 7 259 28 552 80 160 192 240 368 624), lower := (rows 7 259 28 552 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 1 2 12 8 248 0 224 128 256 512), good := (rows 7 259 28 604 80 208 208 208 256 512) }] }

theorem upper_13 : Upper D R [6,257,24,544,64,128,128] 13 :=
  bound_sound D R [6,257,24,544,64,128,128] 13 bound_13
    ((Boolean.boundCheck_true D R [6,257,24,544,64,128,128] 13 bound_13).mp (by decide +kernel))

def route_10 : Route 10 := (fun mask => (mask,id))

theorem upper_10 : Upper D R [6,257,24,544,64,128] 13 := by
  apply routed_branch D R [6,257,24,544,64,128] 13 (by decide) (choices 1) [16,32,128] route_10
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,257,24,544,64,128] (choices 1) [16,32,128] route_10).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_11
  · exact upper_12
  · exact upper_13

def route_7 : Route 10 := (fun mask => (mask,id))

theorem upper_7 : Upper D R [6,257,24,544,64] 13 := by
  apply routed_branch D R [6,257,24,544,64] 13 (by decide) (choices 1) [16,64,128] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,257,24,544,64] (choices 1) [16,64,128] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_8
  · exact upper_9
  · exact upper_10

def route_5 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_5 : Upper D R [6,257,24,544] 13 := by
  apply routed_branch D R [6,257,24,544] 13 (by decide) (choices 1) [32,64] route_5
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,257,24,544] (choices 1) [32,64] route_5).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_6
  · exact upper_7

def route_1 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [6,257,24] 13 := by
  apply routed_branch D R [6,257,24] 13 (by decide) (choices 2) [48,96,528,544] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,257,24] (choices 2) [48,96,528,544] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5

def bound_15 : Bound 10 := { allowed := (rows 240 240 192 192 0 0 0 0 0 0), upper := (rows 7 259 52 56 728 744 712 712 968 712), lower := (rows 7 259 52 56 16 32 64 128 256 512), losses := [] }

theorem upper_15 : Upper D R [6,257,48,48] 13 :=
  bound_sound D R [6,257,48,48] 13 bound_15
    ((Boolean.boundCheck_true D R [6,257,48,48] 13 bound_15).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 240 240 192 160 0 0 0 0 0 0), upper := (rows 7 259 52 88 760 744 744 744 1000 744), lower := (rows 7 259 52 88 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [6,257,48,80] 13 :=
  bound_sound D R [6,257,48,80] 13 bound_16
    ((Boolean.boundCheck_true D R [6,257,48,80] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 240 240 192 48 0 0 0 0 0 0), upper := (rows 7 259 52 200 760 760 760 760 1016 760), lower := (rows 7 259 52 200 16 32 64 128 256 512), losses := [] }

theorem upper_17 : Upper D R [6,257,48,192] 13 :=
  bound_sound D R [6,257,48,192] 13 bound_17
    ((Boolean.boundCheck_true D R [6,257,48,192] 13 bound_17).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 240 240 192 224 0 0 0 0 0 0), upper := (rows 7 259 52 536 248 232 232 232 488 744), lower := (rows 7 259 52 536 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [6,257,48,528] 13 :=
  bound_sound D R [6,257,48,528] 13 bound_18
    ((Boolean.boundCheck_true D R [6,257,48,528] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 240 240 192 176 0 0 0 0 0 0), upper := (rows 7 259 52 584 248 248 248 248 504 760), lower := (rows 7 259 52 584 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [6,257,48,576] 13 :=
  bound_sound D R [6,257,48,576] 13 bound_19
    ((Boolean.boundCheck_true D R [6,257,48,576] 13 bound_19).mp (by decide +kernel))

def route_14 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_14 : Upper D R [6,257,48] 13 := by
  apply routed_branch D R [6,257,48] 13 (by decide) (choices 2) [48,80,192,528,576] route_14
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,257,48] (choices 2) [48,80,192,528,576] route_14).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_15
  · exact upper_16
  · exact upper_17
  · exact upper_18
  · exact upper_19

def bound_22 : Bound 10 := { allowed := (rows 208 208 208 192 0 0 0 0 0 0), upper := (rows 7 259 524 56 48 240 208 208 464 720), lower := (rows 7 259 524 56 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 13 14 12 8 16 0 88 152 280 536), good := (rows 7 259 975 991 976 0 64 128 256 512) }] }

theorem upper_22 : Upper D R [6,257,520,48,32] 13 :=
  bound_sound D R [6,257,520,48,32] 13 bound_22
    ((Boolean.boundCheck_true D R [6,257,520,48,32] 13 bound_22).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 259 524 56 80 48 224 224 480 736), lower := (rows 7 259 524 56 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 13 14 12 8 0 32 104 168 296 552), good := (rows 7 259 975 1007 64 992 64 128 256 512) }] }

theorem upper_24 : Upper D R [6,257,520,48,64,16] 13 :=
  bound_sound D R [6,257,520,48,64,16] 13 bound_24
    ((Boolean.boundCheck_true D R [6,257,520,48,64,16] 13 bound_24).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 176 176 176 192 0 0 0 0 0 0), upper := (rows 7 259 524 56 80 96 240 176 432 688), lower := (rows 7 259 524 56 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 13 14 12 8 16 32 0 136 264 520), good := (rows 7 259 911 959 16 32 0 128 256 512) }] }

theorem upper_25 : Upper D R [6,257,520,48,64,64] 13 :=
  bound_sound D R [6,257,520,48,64,64] 13 bound_25
    ((Boolean.boundCheck_true D R [6,257,520,48,64,64] 13 bound_25).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 259 524 56 80 160 80 224 480 736), lower := (rows 7 259 524 56 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 13 10 12 8 0 248 64 208 336 592), good := (rows 7 259 559 943 992 160 992 160 256 512) }] }

theorem upper_27 : Upper D R [6,257,520,48,64,128,16] 13 :=
  bound_sound D R [6,257,520,48,64,128,16] 13 bound_27
    ((Boolean.boundCheck_true D R [6,257,520,48,64,128,16] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 208 208 208 192 0 0 0 0 0 0), upper := (rows 7 259 524 56 80 160 96 208 464 720), lower := (rows 7 259 524 56 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 13 10 12 8 80 0 64 208 336 592), good := (rows 7 259 527 927 976 128 976 128 256 512) }] }

theorem upper_28 : Upper D R [6,257,520,48,64,128,32] 13 :=
  bound_sound D R [6,257,520,48,64,128,32] 13 bound_28
    ((Boolean.boundCheck_true D R [6,257,520,48,64,128,32] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 240 240 240 128 0 0 0 0 0 0), upper := (rows 7 259 524 56 80 160 192 240 368 624), lower := (rows 7 259 524 56 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 1 2 4 24 16 224 0 128 256 512), good := (rows 7 259 524 56 56 160 160 160 256 512) }] }

theorem upper_29 : Upper D R [6,257,520,48,64,128,128] 13 :=
  bound_sound D R [6,257,520,48,64,128,128] 13 bound_29
    ((Boolean.boundCheck_true D R [6,257,520,48,64,128,128] 13 bound_29).mp (by decide +kernel))

def route_26 : Route 10 := (fun mask => (mask,id))

theorem upper_26 : Upper D R [6,257,520,48,64,128] 13 := by
  apply routed_branch D R [6,257,520,48,64,128] 13 (by decide) (choices 1) [16,32,128] route_26
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,257,520,48,64,128] (choices 1) [16,32,128] route_26).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_27
  · exact upper_28
  · exact upper_29

def route_23 : Route 10 := (fun mask => (mask,id))

theorem upper_23 : Upper D R [6,257,520,48,64] 13 := by
  apply routed_branch D R [6,257,520,48,64] 13 (by decide) (choices 1) [16,64,128] route_23
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,257,520,48,64] (choices 1) [16,64,128] route_23).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_24
  · exact upper_25
  · exact upper_26

def route_21 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_21 : Upper D R [6,257,520,48] 13 := by
  apply routed_branch D R [6,257,520,48] 13 (by decide) (choices 1) [32,64] route_21
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,257,520,48] (choices 1) [32,64] route_21).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_22
  · exact upper_23

def route_20 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_20 : Upper D R [6,257,520] 13 := by
  apply routed_branch D R [6,257,520] 13 (by decide) (choices 2) [48] route_20
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,257,520] (choices 2) [48] route_20).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_21

def bound_31 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 259 532 56 248 232 232 232 488 744), lower := (rows 7 259 532 56 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [6,257,528,48] 13 :=
  bound_sound D R [6,257,528,48] 13 bound_31
    ((Boolean.boundCheck_true D R [6,257,528,48] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 240 240 224 144 0 0 0 0 0 0), upper := (rows 7 259 532 104 248 248 248 248 504 760), lower := (rows 7 259 532 104 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [6,257,528,96] 13 :=
  bound_sound D R [6,257,528,96] 13 bound_32
    ((Boolean.boundCheck_true D R [6,257,528,96] 13 bound_32).mp (by decide +kernel))

def route_30 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_30 : Upper D R [6,257,528] 13 := by
  apply routed_branch D R [6,257,528] 13 (by decide) (choices 2) [48,96] route_30
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,257,528] (choices 2) [48,96] route_30).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_31
  · exact upper_32

def route_0 : Route 10 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 136 => (24,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 576 => (528,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 640 => (528,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [6,257] 13 := by
  apply routed_branch D R [6,257] 13 (by decide) (choices 2) [24,48,520,528] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,257] (choices 2) [24,48,520,528] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_14
  · exact upper_20
  · exact upper_30

theorem upper : Upper D R [6,257] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case04
