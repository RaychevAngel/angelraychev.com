import IrregularTen14Base

namespace Delivery.IrregularTen14.Case56
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_3 : Bound 10 := { allowed := (rows 208 208 208 192 0 0 0 0 0 0), upper := (rows 769 14 7 56 48 240 208 208 464 720), lower := (rows 769 14 7 56 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 27 10 14 8 16 0 88 152 280 536), good := (rows 769 975 7 991 977 0 64 128 256 512) }] }

theorem upper_3 : Upper D R [768,12,3,48,32] 13 :=
  bound_sound D R [768,12,3,48,32] 13 bound_3
    ((Boolean.boundCheck_true D R [768,12,3,48,32] 13 bound_3).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 769 14 7 56 80 48 224 224 480 736), lower := (rows 769 14 7 56 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 43 10 14 8 0 32 104 168 296 552), good := (rows 769 975 7 1007 64 993 64 128 256 512) }] }

theorem upper_5 : Upper D R [768,12,3,48,64,16] 13 :=
  bound_sound D R [768,12,3,48,64,16] 13 bound_5
    ((Boolean.boundCheck_true D R [768,12,3,48,64,16] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 176 176 176 192 0 0 0 0 0 0), upper := (rows 769 14 7 56 80 96 240 176 432 688), lower := (rows 769 14 7 56 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 11 10 14 8 16 32 0 136 264 520), good := (rows 769 911 7 959 16 32 0 128 256 512) }] }

theorem upper_6 : Upper D R [768,12,3,48,64,64] 13 :=
  bound_sound D R [768,12,3,48,64,64] 13 bound_6
    ((Boolean.boundCheck_true D R [768,12,3,48,64,64] 13 bound_6).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 769 14 7 56 80 160 80 224 480 736), lower := (rows 769 14 7 56 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 89 10 14 8 0 248 64 208 336 592), good := (rows 769 47 7 943 993 160 993 160 256 512) }] }

theorem upper_8 : Upper D R [768,12,3,48,64,128,16] 13 :=
  bound_sound D R [768,12,3,48,64,128,16] 13 bound_8
    ((Boolean.boundCheck_true D R [768,12,3,48,64,128,16] 13 bound_8).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 208 208 208 192 0 0 0 0 0 0), upper := (rows 769 14 7 56 80 160 96 208 464 720), lower := (rows 769 14 7 56 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 89 10 14 8 80 0 64 208 336 592), good := (rows 769 15 7 927 977 128 977 128 256 512) }] }

theorem upper_9 : Upper D R [768,12,3,48,64,128,32] 13 :=
  bound_sound D R [768,12,3,48,64,128,32] 13 bound_9
    ((Boolean.boundCheck_true D R [768,12,3,48,64,128,32] 13 bound_9).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 240 240 240 128 0 0 0 0 0 0), upper := (rows 769 14 7 56 80 160 192 240 368 624), lower := (rows 769 14 7 56 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 1 2 4 24 16 224 0 128 256 512), good := (rows 769 14 7 56 56 160 160 160 256 512) }] }

theorem upper_10 : Upper D R [768,12,3,48,64,128,128] 13 :=
  bound_sound D R [768,12,3,48,64,128,128] 13 bound_10
    ((Boolean.boundCheck_true D R [768,12,3,48,64,128,128] 13 bound_10).mp (by decide +kernel))

def route_7 : Route 10 := (fun mask => (mask,id))

theorem upper_7 : Upper D R [768,12,3,48,64,128] 13 := by
  apply routed_branch D R [768,12,3,48,64,128] 13 (by decide) (choices 1) [16,32,128] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,3,48,64,128] (choices 1) [16,32,128] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_8
  · exact upper_9
  · exact upper_10

def route_4 : Route 10 := (fun mask => (mask,id))

theorem upper_4 : Upper D R [768,12,3,48,64] 13 := by
  apply routed_branch D R [768,12,3,48,64] 13 (by decide) (choices 1) [16,64,128] route_4
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,3,48,64] (choices 1) [16,64,128] route_4).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_5
  · exact upper_6
  · exact upper_7

def route_2 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_2 : Upper D R [768,12,3,48] 13 := by
  apply routed_branch D R [768,12,3,48] 13 (by decide) (choices 1) [32,64] route_2
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,3,48] (choices 1) [32,64] route_2).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_3
  · exact upper_4

def route_1 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [768,12,3] 13 := by
  apply routed_branch D R [768,12,3] 13 (by decide) (choices 2) [48] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,12,3] (choices 2) [48] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_2

def bound_12 : Bound 10 := { allowed := (rows 224 240 224 224 0 0 0 0 0 0), upper := (rows 769 14 21 26 240 224 224 224 480 736), lower := (rows 769 14 21 26 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1023 2 4 8 0 1023 1023 1023 1023 1023), good := (rows 993 1007 997 1003 993 993 993 993 993 993) }] }

theorem upper_12 : Upper D R [768,12,17,18] 13 :=
  bound_sound D R [768,12,17,18] 13 bound_12
    ((Boolean.boundCheck_true D R [768,12,17,18] 13 bound_12).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 208 240 192 208 0 0 0 0 0 0), upper := (rows 769 14 21 42 48 240 208 208 464 720), lower := (rows 769 14 21 42 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 23 2 20 8 16 0 84 148 276 532), good := (rows 769 975 981 11 981 0 64 128 256 512) }] }

theorem upper_14 : Upper D R [768,12,17,34,32] 13 :=
  bound_sound D R [768,12,17,34,32] 13 bound_14
    ((Boolean.boundCheck_true D R [768,12,17,34,32] 13 bound_14).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 769 14 21 42 80 48 224 224 480 736), lower := (rows 769 14 21 42 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 43 2 4 8 0 32 104 168 296 552), good := (rows 769 975 5 1003 64 993 64 128 256 512) }] }

theorem upper_16 : Upper D R [768,12,17,34,64,16] 13 :=
  bound_sound D R [768,12,17,34,64,16] 13 bound_16
    ((Boolean.boundCheck_true D R [768,12,17,34,64,16] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 240 224 224 192 0 0 0 0 0 0), upper := (rows 769 14 21 42 80 96 240 176 432 688), lower := (rows 769 14 21 42 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 6 4 12 0 112 64 128 256 512), good := (rows 769 14 47 42 96 96 96 128 256 512) }] }

theorem upper_17 : Upper D R [768,12,17,34,64,64] 13 :=
  bound_sound D R [768,12,17,34,64,64] 13 bound_17
    ((Boolean.boundCheck_true D R [768,12,17,34,64,64] 13 bound_17).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 769 14 21 42 80 160 80 224 480 736), lower := (rows 769 14 21 42 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 85 6 4 14 0 244 64 208 336 592), good := (rows 769 47 943 42 993 160 993 160 256 512) }] }

theorem upper_19 : Upper D R [768,12,17,34,64,128,16] 13 :=
  bound_sound D R [768,12,17,34,64,128,16] 13 bound_19
    ((Boolean.boundCheck_true D R [768,12,17,34,64,128,16] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 208 240 192 208 0 0 0 0 0 0), upper := (rows 769 14 21 42 80 160 96 208 464 720), lower := (rows 769 14 21 42 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 85 2 84 8 80 0 64 208 336 592), good := (rows 769 15 917 10 981 128 981 128 256 512) }] }

theorem upper_20 : Upper D R [768,12,17,34,64,128,32] 13 :=
  bound_sound D R [768,12,17,34,64,128,32] 13 bound_20
    ((Boolean.boundCheck_true D R [768,12,17,34,64,128,32] 13 bound_20).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 769 14 21 42 80 160 192 144 352 608), lower := (rows 769 14 21 42 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 255 2 4 8 0 224 224 128 504 760), good := (rows 769 783 773 875 865 993 993 993 256 512) }] }

theorem upper_22 : Upper D R [768,12,17,34,64,128,128,16] 13 :=
  bound_sound D R [768,12,17,34,64,128,128,16] 13 bound_22
    ((Boolean.boundCheck_true D R [768,12,17,34,64,128,128,16] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 240 224 224 192 0 0 0 0 0 0), upper := (rows 769 14 21 42 80 160 192 160 336 592), lower := (rows 769 14 21 42 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 6 4 14 0 1023 1023 1023 256 512), good := (rows 993 238 239 234 224 224 224 224 480 736) }] }

theorem upper_23 : Upper D R [768,12,17,34,64,128,128,32] 13 :=
  bound_sound D R [768,12,17,34,64,128,128,32] 13 bound_23
    ((Boolean.boundCheck_true D R [768,12,17,34,64,128,128,32] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 240 224 224 192 0 0 0 0 0 0), upper := (rows 769 14 21 42 80 160 192 192 304 560), lower := (rows 769 14 21 42 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 6 4 14 0 1023 1023 1023 256 512), good := (rows 993 238 239 234 224 224 224 224 480 736) }] }

theorem upper_24 : Upper D R [768,12,17,34,64,128,128,64] 13 :=
  bound_sound D R [768,12,17,34,64,128,128,64] 13 bound_24
    ((Boolean.boundCheck_true D R [768,12,17,34,64,128,128,64] 13 bound_24).mp (by decide +kernel))

def route_21 : Route 10 := (fun mask => (mask,id))

theorem upper_21 : Upper D R [768,12,17,34,64,128,128] 13 := by
  apply routed_branch D R [768,12,17,34,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_21
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,17,34,64,128,128] (choices 1) [16,32,64] route_21).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_22
  · exact upper_23
  · exact upper_24

def route_18 : Route 10 := (fun mask => (mask,id))

theorem upper_18 : Upper D R [768,12,17,34,64,128] 13 := by
  apply routed_branch D R [768,12,17,34,64,128] 13 (by decide) (choices 1) [16,32,128] route_18
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,17,34,64,128] (choices 1) [16,32,128] route_18).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_19
  · exact upper_20
  · exact upper_21

def route_15 : Route 10 := (fun mask => (mask,id))

theorem upper_15 : Upper D R [768,12,17,34,64] 13 := by
  apply routed_branch D R [768,12,17,34,64] 13 (by decide) (choices 1) [16,64,128] route_15
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,17,34,64] (choices 1) [16,64,128] route_15).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_16
  · exact upper_17
  · exact upper_18

def route_13 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_13 : Upper D R [768,12,17,34] 13 := by
  apply routed_branch D R [768,12,17,34] 13 (by decide) (choices 1) [32,64] route_13
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,17,34] (choices 1) [32,64] route_13).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_14
  · exact upper_15

def bound_25 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 769 14 21 56 242 226 226 226 482 738), lower := (rows 769 14 21 56 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [768,12,17,48] 13 :=
  bound_sound D R [768,12,17,48] 13 bound_25
    ((Boolean.boundCheck_true D R [768,12,17,48] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 240 240 224 144 0 0 0 0 0 0), upper := (rows 769 14 21 104 242 242 242 242 498 754), lower := (rows 769 14 21 104 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [768,12,17,96] 13 :=
  bound_sound D R [768,12,17,96] 13 bound_26
    ((Boolean.boundCheck_true D R [768,12,17,96] 13 bound_26).mp (by decide +kernel))

def route_11 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_11 : Upper D R [768,12,17] 13 := by
  apply routed_branch D R [768,12,17] 13 (by decide) (choices 2) [18,34,48,96] route_11
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,12,17] (choices 2) [18,34,48,96] route_11).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_12
  · exact upper_13
  · exact upper_25
  · exact upper_26

def bound_28 : Bound 10 := { allowed := (rows 224 240 224 224 0 0 0 0 0 0), upper := (rows 769 14 22 25 240 224 224 224 480 736), lower := (rows 769 14 22 25 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1023 2 4 8 0 1023 1023 1023 1023 1023), good := (rows 993 1007 999 1001 993 993 993 993 993 993) }] }

theorem upper_28 : Upper D R [768,12,18,17] 13 :=
  bound_sound D R [768,12,18,17] 13 bound_28
    ((Boolean.boundCheck_true D R [768,12,18,17] 13 bound_28).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 208 240 224 208 0 0 0 0 0 0), upper := (rows 769 14 22 41 48 240 208 208 464 720), lower := (rows 769 14 22 41 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 23 2 4 8 16 0 84 148 276 532), good := (rows 769 975 983 9 977 0 64 128 256 512) }] }

theorem upper_30 : Upper D R [768,12,18,33,32] 13 :=
  bound_sound D R [768,12,18,33,32] 13 bound_30
    ((Boolean.boundCheck_true D R [768,12,18,33,32] 13 bound_30).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 224 240 224 192 0 0 0 0 0 0), upper := (rows 769 14 22 41 80 48 224 224 480 736), lower := (rows 769 14 22 41 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 43 2 4 40 0 32 104 168 296 552), good := (rows 769 975 7 1001 64 1001 64 128 256 512) }] }

theorem upper_32 : Upper D R [768,12,18,33,64,16] 13 :=
  bound_sound D R [768,12,18,33,64,16] 13 bound_32
    ((Boolean.boundCheck_true D R [768,12,18,33,64,16] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 240 208 192 208 0 0 0 0 0 0), upper := (rows 769 14 22 41 80 96 240 176 432 688), lower := (rows 769 14 22 41 80 96 64 128 256 512), losses := [{ target := 5, region := (rows 1 10 12 8 112 0 64 128 256 512), good := (rows 769 14 22 31 80 80 80 128 256 512) }] }

theorem upper_33 : Upper D R [768,12,18,33,64,64] 13 :=
  bound_sound D R [768,12,18,33,64,64] 13 bound_33
    ((Boolean.boundCheck_true D R [768,12,18,33,64,64] 13 bound_33).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 769 14 22 41 80 160 80 224 480 736), lower := (rows 769 14 22 41 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 85 6 4 94 0 244 64 208 336 592), good := (rows 769 47 943 41 1001 160 1001 160 256 512) }] }

theorem upper_35 : Upper D R [768,12,18,33,64,128,16] 13 :=
  bound_sound D R [768,12,18,33,64,128,16] 13 bound_35
    ((Boolean.boundCheck_true D R [768,12,18,33,64,128,16] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 208 240 224 208 0 0 0 0 0 0), upper := (rows 769 14 22 41 80 160 96 208 464 720), lower := (rows 769 14 22 41 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 85 2 4 8 80 0 64 208 336 592), good := (rows 769 15 919 9 977 128 977 128 256 512) }] }

theorem upper_36 : Upper D R [768,12,18,33,64,128,32] 13 :=
  bound_sound D R [768,12,18,33,64,128,32] 13 bound_36
    ((Boolean.boundCheck_true D R [768,12,18,33,64,128,32] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 240 208 192 208 0 0 0 0 0 0), upper := (rows 769 14 22 41 80 160 192 240 368 624), lower := (rows 769 14 22 41 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 1 10 14 8 248 0 224 128 256 512), good := (rows 769 30 22 95 80 208 208 208 256 512) }] }

theorem upper_37 : Upper D R [768,12,18,33,64,128,128] 13 :=
  bound_sound D R [768,12,18,33,64,128,128] 13 bound_37
    ((Boolean.boundCheck_true D R [768,12,18,33,64,128,128] 13 bound_37).mp (by decide +kernel))

def route_34 : Route 10 := (fun mask => (mask,id))

theorem upper_34 : Upper D R [768,12,18,33,64,128] 13 := by
  apply routed_branch D R [768,12,18,33,64,128] 13 (by decide) (choices 1) [16,32,128] route_34
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,18,33,64,128] (choices 1) [16,32,128] route_34).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_35
  · exact upper_36
  · exact upper_37

def route_31 : Route 10 := (fun mask => (mask,id))

theorem upper_31 : Upper D R [768,12,18,33,64] 13 := by
  apply routed_branch D R [768,12,18,33,64] 13 (by decide) (choices 1) [16,64,128] route_31
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,18,33,64] (choices 1) [16,64,128] route_31).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_32
  · exact upper_33
  · exact upper_34

def route_29 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_29 : Upper D R [768,12,18,33] 13 := by
  apply routed_branch D R [768,12,18,33] 13 (by decide) (choices 1) [32,64] route_29
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,18,33] (choices 1) [32,64] route_29).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_30
  · exact upper_31

def bound_38 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 769 14 22 56 241 225 225 225 481 737), lower := (rows 769 14 22 56 16 32 64 128 256 512), losses := [] }

theorem upper_38 : Upper D R [768,12,18,48] 13 :=
  bound_sound D R [768,12,18,48] 13 bound_38
    ((Boolean.boundCheck_true D R [768,12,18,48] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 240 240 224 144 0 0 0 0 0 0), upper := (rows 769 14 22 104 241 241 241 241 497 753), lower := (rows 769 14 22 104 16 32 64 128 256 512), losses := [] }

theorem upper_39 : Upper D R [768,12,18,96] 13 :=
  bound_sound D R [768,12,18,96] 13 bound_39
    ((Boolean.boundCheck_true D R [768,12,18,96] 13 bound_39).mp (by decide +kernel))

def route_27 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_27 : Upper D R [768,12,18] 13 := by
  apply routed_branch D R [768,12,18] 13 (by decide) (choices 2) [17,33,48,96] route_27
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,12,18] (choices 2) [17,33,48,96] route_27).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_28
  · exact upper_29
  · exact upper_38
  · exact upper_39

def bound_42 : Bound 10 := { allowed := (rows 208 208 192 208 0 0 0 0 0 0), upper := (rows 769 14 52 11 48 240 208 208 464 720), lower := (rows 769 14 52 11 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 23 6 4 14 16 0 84 148 276 532), good := (rows 769 975 991 11 977 0 64 128 256 512) }] }

theorem upper_42 : Upper D R [768,12,48,3,32] 13 :=
  bound_sound D R [768,12,48,3,32] 13 bound_42
    ((Boolean.boundCheck_true D R [768,12,48,3,32] 13 bound_42).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 769 14 52 11 80 48 224 224 480 736), lower := (rows 769 14 52 11 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 39 6 4 14 0 32 100 164 292 548), good := (rows 769 975 1007 11 64 993 64 128 256 512) }] }

theorem upper_44 : Upper D R [768,12,48,3,64,16] 13 :=
  bound_sound D R [768,12,48,3,64,16] 13 bound_44
    ((Boolean.boundCheck_true D R [768,12,48,3,64,16] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 176 176 192 176 0 0 0 0 0 0), upper := (rows 769 14 52 11 80 96 240 176 432 688), lower := (rows 769 14 52 11 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 7 6 4 14 16 32 0 132 260 516), good := (rows 769 911 959 11 16 32 0 128 256 512) }] }

theorem upper_45 : Upper D R [768,12,48,3,64,64] 13 :=
  bound_sound D R [768,12,48,3,64,64] 13 bound_45
    ((Boolean.boundCheck_true D R [768,12,48,3,64,64] 13 bound_45).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 769 14 52 11 80 160 80 224 480 736), lower := (rows 769 14 52 11 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 85 6 4 14 0 244 64 208 336 592), good := (rows 769 47 943 11 993 160 993 160 256 512) }] }

theorem upper_47 : Upper D R [768,12,48,3,64,128,16] 13 :=
  bound_sound D R [768,12,48,3,64,128,16] 13 bound_47
    ((Boolean.boundCheck_true D R [768,12,48,3,64,128,16] 13 bound_47).mp (by decide +kernel))

def bound_48 : Bound 10 := { allowed := (rows 208 208 192 208 0 0 0 0 0 0), upper := (rows 769 14 52 11 80 160 96 208 464 720), lower := (rows 769 14 52 11 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 85 6 4 14 80 0 64 208 336 592), good := (rows 769 15 927 11 977 128 977 128 256 512) }] }

theorem upper_48 : Upper D R [768,12,48,3,64,128,32] 13 :=
  bound_sound D R [768,12,48,3,64,128,32] 13 bound_48
    ((Boolean.boundCheck_true D R [768,12,48,3,64,128,32] 13 bound_48).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 240 240 128 240 0 0 0 0 0 0), upper := (rows 769 14 52 11 80 160 192 240 368 624), lower := (rows 769 14 52 11 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 1 2 20 8 16 224 0 128 256 512), good := (rows 769 14 52 11 52 160 160 160 256 512) }] }

theorem upper_49 : Upper D R [768,12,48,3,64,128,128] 13 :=
  bound_sound D R [768,12,48,3,64,128,128] 13 bound_49
    ((Boolean.boundCheck_true D R [768,12,48,3,64,128,128] 13 bound_49).mp (by decide +kernel))

def route_46 : Route 10 := (fun mask => (mask,id))

theorem upper_46 : Upper D R [768,12,48,3,64,128] 13 := by
  apply routed_branch D R [768,12,48,3,64,128] 13 (by decide) (choices 1) [16,32,128] route_46
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,48,3,64,128] (choices 1) [16,32,128] route_46).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_47
  · exact upper_48
  · exact upper_49

def route_43 : Route 10 := (fun mask => (mask,id))

theorem upper_43 : Upper D R [768,12,48,3,64] 13 := by
  apply routed_branch D R [768,12,48,3,64] 13 (by decide) (choices 1) [16,64,128] route_43
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,48,3,64] (choices 1) [16,64,128] route_43).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_44
  · exact upper_45
  · exact upper_46

def route_41 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_41 : Upper D R [768,12,48,3] 13 := by
  apply routed_branch D R [768,12,48,3] 13 (by decide) (choices 1) [32,64] route_41
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,12,48,3] (choices 1) [32,64] route_41).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_42
  · exact upper_43

def bound_50 : Bound 10 := { allowed := (rows 240 240 192 224 0 0 0 0 0 0), upper := (rows 769 14 52 25 242 226 226 226 482 738), lower := (rows 769 14 52 25 16 32 64 128 256 512), losses := [] }

theorem upper_50 : Upper D R [768,12,48,17] 13 :=
  bound_sound D R [768,12,48,17] 13 bound_50
    ((Boolean.boundCheck_true D R [768,12,48,17] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 240 240 192 224 0 0 0 0 0 0), upper := (rows 769 14 52 26 241 225 225 225 481 737), lower := (rows 769 14 52 26 16 32 64 128 256 512), losses := [] }

theorem upper_51 : Upper D R [768,12,48,18] 13 :=
  bound_sound D R [768,12,48,18] 13 bound_51
    ((Boolean.boundCheck_true D R [768,12,48,18] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 240 240 192 192 0 0 0 0 0 0), upper := (rows 769 14 52 56 211 227 195 195 451 707), lower := (rows 769 14 52 56 16 32 64 128 256 512), losses := [] }

theorem upper_52 : Upper D R [768,12,48,48] 13 :=
  bound_sound D R [768,12,48,48] 13 bound_52
    ((Boolean.boundCheck_true D R [768,12,48,48] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 240 240 192 176 0 0 0 0 0 0), upper := (rows 769 14 52 73 242 242 242 242 498 754), lower := (rows 769 14 52 73 16 32 64 128 256 512), losses := [] }

theorem upper_53 : Upper D R [768,12,48,65] 13 :=
  bound_sound D R [768,12,48,65] 13 bound_53
    ((Boolean.boundCheck_true D R [768,12,48,65] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 240 240 192 176 0 0 0 0 0 0), upper := (rows 769 14 52 74 241 241 241 241 497 753), lower := (rows 769 14 52 74 16 32 64 128 256 512), losses := [] }

theorem upper_54 : Upper D R [768,12,48,66] 13 :=
  bound_sound D R [768,12,48,66] 13 bound_54
    ((Boolean.boundCheck_true D R [768,12,48,66] 13 bound_54).mp (by decide +kernel))

def bound_55 : Bound 10 := { allowed := (rows 240 240 192 160 0 0 0 0 0 0), upper := (rows 769 14 52 88 243 227 227 227 483 739), lower := (rows 769 14 52 88 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [768,12,48,80] 13 :=
  bound_sound D R [768,12,48,80] 13 bound_55
    ((Boolean.boundCheck_true D R [768,12,48,80] 13 bound_55).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 240 240 192 48 0 0 0 0 0 0), upper := (rows 769 14 52 200 243 243 243 243 499 755), lower := (rows 769 14 52 200 16 32 64 128 256 512), losses := [] }

theorem upper_56 : Upper D R [768,12,48,192] 13 :=
  bound_sound D R [768,12,48,192] 13 bound_56
    ((Boolean.boundCheck_true D R [768,12,48,192] 13 bound_56).mp (by decide +kernel))

def route_40 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_40 : Upper D R [768,12,48] 13 := by
  apply routed_branch D R [768,12,48] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] route_40
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,12,48] (choices 2) [3,17,18,48,65,66,80,192] route_40).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_41
  · exact upper_50
  · exact upper_51
  · exact upper_52
  · exact upper_53
  · exact upper_54
  · exact upper_55
  · exact upper_56

def route_0 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 130 => (18,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [768,12] 13 := by
  apply routed_branch D R [768,12] 13 (by decide) (choices 2) [3,17,18,48] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,12] (choices 2) [3,17,18,48] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_11
  · exact upper_27
  · exact upper_40

theorem upper : Upper D R [768,12] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case56
