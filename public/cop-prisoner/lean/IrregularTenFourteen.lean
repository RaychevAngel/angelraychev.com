import IrregularTen14Case00
import IrregularTen14Case01
import IrregularTen14Case02
import IrregularTen14Case03
import IrregularTen14Case04
import IrregularTen14Case05
import IrregularTen14Case06
import IrregularTen14Case07
import IrregularTen14Case08
import IrregularTen14Case09
import IrregularTen14Case10
import IrregularTen14Case11
import IrregularTen14Case12
import IrregularTen14Case13
import IrregularTen14Case14
import IrregularTen14Case15
import IrregularTen14Case16
import IrregularTen14Case17
import IrregularTen14Case18
import IrregularTen14Case19
import IrregularTen14Case20
import IrregularTen14Case21
import IrregularTen14Case22
import IrregularTen14Case23
import IrregularTen14Case24
import IrregularTen14Case25
import IrregularTen14Case26
import IrregularTen14Case27
import IrregularTen14Case28
import IrregularTen14Case29
import IrregularTen14Case30
import IrregularTen14Case31
import IrregularTen14Case32
import IrregularTen14Case33
import IrregularTen14Case34
import IrregularTen14Case35
import IrregularTen14Case36
import IrregularTen14Case37
import IrregularTen14Case38
import IrregularTen14Case39
import IrregularTen14Case40
import IrregularTen14Case41
import IrregularTen14Case42
import IrregularTen14Case43
import IrregularTen14Case44
import IrregularTen14Case45
import IrregularTen14Case46
import IrregularTen14Case47
import IrregularTen14Case48
import IrregularTen14Case49
import IrregularTen14Case50
import IrregularTen14Case51
import IrregularTen14Case52
import IrregularTen14Case53
import IrregularTen14Case54
import IrregularTen14Case55
import IrregularTen14Case56
import IrregularTen14Case57
import IrregularTen14Case58
import IrregularTen14Case59
import IrregularTenProfile

namespace Delivery.IrregularTen14
open FiniteGame Extremal RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row_6 : Upper D R [6] 13 := by
  apply routed_branch D R [6] 13 (by decide) (choices 2) [9,17,24,48,257,264,272,768]
    (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 513 => (257,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 136 => (24,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 520 => (264,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 544 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 576 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (272,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 640 => (272,(fun i => match i.val with | 4 => 7 | 7 => 4 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))
    (by exact cover_two) (by decide +kernel)
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Case00.upper
  · exact Case01.upper
  · exact Case02.upper
  · exact Case03.upper
  · exact Case04.upper
  · exact Case05.upper
  · exact Case06.upper
  · exact Case07.upper

theorem row_18 : Upper D R [18] 13 := by
  apply routed_branch D R [18] 13 (by decide) (choices 2) [5,12,17,20,33,36,48,96,257,260,272,288,768]
    (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 513 => (257,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 516 => (260,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 136 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 7 | 7 => 5 | _ => i)) | 264 => (260,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 520 => (260,(fun i => match i.val with | 2 => 3 | 3 => 2 | 8 => 9 | 9 => 8 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 576 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 640 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))
    (by exact cover_two) (by decide +kernel)
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Case08.upper
  · exact Case09.upper
  · exact Case10.upper
  · exact Case11.upper
  · exact Case12.upper
  · exact Case13.upper
  · exact Case14.upper
  · exact Case15.upper
  · exact Case16.upper
  · exact Case17.upper
  · exact Case18.upper
  · exact Case19.upper
  · exact Case20.upper

theorem row_48 : Upper D R [48] 13 := by
  apply routed_branch D R [48] 13 (by decide) (choices 2) [5,12,17,20,48,65,68,80,192,257,260,272,320,768]
    (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 513 => (257,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 516 => (260,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 136 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 264 => (260,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 520 => (260,(fun i => match i.val with | 2 => 3 | 3 => 2 | 8 => 9 | 9 => 8 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 544 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))
    (by exact cover_two) (by decide +kernel)
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Case21.upper
  · exact Case22.upper
  · exact Case23.upper
  · exact Case24.upper
  · exact Case25.upper
  · exact Case26.upper
  · exact Case27.upper
  · exact Case28.upper
  · exact Case29.upper
  · exact Case30.upper
  · exact Case31.upper
  · exact Case32.upper
  · exact Case33.upper
  · exact Case34.upper

theorem row_258 : Upper D R [258] 13 := by
  apply routed_branch D R [258] 13 (by decide) (choices 2) [5,12,17,20,48,513,516,528]
    (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 132 => (20,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 6 | 6 => 4 | _ => i)) | 136 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 7 | 7 => 4 | _ => i)) | 520 => (516,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 576 => (528,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 640 => (528,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | _ => (mask,id))
    (by exact cover_two) (by decide +kernel)
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Case35.upper
  · exact Case36.upper
  · exact Case37.upper
  · exact Case38.upper
  · exact Case39.upper
  · exact Case40.upper
  · exact Case41.upper
  · exact Case42.upper

theorem row_272 : Upper D R [272] 13 := by
  apply routed_branch D R [272] 13 (by decide) (choices 2) [5,12,17,20,33,36,48,96,513,516,528,544]
    (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 136 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 7 | 7 => 5 | _ => i)) | 520 => (516,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))
    (by exact cover_two) (by decide +kernel)
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Case43.upper
  · exact Case44.upper
  · exact Case45.upper
  · exact Case46.upper
  · exact Case47.upper
  · exact Case48.upper
  · exact Case49.upper
  · exact Case50.upper
  · exact Case51.upper
  · exact Case52.upper
  · exact Case53.upper
  · exact Case54.upper

theorem row_768 : Upper D R [768] 13 := by
  apply routed_branch D R [768] 13 (by decide) (choices 2) [5,12,17,20,48]
    (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 132 => (20,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 6 | 6 => 4 | _ => i)) | 136 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))
    (by exact cover_two) (by decide +kernel)
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Case55.upper
  · exact Case56.upper
  · exact Case57.upper
  · exact Case58.upper
  · exact Case59.upper

theorem canonical_upper : Upper D R [] 13 := by
  apply routed_branch D R [] 13 (by decide) (choices 2) [6,18,48,258,272,768]
    (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 130 => (18,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 514 => (258,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 36 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 5 | 5 => 4 | _ => i)) | 68 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 6 | 6 => 4 | _ => i)) | 132 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 7 | 7 => 4 | _ => i)) | 260 => (258,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 516 => (258,(fun i => match i.val with | 1 => 2 | 2 => 1 | 8 => 9 | 9 => 8 | _ => i)) | 24 => (18,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 40 => (18,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (18,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 6 | 6 => 4 | _ => i)) | 136 => (18,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 7 | 7 => 4 | _ => i)) | 264 => (258,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 520 => (258,(fun i => match i.val with | 1 => 3 | 3 => 1 | 8 => 9 | 9 => 8 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 544 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 576 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (272,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 640 => (272,(fun i => match i.val with | 4 => 7 | 7 => 4 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))
    (by exact cover_two) (by decide +kernel)
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_6
  · exact row_18
  · exact row_48
  · exact row_258
  · exact row_272
  · exact row_768

/-- Unconditional upper bound for the full positive-degree ten-vertex,
fourteen-arrow family. Degree-profile coverage and all search branches are checked. -/
theorem positive_upper (E : Graph (Fin 10)) (loopless : Loopless E)
    (budget : arcCount E = 14)
    (positiveOut : ∀ x, 1 ≤ SparseSupport.outdegree E x)
    (positiveIn : ∀ x, 1 ≤ SparseSupport.indegree E x) : score E ≤ 13 := by
  by_cases small : score E ≤ 13
  · exact small
  · obtain ⟨F,⟨iso⟩,loops,outDegrees,inDegrees⟩ :=
      IrregularTenProfile.normalize E loopless budget positiveOut positiveIn (by omega)
    have prescribed : Prescribed D R F := ⟨loops,outDegrees,inDegrees⟩
    have bound := canonical_upper F prescribed (by intro s h; simp at h)
    rw [GraphRelabeling.score_eq iso]
    exact bound

#print axioms canonical_upper
#print axioms positive_upper
end Delivery.IrregularTen14
