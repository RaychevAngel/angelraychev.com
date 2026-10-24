import OddEndpointCertificatesSpec
import GroupedInitialMasks
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointPattern099
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
def residue : OddEndpointGraph.Case := 4
def patchAnchor : Option Int := some (8)
def frozenArena : Arena R C := arena residue patchAnchor
instance (x z : R) : Decidable (frozenArena.messenger x z) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).messenger x z))
instance (c d : C) : Decidable (frozenArena.pursuer c d) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).pursuer c d))
instance (x : R) (c : C) : Decidable (frozenArena.collision x c) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).collision x c))
theorem arena_eq : frozenArena=arena residue patchAnchor := rfl
def replyBits (r : Nat) : Nat := (if r < 45 then (if r < 22 then (if r < 11 then (if r < 5 then (if r < 2 then (if r < 1 then 1237940039285380274899124227 else 1237940039285380274899124230) else (if r < 3 then 2060 else (if r < 4 then 280 else 1237940039285380274899124272))) else (if r < 8 then (if r < 6 then 608 else (if r < 7 then 208 else 386)) else (if r < 9 then 131840 else (if r < 10 then 17920 else 3073)))) else (if r < 16 then (if r < 13 then (if r < 12 then 38912 else 13312) else (if r < 14 then 24704 else (if r < 15 then 8437760 else 1146880))) else (if r < 19 then (if r < 17 then 196672 else (if r < 18 then 2490368 else 851968)) else (if r < 20 then 1581056 else (if r < 21 then 540016640 else 73400320))))) else (if r < 33 then (if r < 27 then (if r < 24 then (if r < 23 then 12587008 else 159383552) else (if r < 25 then 54525952 else (if r < 26 then 101187584 else 34561064960))) else (if r < 30 then (if r < 28 then 4697620480 else (if r < 29 then 805568512 else 10200547328)) else (if r < 31 then 3489660928 else (if r < 32 then 6476005376 else 2211908157440)))) else (if r < 39 then (if r < 36 then (if r < 34 then 300647710720 else (if r < 35 then 51556384768 else 652835028992)) else (if r < 37 then 223338299392 else (if r < 38 then 414464344064 else 141562122076160))) else (if r < 42 then (if r < 40 then 19241453486080 else (if r < 41 then 3299608625152 else 41781441855488)) else (if r < 43 then 14293651161088 else (if r < 44 then 26525718020096 else 9059975812874240)))))) else (if r < 68 then (if r < 56 then (if r < 50 then (if r < 47 then (if r < 46 then 1231453023109120 else 211174952009728) else (if r < 48 then 2674012278751232 else (if r < 49 then 914793674309632 else 1697645953286144))) else (if r < 53 then (if r < 51 then 579838452023951360 else (if r < 52 then 78812993478983680 else 13515196928622592)) else (if r < 54 then 171136785840078848 else (if r < 55 then 58546795155816448 else 108649341010313216)))) else (if r < 62 then (if r < 59 then (if r < 57 then 37109660929532887040 else (if r < 58 then 5044031582654955520 else 864972603431845888)) else (if r < 60 then 10952754293765046272 else (if r < 61 then 3746994889972252672 else 6953557824660045824))) else (if r < 65 then (if r < 63 then 2375018299490104770560 else (if r < 64 then 322818021289917153280 else 55358246619638136832)) else (if r < 66 then 700976274800962961408 else (if r < 67 then 239807672958224171008 else 445027700778242932736))))) else (if r < 79 then (if r < 73 then (if r < 70 then (if r < 69 then 152001171167366705315840 else 20660353362554697809920) else (if r < 71 then 3542927783656840757248 else (if r < 72 then 44862481587261629530112 else 15347691069326346944512))) else (if r < 76 then (if r < 74 then 28481772849807547695104 else (if r < 75 then 9728074954711469140213760 else 1322262615203500659834880)) else (if r < 77 then 226747378154037808463872 else (if r < 78 then 2871198821584744289927168 else 982252228436886204448768)))) else (if r < 85 then (if r < 82 then (if r < 80 then 1822833462387683052486656 else (if r < 81 then 622596797101534024973680640 else 84624807373024042229432320)) else (if r < 83 then 14511832201858419741687808 else (if r < 84 then 183756724581423634555338752 else 62864142619960717084721152))) else (if r < 88 then (if r < 86 then 116661341592811715359145984 else (if r < 87 then 1470053796651389076442710016 else 2011652563838742946711076864)) else (if r < 89 then 0 else (if r < 90 then 1856910058928070412348686336 else 2166092837294511823779794943)))))))
def replyMasks (c : C) : Nat := replyBits c.val
def collisionBits (r : Nat) : Nat := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then 4096 else 8192) else (if r < 3 then 16384 else 32768)) else (if r < 6 then (if r < 5 then 65536 else 131072) else (if r < 7 then 262144 else 524288))) else (if r < 12 then (if r < 10 then (if r < 9 then 1048576 else 2097152) else (if r < 11 then 4194304 else 8388608)) else (if r < 14 then (if r < 13 then 16777216 else 33554432) else (if r < 15 then 67108864 else 134217728)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then 268435456 else 536870912) else (if r < 19 then 1073741824 else 2147483648)) else (if r < 22 then (if r < 21 then 4294967296 else 8589934592) else (if r < 23 then 17179869184 else 34359738368))) else (if r < 28 then (if r < 26 then (if r < 25 then 68719476736 else 137438953472) else (if r < 27 then 274877906944 else 549755813888)) else (if r < 30 then (if r < 29 then 1099511627776 else 2199023255552) else (if r < 31 then 4398046511104 else (if r < 32 then 8796093022208 else 17592186044416)))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then 35184372088832 else 70368744177664) else (if r < 36 then 140737488355328 else 281474976710656)) else (if r < 39 then (if r < 38 then 562949953421312 else 1125899906842624) else (if r < 40 then 2251799813685248 else 4503599627370496))) else (if r < 45 then (if r < 43 then (if r < 42 then 9007199254740992 else 18014398509481984) else (if r < 44 then 36028797018963968 else 72057594037927936)) else (if r < 47 then (if r < 46 then 144115188075855872 else 288230376151711744) else (if r < 48 then 576460752303423488 else 1152921504606846976)))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then 2305843009213693952 else 4611686018427387904) else (if r < 52 then 9223372036854775808 else 18446744073709551616)) else (if r < 55 then (if r < 54 then 36893488147419103232 else 73786976294838206464) else (if r < 56 then 147573952589676412928 else 295147905179352825856))) else (if r < 61 then (if r < 59 then (if r < 58 then 590295810358705651712 else 1180591620717411303424) else (if r < 60 then 2361183241434822606848 else 4722366482869645213696)) else (if r < 63 then (if r < 62 then 9444732965739290427392 else 18889465931478580854784) else (if r < 64 then 37778931862957161709568 else (if r < 65 then 75557863725914323419136 else 151115727451828646838272)))))))
def collisionMasks (x : R) : Nat := collisionBits x.val
def requiredBits (r : Nat) : Nat := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then 2166395068749415481073463295 else 2166395068749415481073459199) else (if r < 3 then 2166395068749415481073451007 else 2166395068749415481073434623)) else (if r < 6 then (if r < 5 then 2166395068749415481073401855 else 2166395068749415481073336319) else (if r < 7 then 2166395068749415481073205247 else 2166395068749415481072943103))) else (if r < 12 then (if r < 10 then (if r < 9 then 2166395068749415481072418815 else 2166395068749415481071370239) else (if r < 11 then 2166395068749415481069273087 else 2166395068749415481065078783)) else (if r < 14 then (if r < 13 then 2166395068749415481056690175 else 2166395068749415481039912959) else (if r < 15 then 2166395068749415481006358527 else 2166395068749415480939249663)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then 2166395068749415480805031935 else 2166395068749415480536596479) else (if r < 19 then 2166395068749415479999725567 else 2166395068749415478925983743)) else (if r < 22 then (if r < 21 then 2166395068749415476778500095 else 2166395068749415472483532799) else (if r < 23 then 2166395068749415463893598207 else 2166395068749415446713729023))) else (if r < 28 then (if r < 26 then (if r < 25 then 2166395068749415412353990655 else 2166395068749415343634513919) else (if r < 27 then 2166395068749415206195560447 else 2166395068749414931317653503)) else (if r < 30 then (if r < 29 then 2166395068749414381561839615 else 2166395068749413282050211839) else (if r < 31 then 2166395068749411083026956287 else (if r < 32 then 2166395068749406684980445183 else 2166395068749397888887422975)))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then 2166395068749380296701378559 else 2166395068749345112329289727) else (if r < 36 then 2166395068749274743585112063 else 2166395068749134006096756735)) else (if r < 39 then (if r < 38 then 2166395068748852531120046079 else 2166395068748289581166624767) else (if r < 40 then 2166395068747163681259782143 else 2166395068744911881446096895))) else (if r < 45 then (if r < 43 then (if r < 42 then 2166395068740408281818726399 else 2166395068731401082563985407) else (if r < 44 then 2166395068713386684054503423 else 2166395068677357887035539455)) else (if r < 47 then (if r < 46 then 2166395068605300292997611519 else 2166395068461185104921755647) else (if r < 48 then 2166395068172954728770043903 else 2166395067596493976466620415)))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then 2166395066443572471859773439 else 2166395064137729462646079487) else (if r < 52 then 2166395059526043444218691583 else 2166395050302671407363915775)) else (if r < 55 then (if r < 54 then 2166395031855927333654364159 else 2166394994962439186235260927) else (if r < 56 then 2166394921175462891397054463 else 2166394773601510301720641535))) else (if r < 61 then (if r < 59 then (if r < 58 then 2166394478453605122367815679 else 2166393888157794763662163967) else (if r < 60 then 2166392707566174046250860543 else 2166390346382932611428253695)) else (if r < 63 then (if r < 62 then 2166385624016449741783039999 else 2166376179283484002492612607) else (if r < 64 then 2166357289817552523911757823 else (if r < 65 then 2166319510885689566750048255 else 2166243953021963652426629119)))))))
def requiredMasks (x : R) : Nat := requiredBits x.val
def validMask : Nat := 2166395068749415481073467391
theorem reply_cases : ∀ c, presentC residue patchAnchor c →
    if c=outside then ∀ d, presentC residue patchAnchor d →
      (d=outside ∨ boundary residue d) → Has (replyMasks c) d
    else Has (replyMasks c) c ∧ ∀ b : Bool, permitted residue patchAnchor (cvertex c) b →
      Has (replyMasks c) (pack residue (next residue patchAnchor b (cvertex c))) := by
  unfold Has
  decide +kernel
theorem reply_coverage : ∀ c d, frozenArena.pursuer c d → Has (replyMasks c) d := by
  intro c d move
  obtain ⟨pc,pd,step⟩ := move
  have covered := reply_cases c pc
  by_cases out : c=outside
  · rw [if_pos out] at step covered
    exact covered d pd step
  · rw [if_neg out] at step covered
    rcases step with wait|⟨b,allowed,same⟩
    · simpa only [wait] using covered.1
    · rw [same]
      exact covered.2 b allowed
theorem collision_rows : ∀ x,
    (presentR residue patchAnchor x → Has (collisionMasks x) (pack residue (rvertex x))) ∧
    (¬presentR residue patchAnchor x → collisionMasks x=2^91-1) := by
  unfold Has
  decide +kernel
theorem collision_coverage : ∀ x c, frozenArena.collision x c → Has (collisionMasks x) c :=
  GroupedInitialMasks.collision_coverage (presentR residue patchAnchor)
    (fun x => pack residue (rvertex x)) collisionMasks collision_rows
theorem valid_bits : ∀ c, presentC residue patchAnchor c → Has validMask c := by
  unfold Has
  decide +kernel
theorem required_rows : ∀ x, presentR residue patchAnchor x →
    requiredMasks x=validMask ^^^ 2^(pack residue (rvertex x)).val := by
  decide +kernel
theorem required_coverage : ∀ x c, presentR residue patchAnchor x → presentC residue patchAnchor c →
    ¬(arena residue patchAnchor).collision x c → Has (requiredMasks x) c :=
  GroupedInitialMasks.required_coverage (presentR residue patchAnchor) (presentC residue patchAnchor)
    (fun x => pack residue (rvertex x)) validMask requiredMasks valid_bits required_rows
#print axioms arena_eq
#print axioms required_coverage
end Delivery.OddEndpointPattern099
