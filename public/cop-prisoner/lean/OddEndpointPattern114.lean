import OddEndpointCertificatesSpec
import GroupedInitialMasks
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointPattern114
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
def residue : OddEndpointGraph.Case := 5
def patchAnchor : Option Int := some (1)
def frozenArena : Arena R C := arena residue patchAnchor
instance (x z : R) : Decidable (frozenArena.messenger x z) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).messenger x z))
instance (c d : C) : Decidable (frozenArena.pursuer c d) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).pursuer c d))
instance (x : R) (c : C) : Decidable (frozenArena.collision x c) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).collision x c))
theorem arena_eq : frozenArena=arena residue patchAnchor := rfl
def replyBits (r : Nat) : Nat := (if r < 45 then (if r < 22 then (if r < 11 then (if r < 5 then (if r < 2 then (if r < 1 then 1237940039285380274899124227 else 2054) else (if r < 3 then 1237940039285380274899124236 else (if r < 4 then 1237940039285380274899124248 else 1237940039285380274899124272))) else (if r < 8 then (if r < 6 then 98 else (if r < 7 then 200 else 131456)) else (if r < 9 then 769 else (if r < 10 then 1540 else 3088)))) else (if r < 16 then (if r < 13 then (if r < 12 then 6272 else 12800) else (if r < 14 then 8413184 else (if r < 15 then 49216 else 98560))) else (if r < 19 then (if r < 17 then 197632 else (if r < 18 then 401408 else 819200)) else (if r < 20 then 538443776 else (if r < 21 then 3149824 else 6307840))))) else (if r < 33 then (if r < 27 then (if r < 24 then (if r < 23 then 12648448 else 25690112) else (if r < 25 then 52428800 else (if r < 26 then 34460401664 else 201588736))) else (if r < 30 then (if r < 28 then 403701760 else (if r < 29 then 809500672 else 1644167168)) else (if r < 31 then 3355443200 else (if r < 32 then 2205465706496 else 12901679104)))) else (if r < 39 then (if r < 36 then (if r < 34 then 25836912640 else (if r < 35 then 51808043008 else 105226698752)) else (if r < 37 then 214748364800 else (if r < 38 then 141149805215744 else 825707462656))) else (if r < 42 then (if r < 40 then 1653562408960 else (if r < 41 then 3315714752512 else 6734508720128)) else (if r < 43 then 13743895347200 else (if r < 44 then 9033587533807616 else 52845277609984)))))) else (if r < 68 then (if r < 56 then (if r < 50 then (if r < 47 then (if r < 46 then 105827994173440 else 212205744160768) else (if r < 48 then 1275433488220160 else (if r < 49 then 0 else 0))) else (if r < 53 then (if r < 51 then 3382097767038976 else (if r < 52 then 6772991627100160 else 13581167626289152)) else (if r < 54 then 81064793292668928 else (if r < 55 then 0 else 0)))) else (if r < 62 then (if r < 59 then (if r < 57 then 216207966485872640 else (if r < 58 then 433471464134410240 else 1445655480385929216)) else (if r < 60 then 0 else (if r < 61 then 3602879701896396800 else 2368100770462463688704))) else (if r < 65 then (if r < 63 then 13837309855095848960 else (if r < 64 then 27742173704602255360 else 55628462597280366592)) else (if r < 66 then 112986307451471003648 else (if r < 67 then 230584300921369395200 else 151558449309597676077056))))) else (if r < 79 then (if r < 73 then (if r < 70 then (if r < 69 then 886596637042665324544 else 1775499117094544343040) else (if r < 71 then 3560221606225943461888 else (if r < 72 then 7231123676894144233472 else 14757395258967641292800))) else (if r < 76 then (if r < 74 then 9699740755814251268931584 else (if r < 75 then 56742184770730580770816 else 113631943494050837954560)) else (if r < 77 then 227854182798460381560832 else (if r < 78 then 462791915321225230942208 else 944473296573929042739200)))) else (if r < 85 then (if r < 82 then (if r < 80 then 620783408372112081211621376 else (if r < 81 then 3631499825326757169332224 else 7272444383619253629091840)) else (if r < 83 then 14582667699101464419893248 else (if r < 84 then 29618682580558414780301312 else 60446290980731458735308800))) else (if r < 88 then (if r < 86 then 1353996917968384675670917120 else (if r < 87 then 232415988820912458837262336 else 465436440551632232261877760)) else (if r < 89 then 933290732742493722873167872 else (if r < 90 then 1895595685155738545939283968 else 2475577847115856892504575999)))))))
def replyMasks (c : C) : Nat := replyBits c.val
def collisionBits (r : Nat) : Nat := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then 4096 else 8192) else (if r < 3 then 16384 else 32768)) else (if r < 6 then (if r < 5 then 65536 else 131072) else (if r < 7 then 262144 else 524288))) else (if r < 12 then (if r < 10 then (if r < 9 then 1048576 else 2097152) else (if r < 11 then 4194304 else 8388608)) else (if r < 14 then (if r < 13 then 16777216 else 33554432) else (if r < 15 then 67108864 else 134217728)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then 268435456 else 536870912) else (if r < 19 then 1073741824 else 2147483648)) else (if r < 22 then (if r < 21 then 4294967296 else 8589934592) else (if r < 23 then 17179869184 else 34359738368))) else (if r < 28 then (if r < 26 then (if r < 25 then 68719476736 else 137438953472) else (if r < 27 then 274877906944 else 549755813888)) else (if r < 30 then (if r < 29 then 1099511627776 else 2199023255552) else (if r < 31 then 4398046511104 else (if r < 32 then 8796093022208 else 17592186044416)))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then 35184372088832 else 70368744177664) else (if r < 36 then 140737488355328 else 2475880078570760549798248447)) else (if r < 39 then (if r < 38 then 2475880078570760549798248447 else 1125899906842624) else (if r < 40 then 2251799813685248 else 4503599627370496))) else (if r < 45 then (if r < 43 then (if r < 42 then 9007199254740992 else 2475880078570760549798248447) else (if r < 44 then 2475880078570760549798248447 else 72057594037927936)) else (if r < 47 then (if r < 46 then 144115188075855872 else 288230376151711744) else (if r < 48 then 2475880078570760549798248447 else 1152921504606846976)))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then 2305843009213693952 else 4611686018427387904) else (if r < 52 then 9223372036854775808 else 18446744073709551616)) else (if r < 55 then (if r < 54 then 36893488147419103232 else 73786976294838206464) else (if r < 56 then 147573952589676412928 else 295147905179352825856))) else (if r < 61 then (if r < 59 then (if r < 58 then 590295810358705651712 else 1180591620717411303424) else (if r < 60 then 2361183241434822606848 else 4722366482869645213696)) else (if r < 63 then (if r < 62 then 9444732965739290427392 else 18889465931478580854784) else (if r < 64 then 37778931862957161709568 else (if r < 65 then 75557863725914323419136 else 151115727451828646838272)))))))
def collisionMasks (x : R) : Nat := collisionBits x.val
def requiredBits (r : Nat) : Nat := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then 2475880077939412177036242943 else 2475880077939412177036238847) else (if r < 3 then 2475880077939412177036230655 else 2475880077939412177036214271)) else (if r < 6 then (if r < 5 then 2475880077939412177036181503 else 2475880077939412177036115967) else (if r < 7 then 2475880077939412177035984895 else 2475880077939412177035722751))) else (if r < 12 then (if r < 10 then (if r < 9 then 2475880077939412177035198463 else 2475880077939412177034149887) else (if r < 11 then 2475880077939412177032052735 else 2475880077939412177027858431)) else (if r < 14 then (if r < 13 then 2475880077939412177019469823 else 2475880077939412177002692607) else (if r < 15 then 2475880077939412176969138175 else 2475880077939412176902029311)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then 2475880077939412176767811583 else 2475880077939412176499376127) else (if r < 19 then 2475880077939412175962505215 else 2475880077939412174888763391)) else (if r < 22 then (if r < 21 then 2475880077939412172741279743 else 2475880077939412168446312447) else (if r < 23 then 2475880077939412159856377855 else 2475880077939412142676508671))) else (if r < 28 then (if r < 26 then (if r < 25 then 2475880077939412108316770303 else 2475880077939412039597293567) else (if r < 27 then 2475880077939411902158340095 else 2475880077939411627280433151)) else (if r < 30 then (if r < 29 then 2475880077939411077524619263 else 2475880077939409978012991487) else (if r < 31 then 2475880077939407778989735935 else (if r < 32 then 2475880077939403380943224831 else 2475880077939394584850202623)))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then 2475880077939376992664158207 else 2475880077939341808292069375) else (if r < 36 then 2475880077939271439547891711 else 0)) else (if r < 39 then (if r < 38 then 0 else 2475880077938286277129404415) else (if r < 40 then 2475880077937160377222561791 else 2475880077934908577408876543))) else (if r < 45 then (if r < 43 then (if r < 42 then 2475880077930404977781506047 else 0) else (if r < 44 then 0 else 2475880077867354582998319103)) else (if r < 47 then (if r < 46 then 2475880077795296988960391167 else 2475880077651181800884535295) else (if r < 48 then 0 else 2475880076786490672429400063)))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then 2475880075633569167822553087 else 2475880073327726158608859135) else (if r < 52 then 2475880068716040140181471231 else 2475880059492668103326695423)) else (if r < 55 then (if r < 54 then 2475880041045924029617143807 else 2475880004152435882198040575) else (if r < 56 then 2475879930365459587359834111 else 2475879782791506997683421183))) else (if r < 61 then (if r < 59 then (if r < 58 then 2475879487643601818330595327 else 2475878897347791459624943615) else (if r < 60 then 2475877716756170742213640191 else 2475875355572929307391033343)) else (if r < 63 then (if r < 62 then 2475870633206446437745819647 else 2475861188473480698455392255) else (if r < 64 then 2475842299007549219874537471 else (if r < 65 then 2475804520075686262712827903 else 2475728962211960348389408767)))))))
def requiredMasks (x : R) : Nat := requiredBits x.val
def validMask : Nat := 2475880077939412177036247039
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
end Delivery.OddEndpointPattern114
