import SixTypeObjective08Transfer
import SixTypeObjective08Delivery0
import SixTypeObjective08Delivery1
import SixTypeObjective08Delivery2
import SixTypeObjective08Delivery3
import SixTypeObjective08Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate08
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern08.pattern := by
  constructor
  · exact ⟨SixTypeObjective08Transfer.data, SixTypeObjective08Transfer.checked, SixTypeObjective08Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective08Delivery0.data, SixTypeObjective08Delivery0.checked, SixTypeObjective08Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective08Delivery1.data, SixTypeObjective08Delivery1.checked, SixTypeObjective08Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective08Delivery2.data, SixTypeObjective08Delivery2.checked, SixTypeObjective08Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective08Delivery3.data, SixTypeObjective08Delivery3.checked, SixTypeObjective08Delivery3.initial_states⟩
    · simp [SixTypePattern08.pattern] at present
    · exact ⟨SixTypeObjective08Delivery5.data, SixTypeObjective08Delivery5.checked, SixTypeObjective08Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate08
