import OddEndpointObjective047Transfer
import OddEndpointObjective047Delivery2
import OddEndpointObjective047Delivery3
import OddEndpointObjective047Delivery4
import OddEndpointObjective047Delivery5
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate047
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern047
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective047Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact False.elim ((by decide : ¬targetAllowed residue patchAnchor 0) allowed)
    · exact False.elim ((by decide : ¬targetAllowed residue patchAnchor 1) allowed)
    · exact ⟨OddEndpointObjective047Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective047Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective047Delivery4.certificate⟩
    · exact ⟨OddEndpointObjective047Delivery5.certificate⟩
#print axioms certificates
end Delivery.OddEndpointCertificate047
