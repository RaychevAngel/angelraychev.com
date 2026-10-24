import OddEndpointObjective025Transfer
import OddEndpointObjective025Delivery0
import OddEndpointObjective025Delivery1
import OddEndpointObjective025Delivery2
import OddEndpointObjective025Delivery4
import OddEndpointObjective025Delivery5
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate025
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern025
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective025Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective025Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective025Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective025Delivery2.certificate⟩
    · exact False.elim ((by decide : ¬targetAllowed residue patchAnchor 3) allowed)
    · exact ⟨OddEndpointObjective025Delivery4.certificate⟩
    · exact ⟨OddEndpointObjective025Delivery5.certificate⟩
#print axioms certificates
end Delivery.OddEndpointCertificate025
