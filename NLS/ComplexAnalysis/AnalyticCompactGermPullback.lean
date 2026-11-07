import NLS.ComplexAnalysis.AnalyticGermPullback
import NLS.FunctionalAnalysis.CompactDerivativeComposition

/-! # Analytic germ pullback retaining a compact derivative principal -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.ComplexAnalysis
variable {E F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem analytic_germ_pullback_compact_properties
    (L : E →L[ℂ] H) (D : Set H) (hD : IsOpen D) (q : E) (hqD : L q∈D)
    (U : Set E) (hU : IsOpen U) (hqU : q∈U) (g : E → F) (hg : AnalyticOnNhd ℂ g U)
    (A : Set F) (hA : IsOpen A) (hgqA : g q∈A) (B : F → Y) (hB : AnalyticOnNhd ℂ B A)
    (Qg : E →L[ℂ] F) (QB : F →L[ℂ] Y)
    (hgc : IsCompactOperator (fderiv ℂ g q-Qg))
    (hBc : IsCompactOperator (fderiv ℂ B (g q)-QB))
    (P : E → Y → Prop) (hP : ∀ x, x∈U → g x∈A → L x∈D → P x (B (g x))) :
    ∃ V : Set E, IsOpen V ∧ q∈V ∧ ∃ G : E → Y,
      AnalyticOnNhd ℂ G V ∧
      IsCompactOperator (fderiv ℂ G q-QB.comp Qg) ∧ ∀ x∈V, P x (G x) := by
  let V := (U∩g ⁻¹' A)∩L ⁻¹' D
  have hV : IsOpen V := (hg.continuousOn.isOpen_inter_preimage hU hA).inter
    (hD.preimage L.continuous)
  refine ⟨V,hV,⟨⟨hqU,hgqA⟩,hqD⟩,(fun x => B (g x)),?_,?_,?_⟩
  · intro x hx
    exact (hB (g x) hx.1.2).comp (hg x hx.1.1)
  · exact isCompactOperator_fderiv_comp_sub_principals g B q Qg QB
      (hg q hqU).differentiableAt (hB (g q) hgqA).differentiableAt hgc hBc
  · intro x hx
    exact hP x hx.1.1 hx.1.2 hx.2


end NLS.ComplexAnalysis
