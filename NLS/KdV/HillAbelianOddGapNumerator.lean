import NLS.KdV.HillAbelianFrequencyDifferentials
import NLS.ZakharovShabat.SourceOmittedRootReflection
import NLS.ZakharovShabat.SourceAngularBetaRegularFactorBound

/-! The ACTUAL Hill gap numerator is the difference of two signed
Dirac gap numerators at opposite frequencies. No product-scalar
normalization or ordinary Dirichlet-terminal substitution is used. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem abelianFrequencyNumerator_eq_odd_selected (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ) :
    P.abelianFrequencyNumerator n (z,q) =
      sourcePsiCandidate ((n:ℕ):ℤ) (z,(P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2))-
      sourcePsiCandidate ((n:ℕ):ℤ) (-z,(P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2)) := by
  rw [P.abelianFrequencyNumerator_eq_local n z q hq]
  simp only [HillHminusDirichletBall.psiNumerator,sub_add_cancel]
  exact P.parent.family.numerator_frequency_identity n _ z

theorem abelianGapNumerator_eq_signed_difference (P : HillProductEquationPatch) (n m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi q)) :
    P.abelianGapNumerator n m (z,q) =
      sourceAngularGapNumerator (by norm_num) (by norm_num) ((n:ℕ):ℤ) ((m:ℕ):ℤ)
        P.parent.family.roots (P.sourcePsi q) z-
      sourceAngularGapNumerator (by norm_num) (by norm_num) ((n:ℕ):ℤ) (-((m:ℕ):ℤ))
        P.parent.family.roots (P.sourcePsi q) (-z) := by
  have h : SourcePeriodicReflection (by norm_num) (by norm_num) (P.sourcePsi q) :=
    sourcePeriodicReflection_hillMiuraDiagonal (P.parent.parent.miuraBall.actionBall.lift q)
  have he := h.omittedProduct_neg ((m:ℕ):ℤ) z hz
  unfold abelianGapNumerator sourceAngularGapNumerator
  rw [P.abelianFrequencyNumerator_eq_odd_selected n q hq z,he,sub_div]

end NLS.KdV.HillProductEquationPatch
