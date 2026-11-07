import NLS.Poisson.GardnerHamiltonianDirection
import NLS.SequenceSpaces.PeriodOneHminusOneRealForm
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.ComplexAnalysis.RealFormDifferential

/-! Native Gardner Hamiltonians preserve the physical real form
when their local scalar values are real. Cotangent reality uses the
actual conjugate-reflected Fourier convention, rather than entrywise
real coefficients. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.Poisson

theorem fderiv_real_on_physical_real_germ (F : PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hF : AnalyticAt ℂ F q)
    (hreal : ∀ᶠ p in 𝓝 q, IsRealPeriodOneHminusOne p → (F p).im=0)
    (v : PeriodOneHminusOne) (hv : IsRealPeriodOneHminusOne v) :
    ((fderiv ℂ F q) v).im=0 :=
  fderiv_im_eq_zero_of_fixed_real_germ periodOneHminusConjugation F q
    ((isRealPeriodOneHminusOne_iff_conjugation_fixed q).mp hq) hF
    (hreal.mono (fun p hp hpr => hp ((isRealPeriodOneHminusOne_iff_conjugation_fixed p).mpr hpr))) v
    ((isRealPeriodOneHminusOne_iff_conjugation_fixed v).mp hv)

theorem hminusCotangentCLM_real_of_real_form (L : PeriodOneHminusOne →L[ℂ] ℂ)
    (hL : ∀ v, IsRealPeriodOneHminusOne v → (L v).im=0) :
    ∀ k : ℤ, (hminusCotangentCLM L).val (-k)=conj ((hminusCotangentCLM L).val k) := by
  intro k
  let e : ℤ → PeriodOneHminusOne := fun j => WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single j 1)
  have hJ : periodOneHminusConjugation (e (-k))=e k := by
    apply Subtype.ext
    funext j
    simp only [periodOneHminusConjugation,WeightedCoeff.sobolevConjugation_apply,e,
      WeightedCoeff.ofFinsupp_apply,Finsupp.single_apply]
    by_cases hj : j=k
    · subst j
      simp
    · have hn : -j ≠ -k := by omega
      simp [Ne.symm hj,Ne.symm hn]
  have he := clm_conjugation_of_real_on_fixed_form periodOneHminusConjugation
    periodOneHminusConjugation_involutive L
    (fun v hv => hL v ((isRealPeriodOneHminusOne_iff_conjugation_fixed v).mpr hv)) (e (-k))
  rw [hJ] at he
  simpa only [hminusCotangentCLM_apply,neg_neg,e] using he

theorem gardnerHamiltonianDirection_real_of_real_form (L : PeriodOneHminusOne →L[ℂ] ℂ)
    (hL : ∀ v, IsRealPeriodOneHminusOne v → (L v).im=0) :
    IsRealPeriodOneHminusOne (gardnerHamiltonianDirection L) := by
  intro k
  change (gardnerDerivative (hminusCotangentCLM L)).val (-k) =
    conj ((gardnerDerivative (hminusCotangentCLM L)).val k)
  rw [gardnerDerivative_apply,gardnerDerivative_apply]
  rw [hminusCotangentCLM_real_of_real_form L hL k]
  simp only [map_mul,conj_ofReal,conj_I,map_intCast,Int.cast_neg,map_ofNat]
  ring

theorem gardnerCotangentBivector_real_of_real_form
    (L M : PeriodOneHminusOne →L[ℂ] ℂ)
    (hL : ∀ v, IsRealPeriodOneHminusOne v → (L v).im=0)
    (hM : ∀ v, IsRealPeriodOneHminusOne v → (M v).im=0) :
    (gardnerCotangentBivector L M).im=0 := by
  rw [← apply_gardnerHamiltonianDirection]
  exact hL _ (gardnerHamiltonianDirection_real_of_real_form M hM)

theorem gardnerHamiltonianVector_real_of_eventually_real (F : PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hF : AnalyticAt ℂ F q)
    (hreal : ∀ᶠ p in 𝓝 q, IsRealPeriodOneHminusOne p → (F p).im=0) :
    IsRealPeriodOneHminusOne (gardnerHamiltonianVector F q) :=
  gardnerHamiltonianDirection_real_of_real_form _ (fderiv_real_on_physical_real_germ F q hq hF hreal)

theorem hminusGardnerBracket_real_of_eventually_real (F G : PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q)
    (hFr : ∀ᶠ p in 𝓝 q, IsRealPeriodOneHminusOne p → (F p).im=0)
    (hGr : ∀ᶠ p in 𝓝 q, IsRealPeriodOneHminusOne p → (G p).im=0) :
    (hminusGardnerBracket F G q).im=0 :=
  gardnerCotangentBivector_real_of_real_form _ _
    (fderiv_real_on_physical_real_germ F q hq hF hFr) (fderiv_real_on_physical_real_germ G q hq hG hGr)

end NLS.Poisson
