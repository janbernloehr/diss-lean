import NLS.SequenceSpaces.PeriodOneMiuraFrechetDerivative
import NLS.SequenceSpaces.PeriodOneRealMiuraProperness
import NLS.ComplexAnalysis.AnalyticInverseBetweenSpaces
import NLS.ComplexAnalysis.RealInverseNeighborhoodAt

/-! # Actual real-preserving local inverse of a bijective full Miura derivative -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS

theorem exists_real_periodOneMiura_inverse_of_bijective (u : PeriodOneRealL2)
    (hb : Function.Bijective (periodOneMiuraFrechetDerivative u.val)) :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ periodOneMiura u.val ∈ W ∧
      ∃ g : PeriodOneHminusOne → Coeff 2, AnalyticOnNhd ℂ g W ∧
        g (periodOneMiura u.val) = u.val ∧ ∀ q ∈ W,
          periodOneMiura (g q) = q ∧
          (IsRealPeriodOneHminusOne q → ∀ j : ℤ, g q (-j) = conj (g q j)) := by
  let e := ContinuousLinearEquiv.ofBijective (periodOneMiuraFrechetDerivative u.val)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hd : HasStrictFDerivAt periodOneMiura e.toContinuousLinearMap u.val := by
    change HasStrictFDerivAt periodOneMiura (periodOneMiuraFrechetDerivative u.val) u.val
    rw [←(hasFDerivAt_periodOneMiura u.val).fderiv]
    exact (analyticAt_periodOneMiura u.val).hasStrictFDerivAt
  obtain ⟨V,W,hV,hW,huV,huW,_hsub,_himage,hbij,g,_hFa,hga,hleft,hright⟩ :=
    NLS.ComplexAnalysis.exists_analytic_inverse_between_open_sets isOpen_univ
      (fun v _ => analyticAt_periodOneMiura v) (mem_univ u.val) e hd
  have hJ : Isometry periodOneL2Conjugation := by
    apply Isometry.of_dist_eq
    intro a b
    rw [dist_eq_norm,dist_eq_norm,←periodOneL2Conjugation_sub,norm_periodOneL2Conjugation]
  obtain ⟨U,hU,huU,hUW,hreal⟩ := NLS.ComplexAnalysis.exists_fixed_inverse_neighborhood_at
    periodOneMiura g periodOneL2Conjugation periodOneHminusConjugation hJ
    V W hV hW u.val huV ((periodOneL2Conjugation_fixed_iff _).mpr u.property) huW
    hga.continuousOn hbij.injOn hleft hright (fun v _ => (periodOneMiura_conjugation v).symm)
  refine ⟨U,hU,huU,g,hga.mono hUW,hleft _ huV,?_⟩
  intro q hq
  refine ⟨(hright q (hUW hq)).2,?_⟩
  intro hqr
  exact (periodOneL2Conjugation_fixed_iff _).mp
    (hreal q hq ((periodOneHminusConjugation_fixed_iff _).mpr hqr))

end NLS
