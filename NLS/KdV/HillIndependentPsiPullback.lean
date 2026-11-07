import NLS.KdV.HillIndependentProductRestoration
import NLS.KdV.HillProductFixedPeriods
import NLS.KdV.HillFreePeriodJacobian

/-! The literal independent Hill energy product is a quadratic
pullback of the single-deleted frequency product with an EXPLICIT
factor. The filled identity includes collisions and both restored
frequencies; the quotient is used only where its denominator is nonzero. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillEnergyProduct_independent_candidate_filled (n : ℕ+)
    (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    (hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z)*(2*z*hillEnergySequenceProduct n (z^2-c,d)) =
      ((Real.pi:ℂ)*(n:ℕ))^2*
        sourcePsiCandidate ((n:ℕ):ℤ) (z,hillIndependentFrequencyDisplacement (c,d)) := by
  let a := hillIndependentFrequencyDisplacement (c,d)
  let β := hillIndependentFrequency (c,d) ((n:ℕ):ℤ)
  let A : ℂ := ((Real.pi:ℂ)*(n:ℕ))^2
  let P : ℂ → ℂ := fun w => hillEnergySequenceProduct n (w^2-c,d)
  have hP : Continuous P :=
    (continuous_iff_continuousAt.mpr (fun t => (analyticAt_hillEnergySequenceProduct n t).continuousAt)).comp
      (((continuous_id.pow 2).sub continuous_const).prodMk continuous_const)
  have hC : Continuous (fun w : ℂ => sourcePsiCandidate ((n:ℕ):ℤ) (w,a)) :=
    (continuousOn_univ.mp (analyticOnNhd_sourcePsiCandidate (by norm_num) (by norm_num) ((n:ℕ):ℤ)).continuousOn).comp
      (continuous_id.prodMk continuous_const)
  have hA : A ≠ 0 := pow_ne_zero 2 (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (by exact_mod_cast n.ne_zero))
  have he : (fun w : ℂ => (β+w)*(2*w*P w)) =
      (fun w : ℂ => A*sourcePsiCandidate ((n:ℕ):ℤ) (w,a)) := by
    apply Continuous.ext_on ((Set.to_countable {β}).dense_compl ℂ)
      ((continuous_const.add continuous_id).mul ((continuous_const.mul continuous_id).mul hP))
      (continuous_const.mul hC)
    intro w hw
    have hwβ : w ≠ β := by simpa only [mem_compl_iff,mem_singleton_iff] using hw
    have hβw : β-w ≠ 0 := sub_ne_zero.mpr (Ne.symm hwβ)
    apply mul_left_cancel₀ hβw
    have h := jointSingleSpectralProduct_independent_Hill_restore n c d w
    rw [jointSingleSpectralProduct_eq_deleted (by norm_num) (by norm_num) ((n:ℕ):ℤ)] at h
    change 2*(β-w)*jointDeletedSingleSpectralProduct ((n:ℕ):ℤ) (w,a) =
      -2*w*((hillEnergySequenceZero n d+c-w^2)/A)*P w at h
    have hsq : hillEnergySequenceZero n d+c-w^2 = (β-w)*(β+w) := by
      rw [← hillIndependentFrequency_positive_sq (c,d) n]
      dsimp only [β]
      ring
    rw [hsq] at h
    change (β-w)*((β+w)*(2*w*P w)) =
      (β-w)*(A*(-2*jointDeletedSingleSpectralProduct ((n:ℕ):ℤ) (w,a)))
    field_simp [hA] at h
    linear_combination 2*(β-w)*h
  exact congrFun he z

theorem hillEnergyProduct_independent_candidate_quotient (n : ℕ+)
    (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ)
    (hden : hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z ≠ 0) :
    2*z*hillEnergySequenceProduct n (z^2-c,d) =
      (((Real.pi:ℂ)*(n:ℕ))^2*sourcePsiCandidate ((n:ℕ):ℤ)
        (z,hillIndependentFrequencyDisplacement (c,d)))/(hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z) := by
  apply (eq_div_iff hden).mpr
  rw [mul_comm]
  exact hillEnergyProduct_independent_candidate_filled n c d z

theorem hillWeightedProductIntegrand_independent_candidate (n m : ℕ+)
    (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) (ψ : CoeffPair 2) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) ψ)
    (hden : hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z ≠ 0) :
    (2*Real.pi:ℂ)⁻¹*hillPeriodEquationWeight n m*hillEnergyProductPeriodIntegrand n c ψ (z,d) =
      ((Real.pi:ℂ)^2*(((n:ℕ):ℂ)+((m:ℕ):ℂ))/(hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z))*
      ((((n:ℕ):ℂ)-((m:ℕ):ℂ))*sourcePsiCandidate ((n:ℕ):ℤ)
        (z,hillIndependentFrequencyDisplacement (c,d))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z) := by
  unfold hillEnergyProductPeriodIntegrand
  dsimp only
  rw [hillEnergyProduct_independent_candidate_quotient n c d z hden]
  have hroot := sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) ψ z hz
  have hn : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold hillPeriodEquationWeight
  field_simp [hroot,hden,hn,hpi]
  ring

end NLS.KdV
