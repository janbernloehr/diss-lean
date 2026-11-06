import NLS.KdV.HillDirichletEnergyDisplacement
import NLS.KdV.HillDirichletGreenReconstruction

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis NLS.Fourier NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



/-- The actual rough scalar Hill flow inherits the normalized Volterra
position estimate by finite Fourier approximation in the original topology. -/
theorem hillL2FrequencyStateCurve_position_bound_small (q : Coeff 2) (z : ℂ) (hz : z ≠ 0)
    (H : ℝ) (hH : |z.im| ≤ H) (hsmall : 4*Real.exp H*‖q‖ ≤ ‖z‖)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖(hillL2FrequencyStateCurve q z v t).1‖ ≤ 2*Real.exp H*(‖v.1‖+‖v.2‖/‖z‖) := by
  have hfinite (a : ℤ →₀ ℂ) (ha : ‖Coeff.ofFinsupp (p := 2) a‖ ≤ ‖q‖) :
      ‖(hillL2FrequencyStateCurve (Coeff.ofFinsupp (p := 2) a) z v t).1‖ ≤
        2*Real.exp H*(‖v.1‖+‖v.2‖/‖z‖) := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) = Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    have hmass : classicalHillPotentialMass (hillUnitPotentialCurve Q) ≤ 2*‖q‖ := by
      apply (classicalHillPotentialMass_continuous_bound Q).trans
      rw [hq]
      exact mul_le_mul_of_nonneg_left ha (by norm_num)
    have hs : Real.exp H/‖z‖*classicalHillPotentialMass (hillUnitPotentialCurve Q) ≤ 1/2 := by
      apply (mul_le_mul_of_nonneg_left hmass (by positivity)).trans
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
      nlinarith [hsmall]
    rw [← hq,hillL2FrequencyStateCurve_eq_classical]
    exact classicalHillFlow_position_bound_small (hillUnitPotentialCurve Q) z hz H hH hs v t
  have hc : Continuous (fun a : Coeff 2 => ‖(hillL2FrequencyStateCurve a z v t).1‖) :=
    ((continuous_eval_const t).comp (continuous_hillL2FrequencyStateCurve z v)).fst.norm
  apply le_of_tendsto ((hc.tendsto q).comp (Coeff.tendsto_truncate (by simp) q))
  apply Filter.Eventually.of_forall
  intro s
  have ht : Coeff.ofFinsupp (p := 2) (Coeff.finiteRestriction s q) = Coeff.truncate s q :=
    Coeff.ofFinsupp_finiteRestriction s q
  change ‖(hillL2FrequencyStateCurve (Coeff.truncate s q) z v t).1‖ ≤ _
  rw [← ht]
  apply hfinite
  rw [ht]
  exact Coeff.norm_truncate_le (by norm_num) s q

/-- Original normalized Dirichlet positions have the genuine inverse
frequency gain, with their initial derivative fixed to one. -/
theorem hillL2DirichletPosition_bound_small (q : Coeff 2) (E : ℂ) (hz : Complex.sqrt E ≠ 0)
    (H : ℝ) (hH : |(Complex.sqrt E).im| ≤ H)
    (hsmall : 4*Real.exp H*‖q‖ ≤ ‖Complex.sqrt E‖)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖hillL2DirichletPosition q E x‖ ≤ 2*Real.exp H/‖Complex.sqrt E‖ := by
  change ‖(extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) x).1‖ ≤ _
  rw [show x=(⟨x,hx⟩ : Icc (0 : ℝ) 1).val from rfl,extend_coe]
  simpa only [norm_zero,norm_one,zero_add,mul_one_div] using
    hillL2FrequencyStateCurve_position_bound_small q (Complex.sqrt E) hz H hH hsmall (0,1) ⟨x,hx⟩

end NLS.KdV
