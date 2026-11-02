import NLS.KdV.ClassicalNormalizedProductQuotient
import NLS.SequenceSpaces.PositiveOddMultiplier
import NLS.ZakharovShabat.PairedEnergyResolventExterior

/-! # Large-energy asymptotics of the actual normalized resolvent

The two-weight coefficient vector provides a genuine odd Hilbert direction.
Pairing its frequency resolvent yields the exact energy remainder.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

def classicalHillNormalizedLeadingCoefficient
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) : ℂ :=
  (n : ℂ)⁻¹*lp.tsumCLM ℂ ℤ ℂ (classicalHillNormalizedResidues Q n q)

theorem classicalHillNormalizedLeadingCoefficient_analytic
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (V : Set (NLS.LinearVolterra.Curve ℂ)) (hQa : AnalyticOnNhd ℂ Q V) (n : ℕ+) :
    AnalyticOnNhd ℂ (classicalHillNormalizedLeadingCoefficient Q n) V := by
  intro q hq
  exact analyticAt_const.mul (((lp.tsumCLM ℂ ℤ ℂ).analyticAt _).comp
    (f := classicalHillNormalizedResidues Q n) (classicalHillNormalizedResidues_analytic Q V hQa n q hq))

theorem classicalHillNormalizedLeadingCoefficient_eq
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : NLS.LinearVolterra.Curve ℂ)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m) (n : ℕ+) :
    classicalHillNormalizedLeadingCoefficient Q n q =
      (n : ℂ)⁻¹*∑' k : ℕ+, (k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ) := by
  change (n : ℂ)⁻¹*(∑' j : ℤ, classicalHillNormalizedResidues Q n q j) = _
  rw [tsum_eq_positive_of_nonpositive_zero _ (classicalHillNormalizedResidues_nonpositive Q n q)]
  simp only [classicalHillNormalizedResidues_positive R Q q hcompat n]

theorem classicalHillNormalizedLeadingCoefficient_free
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (n : ℕ+) :
    classicalHillNormalizedLeadingCoefficient Q n 0 = 1 := by
  change (n : ℂ)⁻¹*(∑' j : ℤ, NLS.Coeff.positiveReciprocalHilbert j*
    ((n : ℂ)^2*(Q 0 (lp.single 2 (n : ℤ) 1)) j)) = 1
  rw [hQ0,ContinuousLinearMap.id_apply,tsum_eq_single (n : ℤ)]
  · have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
    simp only [NLS.Coeff.positiveReciprocalHilbert_apply,if_pos hn,Int.cast_natCast,
      lp.single_apply,Pi.single_apply,ite_true,mul_one]
    field_simp
  · intro j hj
    simp only [lp.single_apply,Pi.single_apply,if_neg hj,mul_zero]

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem critical_energy_norm_upper (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    ‖classicalHillUniformCriticalPoint N k q‖ ≤ 4*Real.pi^2*(k : ℝ)^2 := by
  have hm : classicalHillCriticalFrequency N k q ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) :=
    mem_closedBall_iff_norm.mpr ((D.critical_close k q hq).le.trans (by linarith [Real.pi_pos]))
  have hb := norm_le_of_positiveFrequencyDisc k _ hm
  have he : ‖classicalHillUniformCriticalPoint N k q‖ = ‖classicalHillCriticalFrequency N k q‖^2 := by
    rw [classicalHillCriticalFrequency,← norm_pow,sq_sqrt]
  rw [he]
  have hn : 0 ≤ (k : ℝ) := by positivity
  have hle : ‖classicalHillCriticalFrequency N k q‖ ≤ 2*Real.pi*(k : ℝ) := by nlinarith [Real.pi_pos]
  nlinarith [norm_nonneg (classicalHillCriticalFrequency N k q)]

theorem critical_direction_symbol_bound (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (sigma : ℂ) :
    ∃ C : ℝ, ∀ k : ℕ+,
      ‖-(classicalHillUniformCriticalPoint N k q-sigma)/(2*(k : ℂ)*classicalHillCriticalFrequency N k q)‖ ≤ C := by
  refine ⟨(4*Real.pi^2+‖sigma‖)/Real.pi,?_⟩
  intro k
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.pos
  have hnum : ‖classicalHillUniformCriticalPoint N k q-sigma‖ ≤
      (4*Real.pi^2+‖sigma‖)*(k : ℝ)^2 := by
    have hb := norm_sub_le (classicalHillUniformCriticalPoint N k q) sigma
    have he := D.critical_energy_norm_upper k q hq
    nlinarith [mul_nonneg (norm_nonneg sigma) (show 0 ≤ (k : ℝ)^2-1 by nlinarith)]
  have hden : Real.pi*(k : ℝ)^2 ≤ ‖2*(k : ℂ)*classicalHillCriticalFrequency N k q‖ := by
    rw [norm_mul,norm_mul,Complex.norm_natCast,Complex.norm_ofNat]
    have hl := D.critical_frequency_norm_lower k q hq
    nlinarith [mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2*(k : ℝ))]
  rw [norm_div,norm_neg]
  apply (div_le_iff₀ ((by positivity : 0 < Real.pi*(k : ℝ)^2).trans_le hden)).mpr
  have hC : 0 ≤ (4*Real.pi^2+‖sigma‖)/Real.pi := by positivity
  have hh := mul_le_mul_of_nonneg_left hden hC
  have hid : ((4*Real.pi^2+‖sigma‖)/Real.pi)*(Real.pi*(k : ℝ)^2) =
      (4*Real.pi^2+‖sigma‖)*(k : ℝ)^2 := by field_simp
  rw [hid] at hh
  exact hnum.trans hh

/-- The literal two-weight inverse column constructs the frequency
resolvent direction needed for the energy remainder, with no assumed l2 data. -/
theorem exists_normalized_energy_resolvent_direction
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m)
    (n : ℕ+) (sigma : ℂ) :
    ∃ h : NLS.Coeff 2, h 0 = 0 ∧ (∀ k : ℕ+, h (-(k : ℤ)) = -h (k : ℤ)) ∧
      ∀ k : ℕ+, h (k : ℤ) =
        -((k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ))*
          (classicalHillUniformCriticalPoint N k q-sigma)/(2*classicalHillCriticalFrequency N k q) := by
  let d (k : ℕ+) : ℂ := -(classicalHillUniformCriticalPoint N k q-sigma)/
    (2*(k : ℂ)*classicalHillCriticalFrequency N k q)
  let v : NLS.Coeff 2 := (n : ℂ)^2 • Q q (lp.single 2 (n : ℤ) 1)
  obtain ⟨h,hh0,hhneg,hhpos⟩ := NLS.Coeff.exists_oddExtension_of_bounded_positive_multiplier
    d (D.critical_direction_symbol_bound q hq sigma) v
  refine ⟨h,hh0,hhneg,?_⟩
  intro k
  have hkp : (0 : ℤ) < k := by exact_mod_cast k.pos
  have hnp : (0 : ℤ) < n := by exact_mod_cast n.pos
  have he := hcompat (k : ℤ) (n : ℤ)
  simp only [NLS.Coeff.positiveIndexWeight,if_pos hkp,if_pos hnp,Int.cast_natCast] at he
  have hv : v (k : ℤ) = (k : ℂ)^2*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ) := he.symm
  rw [hhpos k,hv]
  dsimp only [d]
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hx0 := D.critical_frequency_ne_zero k q hq
  field_simp

/-- Actual two-weight normalized coefficients give the leading energy
resolvent asymptotic, uniformly on the large separated frequency exterior. -/
theorem exists_threshold_normalized_resolvent_leading
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m)
    (n : ℕ+) (sigma : ℂ) {r : ℝ} (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ K : ℝ, ∀ z : ℂ, K ≤ ‖z‖ → (∀ j : ℤ, r ≤ ‖z-(Real.pi : ℂ)*j‖) →
      (∀ k : ℕ+, z^2 ≠ classicalHillUniformCriticalPoint N k q) ∧
      ‖(z^2-sigma)*(∑' k : ℕ+, (k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ)/
          (z^2-classicalHillUniformCriticalPoint N k q))-
        (∑' k : ℕ+, (k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ))‖ ≤ eps := by
  obtain ⟨h,hh0,hhneg,hhpos⟩ := D.exists_normalized_energy_resolvent_direction R Q q hq hcompat n sigma
  have hneg (k : ℕ+) : classicalHillSignedCritical N q (-(k : ℤ)) =
      -classicalHillSignedCritical N q (k : ℤ) := by
    rw [classicalHillSignedCritical_negative,classicalHillSignedCritical_positive]
  have hrho (k : ℕ+) : classicalHillSignedCritical N q (k : ℤ) ≠ 0 := by
    simpa only [classicalHillSignedCritical_positive] using! D.critical_frequency_ne_zero k q hq
  have hhs (k : ℕ+) : h (k : ℤ) =
      -((k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ))*
      ((classicalHillSignedCritical N q (k : ℤ))^2-sigma)/(2*classicalHillSignedCritical N q (k : ℤ)) := by
    simpa only [classicalHillSignedCritical_positive,sq_sqrt] using! hhpos k
  obtain ⟨K,hK⟩ := exists_threshold_pairedEnergyResolvent_small
    (classicalHillSignedCritical N q) (D.signedCritical_product q hq).2.1 h
    (fun k : ℕ+ => (k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ)) sigma
    hneg hrho hh0 hhneg hhs hr hrpi heps
  refine ⟨K,?_⟩
  intro z hz hsep
  have hb := hK z hz hsep
  simp only [classicalHillSignedCritical_positive,sq_sqrt] at hb
  refine ⟨hb.1,?_⟩
  have hc := (summable_norm_classicalHillNormalizedResidues_positive R Q q hcompat n).of_norm
  have hs := (D.summable_norm_normalized_resolvent R Q q hq hcompat n (z^2)).of_norm
  have he : (z^2-sigma)*(∑' k : ℕ+, (k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ)/
      (z^2-classicalHillUniformCriticalPoint N k q))-
      (∑' k : ℕ+, (k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ)) =
      ∑' k : ℕ+, ((k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ))*
        (classicalHillUniformCriticalPoint N k q-sigma)/(z^2-classicalHillUniformCriticalPoint N k q) := by
    rw [← tsum_mul_left,← (hs.mul_left (z^2-sigma)).tsum_sub hc]
    apply tsum_congr
    intro k
    have hd := sub_ne_zero.mpr (hb.1 k)
    field_simp
    ring
  rw [he]
  exact hb.2.2

/-- The actual energy resolvent has its leading coefficient along every
separated escaping frequency path. -/
theorem tendsto_normalized_resolvent_leading_of_separated
    {T : Type*} {l : Filter T}
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m)
    (n : ℕ+) (sigma : ℂ) (z : T → ℂ) (hz : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (hsep : ∀ i (j : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*j‖) :
    Tendsto (fun i => (z i^2-sigma)*(∑' k : ℕ+, (k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ)/
      (z i^2-classicalHillUniformCriticalPoint N k q))) l
      (𝓝 (∑' k : ℕ+, (k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ))) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨K,hK⟩ := D.exists_threshold_normalized_resolvent_leading R Q q hq hcompat n sigma hr hrpi (half_pos heps)
  filter_upwards [hz.eventually_ge_atTop K] with i hi
  rw [dist_eq_norm]
  exact (hK (z i) hi (hsep i)).2.trans_lt (half_lt_self heps)

end ClassicalAllContourPeriodData
end NLS.KdV
