import NLS.ZakharovShabat.NLSWKBLeadingScalarIntegral
import NLS.ZakharovShabat.SobolevClassicalFreeUniform

/-! # The leading oscillatory WKB solution error

Subtracting the actual density integral gains one inverse-frequency power uniformly on original Sobolev balls and horizontal strips.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual WKB solution error equals its explicit oscillatory leading
term up to order N+1, uniformly on the original Hs ball and spectral strip. -/
theorem exists_uniform_nlsWKB_leading_oscillatory_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0:ℝ) 1,
        ‖nlsWKBVector a b N z t-
          classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z (nlsWKBVector a b N z 0) t-
          (0,-I*((2*I*z)⁻¹)^N*exp (I*z*t.val)*
            (∫ x in (0:ℝ)..t.val, nlsRiccatiDensity a b N x*exp (-2*I*z*x)))‖ ≤
            C*‖(2*I*z)⁻¹‖^(N+1) := by
  obtain ⟨D,hD,hfirst⟩ := exists_uniform_nlsWKB_leading_forced_solution_error_bound s N hs hNs R hR H
  obtain ⟨K,hK,hint⟩ := exists_uniform_nlsWKBLeadingScalar_integral_bound s N hNs R hR H
  obtain ⟨A,hA,haB⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  let B := Real.exp (A+H)
  let E := 2*classicalSobolevErrorConstant (2*R) H
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hE : 0 ≤ E := mul_nonneg (by norm_num) (classicalSobolevErrorConstant_nonneg _ _ (by positivity))
  refine ⟨D+3*B*E*K,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hzn hzH t
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let w : ℂ := (2*I*z)⁻¹
  let f := nlsWKBLeadingScalar a b N z
  have hf : Continuous f := continuous_nlsWKBLeadingScalar a b ha hb N z
  let g := classicalScalarForcing f hf
  have hΦ : ‖Φ‖ ≤ A := by
    apply (ContinuousMap.norm_le _ hA).mpr
    intro x
    apply norm_prod_le_iff.mpr
    exact ⟨haB ab hab a b ha hb hpa hpb hca hcb x,
      haB (ab.2,ab.1) (by simpa only [Prod.norm_def,max_comm] using hab)
        b a hb ha hpb hpa hcb hca x⟩
  have hsol (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (x : Icc (0:ℝ) 1) :
      ‖classicalSolution Φ z v x‖ ≤ B :=
    norm_classicalSolution_unit_strip_le A H Φ hΦ z hzH v hv x
  have herr (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (x : Icc (0:ℝ) 1) :
      ‖classicalSolution Φ z v x-classicalFreeVector z v x‖ ≤ E*‖w‖ := by
    have hh := norm_classicalSolution_sub_free_higherSobolev_le s hs R H ab hab a b
      ha.continuous hb.continuous hpa hpb hca hcb z (norm_pos_iff.mp (by linarith)) hzH v x
    apply hh.trans
    change E*‖v‖*‖w‖ ≤ _
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hE hv) (norm_nonneg _)
  have hfree (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : ‖exp (-I*z*x)‖ ≤ B :=
    (norm_exp_neg_I_mul_strip_le z H hzH x hx).trans (Real.exp_le_exp.mpr (by linarith))
  have he := norm_classicalScalarForcing_sub_free_le Φ z f hf B (E*‖w‖) hB (by positivity)
    hsol herr hfree t
  have hscalar := hint ab hab a b ha hb hpa hpb hca hcb z hzH
  have he' : ‖classicalForcedKernelSolution Φ g z t-
      (0,-I*w^N*exp (I*z*t.val)*(∫ x in (0:ℝ)..t.val, nlsRiccatiDensity a b N x*exp (-2*I*z*x)))‖ ≤
      (3*B*E*K)*‖w‖^(N+1) := by
    rw [free_integral_nlsWKBLeadingScalar] at he
    apply he.trans
    calc
      _ ≤ 3*B*(E*‖w‖)*(K*‖w‖^N) := mul_le_mul_of_nonneg_left hscalar (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have he1 := hfirst ab hab a b ha hb hpa hpb hca hcb z hzn hzH t
  let X := nlsWKBVector a b N z t-classicalSolution Φ z (nlsWKBVector a b N z 0) t
  let Y := classicalForcedKernelSolution Φ g z t
  let Z : ℂ × ℂ := (0,-I*w^N*exp (I*z*t.val)*(∫ x in (0:ℝ)..t.val, nlsRiccatiDensity a b N x*exp (-2*I*z*x)))
  change ‖X-Z‖ ≤ _
  calc
    _ = ‖(X-Y)+(Y-Z)‖ := by congr 1; abel
    _ ≤ ‖X-Y‖+‖Y-Z‖ := norm_add_le _ _
    _ ≤ D*‖w‖^(N+1)+(3*B*E*K)*‖w‖^(N+1) := add_le_add he1 he'
    _ = _ := by ring

end NLS.ZakharovShabat
