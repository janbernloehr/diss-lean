import NLS.Fourier.RudinShapiro
import NLS.Fourier.PeriodicL1Uniqueness

/-!
# Remark A.6: the L¹ Fourier transform is not onto c₀

The actual L¹ Fourier map is injective and has dense range, but is not
surjective. Rudin–Shapiro polynomials have uniformly bounded Fourier
coefficients and unbounded L¹ norms. A hypothetical bounded inverse,
supplied by the open mapping theorem, contradicts these estimates.
This holds for every positive physical period with normalized Haar measure.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal ZeroAtInfty
namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]

/-- The actual L¹ class of the first Rudin–Shapiro polynomial. -/
def rudinShapiroL1 (n : ℕ) : Lp ℂ 1 (AddCircle.haarAddCircle (T := L)) :=
  ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ (rudinShapiroPair n).1

theorem norm_fourier_rudinShapiroL1_le (n : ℕ) :
    ‖circleL1Fourier (rudinShapiroL1 (L := L) n)‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro k
  change ‖circleL1Fourier (rudinShapiroL1 (L := L) n) k‖ ≤ 1
  rw [circleL1Fourier_apply]
  change ‖fourierCoeff (ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ (rudinShapiroPair n).1) k‖ ≤ 1
  rw [fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ _),(rudinShapiro_coeff_norm n k).1]
  split_ifs <;> norm_num

/-- Combining Parseval and the uniform bound forces growth of the normalized L¹ norm. -/
theorem rudinShapiroL1_lower_bound (n : ℕ) :
    (2:ℝ)^n ≤ Real.sqrt (2^(n+1)) * ‖rudinShapiroL1 (L := L) n‖ := by
  let P := (rudinShapiroPair (L := L) n).1
  have hint : Integrable (fun x => ‖P x‖^2) AddCircle.haarAddCircle :=
    (by fun_prop : Continuous (fun x => ‖P x‖^2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun x => ‖P x‖) AddCircle.haarAddCircle :=
    P.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ x, ‖P x‖^2 ∂AddCircle.haarAddCircle := (integral_sq_rudinShapiro n).symm
    _ ≤ ∫ x, Real.sqrt (2^(n+1))*‖P x‖ ∂AddCircle.haarAddCircle := by
      apply integral_mono hint (hi.const_mul _)
      intro x
      have hb := (P.norm_coe_le_norm x).trans (norm_rudinShapiro_le n)
      nlinarith [norm_nonneg (P x)]
    _ = _ := by
      rw [integral_const_mul,L1.norm_eq_integral_norm]
      congr 1
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) AddCircle.haarAddCircle P] with x hx
      exact congrArg norm hx.symm

/-- The non-surjectivity assertion of Remark A.6, by the open mapping theorem. -/
theorem circleL1Fourier_not_surjective : ¬Function.Surjective (circleL1Fourier (L := L)) := by
  intro hsurj
  let e := ContinuousLinearEquiv.ofBijective (circleL1Fourier (L := L))
    (LinearMap.ker_eq_bot.mpr circleL1Fourier_injective) (LinearMap.range_eq_top.mpr hsurj)
  let C := ‖e.symm.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg _
  have hb (f : Lp ℂ 1 (AddCircle.haarAddCircle (T := L))) : ‖f‖ ≤ C*‖circleL1Fourier f‖ := by
    have h := e.symm.toContinuousLinearMap.le_opNorm (e f)
    simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply,e,
      ContinuousLinearEquiv.coeFn_ofBijective,ContinuousLinearEquiv.ofBijective_symm_apply_apply,C] using h
  have hbound (n : ℕ) : (2:ℝ)^n ≤ 2*C^2 := by
    have hl : ‖rudinShapiroL1 (L := L) n‖ ≤ C :=
      (hb _).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_fourier_rudinShapiroL1_le n) hC)
    have hh := (rudinShapiroL1_lower_bound (L := L) n).trans
      (mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg _))
    have hN : (0:ℝ) < 2^n := by positivity
    have hs := mul_self_le_mul_self (le_of_lt hN) hh
    have hroot : (Real.sqrt ((2:ℝ)^(n+1)))^2 = 2^(n+1) := Real.sq_sqrt (by positivity)
    have hmul : (2:ℝ)^n * 2^n ≤ 2^n * (2*C^2) := by
      nlinarith only [hs,hroot,show (2:ℝ)^(n+1) = 2^n*2 by rw [pow_succ]]
    exact (mul_le_mul_iff_right₀ hN).mp hmul
  obtain ⟨n,hn⟩ := exists_nat_gt (2*C^2)
  have hn := hn.trans_le (by exact_mod_cast (show n ≤ 2^n from Nat.le_of_lt Nat.lt_two_pow_self) : (n:ℝ) ≤ 2^n)
  exact (not_lt_of_ge (hbound n)) hn

/-- A c₀ sequence which is not the Fourier sequence of any integrable function. -/
theorem exists_c0_not_fourierCoeff : ∃ a : C₀(ℤ,ℂ),
    ¬∃ f : AddCircle L → ℂ, Integrable f AddCircle.haarAddCircle ∧ fourierCoeff f = a := by
  have h := circleL1Fourier_not_surjective (L := L)
  rw [Function.Surjective] at h
  push Not at h
  obtain ⟨a,ha⟩ := h
  refine ⟨a,?_⟩
  rintro ⟨f,hf,he⟩
  apply ha ((memLp_one_iff_integrable.mpr hf).toLp f)
  ext n
  rw [circleL1Fourier_apply,fourierCoeff_congr_ae (memLp_one_iff_integrable.mpr hf).coeFn_toLp,he]

/-- The counterexample as a raw integer sequence with two-sided decay. -/
theorem exists_vanishing_not_fourierCoeff : ∃ a : ℤ → ℂ,
    Tendsto a cofinite (𝓝 0) ∧
      ¬∃ f : AddCircle L → ℂ, Integrable f AddCircle.haarAddCircle ∧ fourierCoeff f = a := by
  obtain ⟨a,ha⟩ := exists_c0_not_fourierCoeff (L := L)
  refine ⟨a,?_,ha⟩
  simpa only [Filter.cocompact_eq_cofinite] using (zero_at_infty a)

/-- Every polynomial in the family has Fourier c₀ norm exactly one. -/
theorem norm_fourier_rudinShapiroL1 (n : ℕ) :
    ‖circleL1Fourier (rudinShapiroL1 (L := L) n)‖ = 1 := by
  apply le_antisymm (norm_fourier_rudinShapiroL1_le n)
  have h := (circleL1Fourier (rudinShapiroL1 (L := L) n)).toBCF.norm_coe_le_norm 0
  change ‖circleL1Fourier (rudinShapiroL1 (L := L) n) 0‖ ≤ _ at h
  rw [circleL1Fourier_apply] at h
  change ‖fourierCoeff (ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ (rudinShapiroPair n).1) 0‖ ≤ _ at h
  rw [fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ _),(rudinShapiro_coeff_norm n 0).1,
    if_pos (by constructor; rfl; positivity)] at h
  exact h

/-- The dense Fourier image is a proper, nonclosed subspace of c₀. -/
theorem not_isClosed_range_circleL1Fourier :
    ¬IsClosed (Set.range (circleL1Fourier (L := L))) := by
  intro hc
  apply circleL1Fourier_not_surjective (L := L)
  apply Set.range_eq_univ.mp
  rw [← hc.closure_eq]
  exact denseRange_circleL1Fourier.closure_range

namespace PeriodicFourierLebesgue
open SmoothPeriodicTest

/-- An original FL∞ distribution with vanishing coefficients and no L¹ representative. -/
theorem exists_vanishing_not_ofCircleL1 :
    ∃ u : PeriodicFourierLebesgue L Weight.one ⊤,
      Tendsto (fun n : ℤ => u.val (mode (-n))) cofinite (𝓝 0) ∧
      ¬∃ (f : AddCircle L → ℂ) (hf : Integrable f AddCircle.haarAddCircle),
        Distribution.ofCircleL1 f hf = u.val := by
  obtain ⟨a,ha⟩ := exists_c0_not_fourierCoeff (L := L)
  let b : Coeff ⊤ := ⟨(fun n => a n),memℓp_infty ⟨‖a‖,by
    rintro y ⟨n,rfl⟩
    exact a.toBCF.norm_coe_le_norm n⟩⟩
  let u := (unweightedCoefficients (L := L) ⊤).symm b
  have hc (n : ℤ) : u.val (mode (-n)) = a n := by
    rw [← unweightedCoefficients_apply]
    change unweightedCoefficients ⊤ ((unweightedCoefficients ⊤).symm b) n = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  refine ⟨u,?_,?_⟩
  · simpa only [hc,Filter.cocompact_eq_cofinite] using (zero_at_infty a)
  · rintro ⟨f,hf,he⟩
    apply ha
    refine ⟨f,hf,funext fun n => ?_⟩
    rw [← Distribution.ofCircleL1_coefficient f hf n,he,hc]

/-- Even FL∞ norm convergence of Fourier truncations does not imply L¹ representability. -/
theorem exists_norm_convergent_not_ofCircleL1 :
    ∃ u : PeriodicFourierLebesgue L Weight.one ⊤,
      Tendsto (fun S : Finset ℤ => truncate Weight.one ⊤ Weight.hasTemperedInverse_one S u) atTop (𝓝 u) ∧
      ¬∃ (f : AddCircle L → ℂ) (hf : Integrable f AddCircle.haarAddCircle),
        Distribution.ofCircleL1 f hf = u.val := by
  obtain ⟨u,hu,hn⟩ := exists_vanishing_not_ofCircleL1 (L := L)
  refine ⟨u,?_,hn⟩
  apply (tendsto_truncate_top_iff Weight.one Weight.hasTemperedInverse_one _).mpr
  intro ε hε
  have h := Metric.tendsto_nhds.mp hu ε hε
  have hfin : {n : ℤ | ¬ ‖u.val (mode (-n))‖ < ε}.Finite := by
    simpa only [dist_zero_right,Filter.eventually_cofinite] using h
  refine ⟨hfin.toFinset,fun n hn => ?_⟩
  have hn' : ‖u.val (mode (-n))‖ < ε := by
    simpa only [Set.Finite.mem_toFinset,mem_ofPred_eq,not_not] using hn
  simpa only [Weight.one_apply,Complex.ofReal_one,one_mul] using hn'.le

end PeriodicFourierLebesgue
end NLS.Fourier
