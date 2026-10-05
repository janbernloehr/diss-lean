import NLS.ZakharovShabat.SourcePrimitivePowerPositive
import NLS.ZakharovShabat.SourceFullAbelianUniformGapBound

/-! # Real-source gap-size bounds for primitive-power moments

A uniform bound for the arcosh profile gives the expected additional
factor of the gap width. The established boundary bounds make this
locally uniform in real sources and uniform in distant indices.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

theorem real_moment_norm_eq_re (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ) :
    ‖A.moment n m φ.val‖ = (A.moment n m φ.val).re := by
  obtain ⟨hpos,him⟩ := A.real_moment_nonneg φ n m
  have he : ((A.moment n m φ.val).re:ℂ) = A.moment n m φ.val :=
    Complex.ext rfl (by simpa only [ofReal_im] using him.symm)
  exact (congrArg norm he.symm).trans (Complex.norm_of_nonneg hpos)

/-- A profile bound produces one extra power of the gap width. -/
theorem real_odd_moment_norm_le (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ θ ∈ Icc (0:ℝ) Real.pi, sourceRealGapCosineProfile hp hp1 φ.val n θ ≤ B) :
    ‖A.moment n (2*m+1) φ.val‖ ≤
      ‖canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n‖ * B^(2*m+1) := by
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · rw [A.moment_of_collapsed φ.val (A.realType_subset_domain φ.property) n hgap (2*m+1),hgap]
    simp
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 n φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  have hwidth : 0 ≤ (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re := by
    simpa only [canonicalPeriodicGap,sub_re,sub_nonneg] using hopen.le
  have hc := Real.continuous_sin.mul ((sourceRealGapCosineProfile_continuous hp hp1 φ n).pow (2*m+1))
  have hi : (∫ θ in (0:ℝ)..Real.pi, Real.sin θ * (sourceRealGapCosineProfile hp hp1 φ.val n θ)^(2*m+1)) ≤
      Real.pi * B^(2*m+1) := by
    have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) Real.pi_pos.le (hc.intervalIntegrable _ _)
      (intervalIntegrable_const (c := B^(2*m+1))) (fun θ hθ =>
        (mul_le_mul (Real.sin_le_one θ)
          (pow_le_pow_left₀ (sourceRealGapCosineProfile_nonneg hp hp1 φ n θ) (hb θ hθ) _)
          (pow_nonneg (sourceRealGapCosineProfile_nonneg hp hp1 φ n θ) _) zero_le_one).trans_eq (one_mul _))
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,Pi.mul_apply,Pi.pow_apply] using! h
  rw [A.real_moment_norm_eq_re φ n (2*m+1),A.real_odd_moment_eq_cosineIntegral φ n m,ofReal_re]
  calc
    _ ≤ (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re / Real.pi *
        (Real.pi * B^(2*m+1)) := mul_le_mul_of_nonneg_left hi (div_nonneg hwidth Real.pi_pos.le)
    _ = (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re * B^(2*m+1) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (pow_nonneg hB _)

/-- The real-source part of Lemma 21.1(iii), with one neighborhood,
cutoff and positive constant for every natural order and distant index. -/
theorem exists_real_local_uniform_power_bound (φ : realTypeSourceSubmodule p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ ∃ K : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ ψ : realTypeSourceSubmodule p, ψ.val ∈ U → ∀ n : ℤ, K ≤ n.natAbs → ∀ m : ℕ,
        ‖A.moment n m ψ.val‖ ≤ B^m *
          ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n‖^(m+1) := by
  obtain ⟨V,_,_,hlocal⟩ := exists_sourceFullAbelian_local_uniform_gap_bound hp hp1
  obtain ⟨C,U,hU,hφU,hUC,K,B,hB,hb⟩ := hlocal φ
  refine ⟨U,hU,hφU,K,B,hB,?_⟩
  intro ψ hψ n hn m
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n = 0
  · rw [A.moment_of_collapsed ψ.val (A.realType_subset_domain ψ.property) n hgap m,norm_zero]
    exact mul_nonneg (pow_nonneg hB.le _) (pow_nonneg (norm_nonneg _) _)
  obtain ⟨k,hk | hk⟩ := Nat.even_or_odd' m
  · rw [hk,A.moment_even ψ.val (A.realType_subset_domain ψ.property) n k,norm_zero]
    positivity
  · rw [hk]
    have hprofile (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) :
        sourceRealGapCosineProfile hp hp1 ψ.val n θ ≤
          B * ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n‖ := by
      have h := (hb ψ.val hψ n hn θ hθ true).1
      rw [C.gapBoundary_eq_realCosineProfile n ψ (hUC hψ) hgap θ hθ,
        Complex.norm_of_nonneg (sourceRealGapCosineProfile_nonneg hp hp1 ψ n θ)] at h
      exact h.trans_eq (congrArg (fun z : ℂ => B * ‖z‖)
        (sourcePeriodicGapDisplacement_apply hp hp1 ψ.val n))
    calc
      _ ≤ ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n‖ *
          (B * ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n‖)^(2*k+1) :=
        A.real_odd_moment_norm_le ψ n k _ (mul_nonneg hB.le (norm_nonneg _)) hprofile
      _ = _ := by rw [mul_pow,pow_succ]; ring

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas
