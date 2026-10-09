import NLS.ZakharovShabat.ClassicalHermitianFourierDecay

/-! # The full Hermitian matrix H¹ time bound in G.3 -/
noncomputable section
open Set MeasureTheory NLS.ComplexAnalysis NLS.LinearVolterra
namespace NLS.ComplexAnalysis

/-- The linear assembly map for two complex columns. -/
def hermitianColumnsCLM : ((ℂ × ℂ) × (ℂ × ℂ)) →L[ℂ] HermitianOperator :=
  ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ))).smulRight
      (hermitianMatrixUnit 0 0) +
  ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ))).smulRight
      (hermitianMatrixUnit 1 0) +
  ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ))).smulRight
      (hermitianMatrixUnit 0 1) +
  ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ))).smulRight
      (hermitianMatrixUnit 1 1)

@[simp] theorem hermitianColumnsCLM_apply (uv : (ℂ × ℂ) × (ℂ × ℂ)) :
    hermitianColumnsCLM uv = hermitianColumns uv.1 uv.2 := by
  simp [hermitianColumnsCLM,hermitianColumns_eq_matrixUnits]

/-- A common bound on the two columns bounds the genuine operator norm. -/
theorem norm_hermitianColumns_le (u v : ℂ × ℂ) (A : ℝ) (hu : ‖u‖ ≤ A) (hv : ‖v‖ ≤ A) :
    ‖hermitianColumns u v‖ ≤ 4*A := by
  have he (c : ℂ) (i j : Fin 2) : ‖c • hermitianMatrixUnit i j‖ ≤ ‖c‖ := by
    rw [norm_smul]
    simpa using mul_le_mul_of_nonneg_left (norm_hermitianMatrixUnit_le i j) (norm_nonneg c)
  rw [hermitianColumns_eq_matrixUnits]
  have h := (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (he u.1 0 0) (he u.2 1 0))) (he v.1 0 1))) (he v.2 1 1))
  exact h.trans (by linarith [(norm_fst_le u).trans hu,(norm_snd_le u).trans hu,
    (norm_fst_le v).trans hv,(norm_snd_le v).trans hv])

/-- The physical H¹ norm uses the actual time derivative and operator norms. -/
def hermitianIntervalH1Norm (F : ℝ → HermitianOperator) : ℝ :=
  Real.sqrt ((∫ t in (0 : ℝ)..1, ‖F t‖^2) + (∫ t in (0 : ℝ)..1, ‖deriv F t‖^2))

theorem hermitianIntervalH1Norm_le (F : ℝ → HermitianOperator) (hF : ContDiff ℝ 1 F)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖F t‖ ≤ A)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv F t‖ ≤ D) :
    hermitianIntervalH1Norm F ≤ A+D := by
  have hi (G : ℝ → HermitianOperator) (hG : Continuous G) (K : ℝ) (hK : 0 ≤ K)
      (h : ∀ t ∈ Icc (0 : ℝ) 1, ‖G t‖ ≤ K) : (∫ t in (0 : ℝ)..1, ‖G t‖^2) ≤ K^2 := by
    have hh := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      ((hG.norm.pow 2).intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
      (fun t ht => (sq_le_sq₀ (norm_nonneg _) hK).mpr (h t ht))
    simpa using hh
  apply (Real.sqrt_le_left (add_nonneg hA hD)).mpr
  exact (add_le_add (hi F hF.continuous A hA hb)
    (hi (deriv F) (contDiff_one_iff_deriv.mp hF).2 D hD hd)).trans (by nlinarith)

end NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- Matrix assembly preserves the actual C¹ regularity. -/
theorem contDiff_classicalHermitianRemainderOperator (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    ContDiff ℝ 1 (classicalHermitianRemainderOperator φ z) := by
  change ContDiff ℝ 1 (fun t => hermitianColumns (classicalSolutionRemainder φ z (1,0) t)
    (classicalSolutionRemainder φ z (0,1) t))
  simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars',hermitianColumnsCLM_apply] using
    (hermitianColumnsCLM.restrictScalars ℝ).contDiff.comp
      ((contDiff_classicalSolutionRemainder φ z (1,0)).prodMk
        (contDiff_classicalSolutionRemainder φ z (0,1)))

/-- The derivative of the full matrix has the actual derivatives as columns. -/
theorem deriv_classicalHermitianRemainderOperator (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    deriv (classicalHermitianRemainderOperator φ z) t =
      hermitianColumns (deriv (classicalSolutionRemainder φ z (1,0)) t)
        (deriv (classicalSolutionRemainder φ z (0,1)) t) := by
  change deriv (fun t => hermitianColumns (classicalSolutionRemainder φ z (1,0) t)
    (classicalSolutionRemainder φ z (0,1) t)) t = _
  have hu := ((contDiff_one_iff_deriv.mp (contDiff_classicalSolutionRemainder φ z (1,0))).1 t).hasDerivAt
  have hv := ((contDiff_one_iff_deriv.mp (contDiff_classicalSolutionRemainder φ z (0,1))).1 t).hasDerivAt
  simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars',hermitianColumnsCLM_apply] using
    ((hermitianColumnsCLM.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hu.prodMk hv)).deriv

/-- Uniform H¹ time control for the whole matrix in a spectral strip. -/
theorem classicalHermitianRemainder_H1_le (M H : ℝ) (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : ‖a‖ ≤ M) (z : ℂ) (hz : z ≠ 0) (hH : |z.im| ≤ H) (hz1 : 1 ≤ ‖z‖) :
    hermitianIntervalH1Norm (classicalHermitianRemainderOperator (classicalSobolevPotential a) z) ≤
      4*(classicalSobolevErrorConstant M H+classicalSobolevDerivativeConstant M H) := by
  have hC := classicalSobolevErrorConstant_nonneg M H ((norm_nonneg a).trans ha)
  have hD := classicalSobolevDerivativeConstant_nonneg M H ((norm_nonneg a).trans ha)
  have hb (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
      ‖classicalSolutionRemainder (classicalSobolevPotential a) z v t‖ ≤
        classicalSobolevErrorConstant M H*‖v‖ := by
    have h := norm_classicalSolutionRemainder_sobolev_strip_le M H a ha z hz hH v t
    have he : (4+Real.pi)*M*‖v‖/‖z‖*Real.exp (4*M+H) =
        classicalSobolevErrorConstant M H*‖v‖/‖z‖ := by unfold classicalSobolevErrorConstant; ring
    rw [he] at h
    exact h.trans (div_le_self (mul_nonneg hC (norm_nonneg _)) hz1)
  have hd (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
      ‖deriv (classicalSolutionRemainder (classicalSobolevPotential a) z v) t‖ ≤
        classicalSobolevDerivativeConstant M H*‖v‖ := by
    apply (norm_deriv_classicalSolutionRemainder_sobolev_strip_le M H a ha z hz hH v t).trans_eq
    unfold classicalSobolevDerivativeConstant
    ring
  apply (hermitianIntervalH1Norm_le _ (contDiff_classicalHermitianRemainderOperator _ _)
    (4*classicalSobolevErrorConstant M H) (4*classicalSobolevDerivativeConstant M H)
    (by positivity) (by positivity) ?_ ?_).trans_eq (by ring)
  · intro t ht
    exact norm_hermitianColumns_le _ _ _ (by simpa using hb (1,0) ⟨t,ht⟩)
      (by simpa using hb (0,1) ⟨t,ht⟩)
  · intro t ht
    rw [deriv_classicalHermitianRemainderOperator]
    exact norm_hermitianColumns_le _ _ _ (by simpa using hd (1,0) ⟨t,ht⟩)
      (by simpa using hd (0,1) ⟨t,ht⟩)

/-- The H¹ assertion of G.3, with one cutoff for each potential ball and displacement bound. -/
theorem exists_classicalHermitianRemainder_sequence_H1_bound
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ n : ℤ, N ≤ n.natAbs →
      hermitianIntervalH1Norm (classicalHermitianRemainderOperator (classicalSobolevPotential a) (ν n)) ≤
        4*(classicalSobolevErrorConstant M B+classicalSobolevDerivativeConstant M B) := by
  obtain ⟨N,hN,hcut⟩ := exists_near_free_frequency_cutoff B hB
  refine ⟨max N N₀,lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro ν hν a ha n hn
  obtain ⟨him,hz1,_⟩ := hcut n ((le_max_left N N₀).trans hn) (ν n)
    (hν n ((le_max_right N N₀).trans hn))
  exact classicalHermitianRemainder_H1_le M B a ha (ν n)
    (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hz1)) him hz1

end NLS.ZakharovShabat
