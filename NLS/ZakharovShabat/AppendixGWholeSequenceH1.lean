import NLS.ZakharovShabat.SourceLemmaG3
import NLS.ZakharovShabat.ClassicalEndpointGradientBounds

/-! # The whole-sequence H1 assertion in Appendix G.3

A coarse estimate at every complex frequency controls the finite head.
The existing uniform tail bound then gives one constant for every index
of a fixed near-free frequency sequence and every source in an H1 ball.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- A finite H1 time bound at every frequency, including zero. -/
theorem appendixG_remainder_H1_coarse_bound
    (M : ℝ) (φ : Curve (ℂ × ℂ)) (hφ : ‖φ‖ ≤ M) (z : ℂ) :
    hermitianIntervalH1Norm (classicalHermitianRemainderOperator φ z) ≤
      4*(2+2*‖z‖+M)*Real.exp (M+‖z‖) := by
  have hM : 0 ≤ M := (norm_nonneg φ).trans hφ
  let E := Real.exp (M+‖z‖)
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hs (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (t : Icc (0 : ℝ) 1) :
      ‖classicalSolution φ z v t‖ ≤ E :=
    norm_classicalSolution_unit_strip_le M ‖z‖ φ hφ z (Complex.abs_im_le_norm z) v hv t
  have hr (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (t : Icc (0 : ℝ) 1) :
      ‖classicalSolutionRemainder φ z v t‖ ≤ 2*E := by
    have he : classicalFreeVector z v t = classicalSolution 0 z v t := by
      simp [classicalSolution_free,classicalFreeVector]
    have hf := norm_classicalSolution_unit_strip_le M ‖z‖ 0 (by simpa using hM)
      z (Complex.abs_im_le_norm z) v hv t
    dsimp only [classicalSolutionRemainder]
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith [hs v hv t])
  have hd (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (t : Icc (0 : ℝ) 1) :
      ‖deriv (classicalSolutionRemainder φ z v) t‖ ≤ (2*‖z‖+M)*E := by
    apply (norm_deriv_classicalSolutionRemainder_le φ z v t).trans
    have h1 := mul_le_mul_of_nonneg_left (hr v hv t) (norm_nonneg z)
    have h2 := mul_le_mul hφ (hs v hv t) (norm_nonneg _) hM
    nlinarith
  apply (hermitianIntervalH1Norm_le _ (contDiff_classicalHermitianRemainderOperator φ z)
    (4*(2*E)) (4*((2*‖z‖+M)*E)) (by positivity) (by positivity) ?_ ?_).trans_eq
    (by dsimp [E]; ring)
  · intro t ht
    exact norm_hermitianColumns_le _ _ _
      (hr (1,0) (by simp) ⟨t,ht⟩) (hr (0,1) (by simp) ⟨t,ht⟩)
  · intro t ht
    rw [deriv_classicalHermitianRemainderOperator]
    exact norm_hermitianColumns_le _ _ _
      (hd (1,0) (by simp) ⟨t,ht⟩) (hd (0,1) (by simp) ⟨t,ht⟩)

/-- The coarse bound on the exact original periodic H1 source ball. -/
theorem appendixG_source_remainder_H1_coarse_bound
    (M : ℝ) (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M)
    (z : ℂ) :
    hermitianIntervalH1Norm (classicalHermitianRemainderOperator
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) z) ≤
      4*(2+2*‖z‖+8*M)*Real.exp (8*M+‖z‖) := by
  apply appendixG_remainder_H1_coarse_bound (8*M)
  exact (norm_classicalSobolevPotential_le _).trans
    (by have h := norm_sourceG3ClassicalCoefficients_le a; linarith)

/-- The actual operator remainder has uniform inverse-index decay at every
time, with one cutoff before both the source and the spectral sequence. -/
theorem appendixG_source_remainder_uniform_time_decay
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ ν : ℤ → ℂ,
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) →
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M →
      ∀ n : ℤ, N ≤ n.natAbs → ∀ t : Icc (0 : ℝ) 1,
        ‖classicalHermitianRemainderOperator
          (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) t‖ ≤
          4*classicalSobolevErrorConstant (2*M) B/(n.natAbs : ℝ) := by
  obtain ⟨N,hN,hcut⟩ := exists_near_free_frequency_cutoff B hB
  refine ⟨max N N₀,lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro ν hν a ha n hn t
  have hnN := (le_max_left N N₀).trans hn
  obtain ⟨him,hz1,hzn⟩ := hcut n hnN (ν n) (hν n ((le_max_right N N₀).trans hn))
  have hnpos : 0 < (n.natAbs : ℝ) := by exact_mod_cast lt_of_lt_of_le hN hnN
  have hzn' : (n.natAbs : ℝ) ≤ ‖ν n‖ := by nlinarith [Real.two_le_pi]
  have hz : ν n ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hz1)
  have ha' : ‖sourceG3ClassicalCoefficients a‖ ≤ 2*M :=
    (norm_sourceG3ClassicalCoefficients_le a).trans (by linarith)
  have hM : 0 ≤ 2*M := (norm_nonneg _).trans ha'
  have hc := classicalSobolevErrorConstant_nonneg (2*M) B hM
  have hcol (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) :
      ‖classicalSolutionRemainder (classicalSobolevPotential (sourceG3ClassicalCoefficients a))
        (ν n) v t‖ ≤ classicalSobolevErrorConstant (2*M) B/(n.natAbs : ℝ) := by
    have h := norm_classicalSolutionRemainder_sobolev_strip_le (2*M) B
      (sourceG3ClassicalCoefficients a) ha' (ν n) hz him v t
    have he : (4+Real.pi)*(2*M)*‖v‖/‖ν n‖*Real.exp (4*(2*M)+B) =
        classicalSobolevErrorConstant (2*M) B*‖v‖/‖ν n‖ := by
      unfold classicalSobolevErrorConstant
      ring
    rw [he] at h
    exact h.trans ((div_le_div_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_left hv hc) (norm_nonneg _)).trans
        (div_le_div_of_nonneg_left hc hnpos hzn'))
  exact (norm_hermitianColumns_le _ _ _ (hcol (1,0) (by simp))
    (hcol (0,1) (by simp))).trans_eq (by ring)

/-- G.3 is uniform over every index of a fixed near-free sequence,
including arbitrary finite initial frequencies. -/
theorem appendixG_source_remainder_H1_whole_sequence
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) :
    ∃ K : ℝ, ∀ a : ScalarDomain 2 × ScalarDomain 2,
      ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M →
      ∀ n : ℤ, hermitianIntervalH1Norm (classicalHermitianRemainderOperator
        (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n)) ≤ K := by
  obtain ⟨N,_,htail⟩ := sourceLemmaG3_H1 M B hB N₀
  let C := fun n : ℤ => 4*(2+2*‖ν n‖+8*M)*Real.exp (8*M+‖ν n‖)
  obtain ⟨H,hH⟩ := ((Set.finite_Icc (-(N : ℤ)) (N : ℤ)).image C).bddAbove
  refine ⟨max (4*(classicalSobolevErrorConstant (2*M) B+
    classicalSobolevDerivativeConstant (2*M) B)) H,?_⟩
  intro a ha n
  by_cases hn : N ≤ n.natAbs
  · exact (htail ν hν a ha n hn).trans (le_max_left _ _)
  · have hmem : n ∈ Icc (-(N : ℤ)) (N : ℤ) := by
      constructor <;> omega
    exact (appendixG_source_remainder_H1_coarse_bound M a ha (ν n)).trans
      ((hH (mem_image_of_mem C hmem)).trans (le_max_right _ _))

end NLS.ZakharovShabat
