import NLS.Articles.KdVPseudomeasures.SpectralComplexCounting

/-! The actual complex disk count agrees with the source's real-part central block. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- On the entire actual complex spectrum, the constructed central disk
selects exactly the source real-part sublevel. -/
theorem sourceHillSpectrum_mem_complexCircle_iff (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, M ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*R ≤ 1/2)
    (hlarge : 2*(freeHillValue M-12*(M:ℝ))+4*sourceSpectralBound r hr R <
      freeHillValue N-12*(N:ℝ))
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R)
    (z : ℂ) (hz : z ∈ sourceHillSpectrum r hr q) :
    z ∈ ball (0:ℂ) (freeHillValue N-12*(N:ℝ)) ↔ z.re < freeHillValue N-12*(N:ℝ) := by
  simp only [mem_ball, dist_zero_right]
  by_cases hhigh : freeHillValue M-12*(M:ℝ) ≤ z.re
  · have hsmall (n : ℕ) (hn : M ≤ n) :
        13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 :=
      (mul_le_mul_of_nonneg_left hq (by positivity [endpointHillConstant_pos r hr.2])).trans (hs n hn)
    obtain ⟨n, hn, _, hloc⟩ := sourceHillSpectrum_complex_high_cover r hr q M hM hsmall z hz hhigh
    obtain ⟨hnorm, hre⟩ := localized_freeHillCentralEdge_iff N n hN (hM.trans hn) z hloc
    exact hnorm.trans hre.symm
  · have hbound := sourceHillSpectrum_norm_le_on_ball r hr R q hq z hz
    have hnorm : ‖z‖ < freeHillValue N-12*(N:ℝ) := by linarith
    exact iff_of_true hnorm ((Complex.re_le_norm z).trans_lt hnorm)

/-- Equality of the actual enclosed complex finite spectrum and the original central spectrum. -/
theorem sourceComplexEnclosedSpectrum_eq_central (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, M ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*R ≤ 1/2)
    (hlarge : 2*(freeHillValue M-12*(M:ℝ))+4*sourceSpectralBound r hr R <
      freeHillValue N-12*(N:ℝ))
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) :
    endpointHillEnclosedSpectrum r hr.1 hr.2 (sourceEndpointCoefficients r q)
      0 (freeHillValue N-12*(N:ℝ)) = sourceCentralSpectrum r hr q N := by
  ext z
  rw [mem_endpointHillEnclosedSpectrum, mem_sourceCentralSpectrum, ← sourceHillSpectrum_eq r hr q]
  exact and_congr_right fun hz => sourceHillSpectrum_mem_complexCircle_iff r hr R M N hM hN hs hlarge q hq z hz

/-- The actual complex circle count is exactly the original real-part central algebraic count. -/
theorem sourceComplexCircleAlgebraicCount_eq_central (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, M ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*R ≤ 1/2)
    (hlarge : 2*(freeHillValue M-12*(M:ℝ))+4*sourceSpectralBound r hr R <
      freeHillValue N-12*(N:ℝ))
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) :
    sourceComplexCircleAlgebraicCount r hr q N = sourceCentralAlgebraicCount r hr q N := by
  unfold sourceComplexCircleAlgebraicCount endpointHillEnclosedAlgebraicCount
  rw [sourceComplexEnclosedSpectrum_eq_central r hr R M N hM hN hs hlarge q hq]
  simp only [sourceCentralAlgebraicCount, sourceHillAlgebraicMultiplicity_eq r hr q]

/-- The original central block has actual algebraic count2N-1 also for complex potentials. -/
theorem sourceCentralAlgebraicCount_complex_eq (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, M ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*R ≤ 1/2)
    (hlarge : 2*(freeHillValue M-12*(M:ℝ))+4*sourceSpectralBound r hr R <
      freeHillValue N-12*(N:ℝ))
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) :
    sourceCentralAlgebraicCount r hr q N = 2*N-1 := by
  rw [← sourceComplexCircleAlgebraicCount_eq_central r hr R M N hM hN hs hlarge q hq]
  exact sourceComplexCircleAlgebraicCount_eq r hr R N hN
    (fun p hp => sourceComplexCircle_subset_resolvent r hr R M N hM hN hs hlarge p hp) q hq

/-- One cutoff BEFORE the original complex norm ball supplies the exact central
count at EVERY subsequent separator, together with the uniform wide contraction. -/
theorem source_uniform_all_complex_central_counts (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ L : ℕ, 2 ≤ L ∧
      (∀ n : ℕ, L ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*R ≤ 1/2) ∧
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R → ∀ N : ℕ, L ≤ N →
        sourceCentralAlgebraicCount r hr q N = 2*N-1 := by
  obtain ⟨M, hM, hs⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  obtain ⟨L, hL⟩ := exists_nat_gt
    (max (M:ℝ) (2*(freeHillValue M-12*(M:ℝ))+4*sourceSpectralBound r hr R))
  have hML : M ≤ L := by
    have hm : (M:ℝ) < L := (le_max_left _ _).trans_lt hL
    exact_mod_cast hm.le
  refine ⟨L, hM.trans hML, fun n hn => hs n (hML.trans hn), ?_⟩
  intro q hq N hN
  have hN2 : 2 ≤ N := hM.trans (hML.trans hN)
  apply sourceCentralAlgebraicCount_complex_eq r hr R M N hM hN2 hs _ q hq
  have hLN : (L:ℝ) ≤ N := by exact_mod_cast hN
  exact (((le_max_right _ _).trans_lt hL).trans_le hLN).trans (natCast_lt_freeHillCentralEdge N hN2)

end NLS.Articles.KdVPseudomeasures
