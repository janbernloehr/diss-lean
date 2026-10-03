import NLS.ZakharovShabat.SourceSpectralGradientSobolevSummability
import NLS.ZakharovShabat.SourceAntiDiscriminantSobolevSummability

/-! # Independent outer exponents for Hilbert source gradient errors

The physical Fourier estimates allow inner exponent two and every outer
exponent strictly above one. Keeping these exponents independent enables
restriction of the actual Hilbert cotangents to smaller source spaces.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem hilbert_gt_gradient_threshold (s : ℝ) (hs : 1 < s) :
    ENNReal.ofReal (1+1/s) < (2 : ℝ≥0∞) := by
  have h : 1/s < 1 := (div_lt_one (by linarith)).mpr hs
  have hbound : ENNReal.ofReal (1+1/s) < ENNReal.ofReal 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by linarith)
  simpa only [ENNReal.ofReal_ofNat] using hbound

/-- Actual Hilbert midpoint derivatives have every outer exponent above one. -/
theorem memlp_hilbert_midpoint_fderiv_outer
    (s : ℝ) (hs : 1 < s) (φ : CoeffPair 2) (hφ : φ ∈ realTypeSourceLocus 2)
    (a : Domain 2) (ha : periodOnePotential φ = domainInclusion a) :
    Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodicMidpoint
      (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ)
      (ENNReal.ofReal s) := by
  obtain ⟨U,_,hmem,N,hlocal⟩ := exists_local_source_midpoint_fderiv_tail_contour_bound
    (p := 2) (by simp) (by norm_num) φ hφ
  obtain ⟨N₀,_,b,hb,h⟩ := exists_sourceMidpointContourIntegrand_sobolev_uniform_memlp
    (p := 2) (q := 2) (by simp) (by norm_num) le_rfl s hs
    (hilbert_gt_gradient_threshold s hs) ‖a‖ (norm_nonneg _)
  apply memlp_of_natAbs_eventual_bound s (by linarith) _
    (fun n => (Real.pi/4)*b n) (hb.const_mul (Real.pi/4)) (max (N+1) N₀)
  intro n hn
  have hn₁ : N < n.natAbs := by omega
  have hn₂ : N₀ ≤ n.natAbs := le_trans (le_max_right _ _) hn
  exact (hlocal φ hmem n hn₁).2.2 (b n)
    (h a le_rfl φ (physicalBase_source_sobolev_compatibility φ a ha) n hn₂)

/-- Actual Hilbert Dirichlet derivative errors have every outer exponent above one. -/
theorem memlp_hilbert_dirichlet_fderiv_error_outer
    (s : ℝ) (hs : 1 < s) (φ : CoeffPair 2) (hφ : φ ∈ realTypeSourceLocus 2)
    (a : Domain 2) (ha : periodOnePotential φ = domainInclusion a) :
    Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair 2 =>
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ n) φ-
      sourceFreeDirichletCotangent 2 n) (ENNReal.ofReal s) := by
  obtain ⟨W,_,hreal,hbound⟩ := exists_global_source_dirichlet_fderiv_error_fourier_bound
    (p := 2) (q := 2) (by simp) (by norm_num) le_rfl (by norm_num)
  have h₁ := memlp_source_dirichlet_gradient_fourier_norms (p := 2) (by simp) (by norm_num)
    le_rfl s hs 2 (hilbert_gt_gradient_threshold s hs) φ a ha
    (ContinuousLinearMap.fst ℝ ℂ ℂ) (ContinuousLinearMap.norm_fst_le ..)
  have h₂ := memlp_source_dirichlet_gradient_fourier_norms (p := 2) (by simp) (by norm_num)
    le_rfl s hs 2 (hilbert_gt_gradient_threshold s hs) φ a ha
    (ContinuousLinearMap.snd ℝ ℂ ℂ) (ContinuousLinearMap.norm_snd_le ..)
  apply (h₁.add h₂).mono
  intro n
  have h := hbound φ (hreal hφ) a ha n
  dsimp only at h
  rwa [fderiv_canonicalDirichletRoot_zero_eq_free (by simp) (by norm_num) le_rfl n] at h

/-- Actual Hilbert anti-discriminant cotangent errors at either canonical
boundary sequence have every outer exponent above one. -/
theorem memlp_hilbert_antiDiscriminantCotangent_error_outer
    (s : ℝ) (hs : 1 < s) (φ : CoeffPair 2)
    (a : Domain 2) (ha : periodOnePotential φ = domainInclusion a) (b : BoundaryCondition) :
    Memℓp (fun n : ℤ => sourceAntiDiscriminantCotangent (by simp) (by norm_num)
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) b φ n) φ-
      sourceAntiDiscriminantCotangent (by simp) (by norm_num) ((Real.pi : ℂ)*n) 0)
      (ENNReal.ofReal s) := by
  have h₁ := memlp_source_antiDiscriminant_gradient_fourier_norms (p := 2) (by simp) (by norm_num)
    le_rfl s hs 2 (hilbert_gt_gradient_threshold s hs) φ a ha b
    (ContinuousLinearMap.fst ℝ ℂ ℂ) (ContinuousLinearMap.norm_fst_le ..)
  have h₂ := memlp_source_antiDiscriminant_gradient_fourier_norms (p := 2) (by simp) (by norm_num)
    le_rfl s hs 2 (hilbert_gt_gradient_threshold s hs) φ a ha b
    (ContinuousLinearMap.snd ℝ ℂ ℂ) (ContinuousLinearMap.norm_snd_le ..)
  exact (h₁.add h₂).mono (fun n => norm_sourceAntiDiscriminantCotangent_error_le
    (p := 2) (q := 2) (by simp) (by norm_num) le_rfl (by norm_num)
    φ (classicalSobolevPotential a) (physicalBase_source_sobolev_compatibility φ a ha)
    (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) b φ n) ((Real.pi : ℂ)*n))

end NLS.ZakharovShabat
