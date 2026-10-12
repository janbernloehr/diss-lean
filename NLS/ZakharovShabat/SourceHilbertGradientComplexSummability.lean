import NLS.ZakharovShabat.SourceHilbertGradientOuterSummability
import NLS.SequenceSpaces.PairExponentIdentity

/-! # Complex neighborhoods for independent outer Hilbert exponents

The local midpoint contour domains can be united before choosing the
outer exponent. The Dirichlet Fourier bound already has a common domain.
Both estimates retain the original H1 source and all signed indices.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem complexHilbert_gt_threshold (s : ℝ) (hs : 1 < s) :
    ENNReal.ofReal (1+1/s) < (2 : ℝ≥0∞) := by
  have h : 1/s < 1 := (div_lt_one (by linarith)).mpr hs
  have hbound : ENNReal.ofReal (1+1/s) < ENNReal.ofReal 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by linarith)
  simpa only [ENNReal.ofReal_ofNat] using hbound

/-- One open complex domain supports every outer exponent strictly above
one for the actual Hilbert midpoint derivatives of H1 sources. -/
theorem exists_global_hilbert_midpoint_outer_complex :
    ∃ W : Set (CoeffPair 2), IsOpen W ∧ realTypeSourceLocus 2 ⊆ W ∧
      ∀ (s : ℝ), 1 < s → ∀ φ ∈ W, ∀ a : Domain 2,
        periodOnePotential φ = domainInclusion a →
        Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodicMidpoint
          (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ)
          (ENNReal.ofReal s) := by
  classical
  let R := realTypeSourceLocus 2
  have hloc := fun φ : R => exists_local_source_midpoint_fderiv_tail_contour_bound
    (p := 2) (by simp) (by norm_num) φ.val φ.property
  choose U hU hmem N hlocal using hloc
  refine ⟨⋃ φ : R, U φ,isOpen_iUnion hU,?_,?_⟩
  · intro φ hφ
    exact mem_iUnion_of_mem (⟨φ,hφ⟩ : R) (hmem ⟨φ,hφ⟩)
  intro s hs φ hφ a ha
  obtain ⟨ι,hι⟩ := mem_iUnion.mp hφ
  obtain ⟨N₀,_,b,hb,h⟩ := exists_sourceMidpointContourIntegrand_sobolev_uniform_memlp
    (p := 2) (q := 2) (by simp) (by norm_num) le_rfl s hs
    (complexHilbert_gt_threshold s hs) ‖a‖ (norm_nonneg _)
  apply memlp_of_natAbs_eventual_bound s (by linarith) _
    (fun n => (Real.pi/4)*b n) (hb.const_mul (Real.pi/4)) (max (N ι+1) N₀)
  intro n hn
  have hn₁ : N ι < n.natAbs := by omega
  have hn₂ : N₀ ≤ n.natAbs := le_trans (le_max_right _ _) hn
  exact (hlocal ι φ hι n hn₁).2.2 (b n)
    (h a le_rfl φ (physicalBase_source_sobolev_compatibility φ a ha) n hn₂)

/-- The same independence of the outer exponent holds for actual Dirichlet
derivative errors, with the exact free cotangent subtracted. -/
theorem exists_global_hilbert_dirichlet_outer_complex :
    ∃ W : Set (CoeffPair 2), IsOpen W ∧ realTypeSourceLocus 2 ⊆ W ∧
      ∀ (s : ℝ), 1 < s → ∀ φ ∈ W, ∀ a : Domain 2,
        periodOnePotential φ = domainInclusion a →
        Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair 2 =>
          canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ n) φ-
          sourceFreeDirichletCotangent 2 n) (ENNReal.ofReal s) := by
  obtain ⟨W,hW,hreal,hbound⟩ := exists_global_source_dirichlet_fderiv_error_fourier_bound
    (p := 2) (q := 2) (by simp) (by norm_num) le_rfl (by norm_num)
  refine ⟨W,hW,hreal,?_⟩
  intro s hs φ hφ a ha
  have h₁ := memlp_source_dirichlet_gradient_fourier_norms (p := 2) (by simp) (by norm_num)
    le_rfl s hs 2 (complexHilbert_gt_threshold s hs) φ a ha
    (ContinuousLinearMap.fst ℝ ℂ ℂ) (ContinuousLinearMap.norm_fst_le ..)
  have h₂ := memlp_source_dirichlet_gradient_fourier_norms (p := 2) (by simp) (by norm_num)
    le_rfl s hs 2 (complexHilbert_gt_threshold s hs) φ a ha
    (ContinuousLinearMap.snd ℝ ℂ ℂ) (ContinuousLinearMap.norm_snd_le ..)
  apply (h₁.add h₂).mono
  intro n
  have hφ' : CoeffPair.exponentInclusion (le_rfl : (2 : ℝ≥0∞) ≤ 2) φ ∈ W := by
    simpa only [CoeffPair.exponentInclusion_refl] using hφ
  have h := hbound φ hφ' a ha n
  dsimp only at h
  simpa [CoeffPair.exponentInclusion_refl,
    fderiv_canonicalDirichletRoot_zero_eq_free (by simp) (by norm_num) le_rfl n] using h

end NLS.ZakharovShabat
