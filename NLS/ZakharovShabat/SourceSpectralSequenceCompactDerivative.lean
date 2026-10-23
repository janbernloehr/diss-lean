import NLS.ZakharovShabat.SourceMidpointSequenceAnalytic
import NLS.ZakharovShabat.SourceSpectralGradientSobolevSummability
import NLS.ZakharovShabat.SourceLemmaG7
import NLS.ZakharovShabat.SourceSection20SobolevDomain
import NLS.SequenceSpaces.CompactRowMajorant
import NLS.SequenceSpaces.PairExponentIdentity

/-! # Compact derivatives of the actual Hilbert spectral displacement sequences

At physical H1 sources the established operator-row estimates yield
finite-rank approximation. Density of H1 and continuity of the analytic
sequence derivatives extend compactness to a common complex neighborhood
of the entire real Hilbert source locus. No H1 assumption remains there.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ZakharovShabat

private theorem compact_operator_of_memlp_rows
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] Coeff 2) (L : ℤ → E →L[ℂ] ℂ) (hL : Memℓp L 2)
    (he : ∀ h n, T h n = L n h) : IsCompactOperator T := by
  let b : Coeff 2 := ⟨fun n => (‖L n‖ : ℂ), Memℓp.of_norm (by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_norm] using hL.norm)⟩
  apply Coeff.isCompactOperator_of_rowMajorant (by simp) T b
  intro n h
  rw [he]
  change ‖L n h‖ ≤ ‖(‖L n‖ : ℂ)‖ * ‖h‖
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_norm] using (L n).le_opNorm h

/-- One complex neighborhood of the entire real Hilbert locus has compact midpoint derivative
and compact Dirichlet derivative error relative to the exact free derivative. -/
theorem exists_source_spectral_sequence_compact_derivative_domain :
    ∃ W : Set (CoeffPair 2), IsOpen W ∧ realTypeSourceLocus 2 ⊆ W ∧ ∀ φ ∈ W,
      IsCompactOperator (fderiv ℂ (sourcePeriodicMidpointDisplacement (by simp) (by norm_num)) φ) ∧
      IsCompactOperator
        (fderiv ℂ (sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet) φ -
          fderiv ℂ (sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet) 0) := by
  let D := sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet
  let M := sourcePeriodicMidpointDisplacement (p := 2) (by simp) (by norm_num)
  obtain ⟨U,hU,hrealU,hrows⟩ := exists_global_source_spectral_gradients_sobolev_memlp
    (p := 2) (by simp) (by norm_num) le_rfl
  obtain ⟨V,hV,hrealV,hD⟩ := exists_sourceBoundaryDisplacement_analytic_common_domain
    (p := 2) (by simp) (by norm_num)
  obtain ⟨A,hA,hrealA,hM⟩ := exists_sourcePeriodicMidpointDisplacement_analytic_common_domain
    (p := 2) (by simp) (by norm_num)
  let W := U ∩ (V ∩ A)
  have hW : IsOpen W := hU.inter (hV.inter hA)
  have hzero : DifferentiableAt ℂ D 0 :=
    (hD .dirichlet 0 (hrealV (by simp [realTypeSourceLocus]))).differentiableAt
  have hsmooth (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ W) :
      IsCompactOperator (fderiv ℂ M (sobolevSourceInclusion a)) ∧
      IsCompactOperator (fderiv ℂ D (sobolevSourceInclusion a) - fderiv ℂ D 0) := by
    have h := hrows (sobolevSourceInclusion a)
      (by simpa only [CoeffPair.exponentInclusion_refl] using ha.1)
      (sourceG3ClassicalCoefficients a) (sourceG7_periodic_representative a)
    simp only [CoeffPair.exponentInclusion_refl] at h
    constructor
    · apply compact_operator_of_memlp_rows _ _ h.1
      intro v n
      exact fderiv_sourcePeriodicMidpointDisplacement_apply_of_differentiableAt
        (by simp) (by norm_num) _ v n (hM _ ha.2.2).differentiableAt
    · apply compact_operator_of_memlp_rows _ _ h.2
      intro v n
      change (fderiv ℂ D (sobolevSourceInclusion a)) v n - (fderiv ℂ D 0) v n = _
      rw [fderiv_sourceBoundaryDisplacement_apply_of_differentiableAt
        (by simp) (by norm_num) .dirichlet _ v n (hD .dirichlet _ ha.2.1).differentiableAt,
        fderiv_sourceBoundaryDisplacement_apply_of_differentiableAt
          (by simp) (by norm_num) .dirichlet 0 v n hzero,
        fderiv_canonicalDirichletRoot_zero_eq_free (by simp) (by norm_num) le_rfl n]
      rfl
  refine ⟨W,hW,fun φ hφ => ⟨hrealU hφ,hrealV hφ,hrealA hφ⟩,fun φ hφ => ?_⟩
  obtain ⟨a,ha,hat⟩ := mem_closure_iff_seq_limit.mp (sobolevSourceInclusion_denseRange φ)
  have hev : ∀ᶠ k in atTop, a k ∈ W := hat.eventually (hW.mem_nhds hφ)
  have hmcont : ContinuousAt (fun ψ => fderiv ℂ M ψ) φ :=
    (hM φ hφ.2.2).contDiffAt.continuousAt_fderiv (n := 1) one_ne_zero
  have hdcont : ContinuousAt (fun ψ => fderiv ℂ D ψ - fderiv ℂ D 0) φ :=
    ((hD .dirichlet φ hφ.2.1).contDiffAt.continuousAt_fderiv (n := 1) one_ne_zero).sub continuousAt_const
  have hcompact : ∀ᶠ k in atTop,
      IsCompactOperator (fderiv ℂ M (a k)) ∧
      IsCompactOperator (fderiv ℂ D (a k) - fderiv ℂ D 0) := by
    filter_upwards [hev] with k hk
    obtain ⟨b,hb⟩ := ha k
    rw [← hb] at hk ⊢
    exact hsmooth b hk
  exact ⟨isCompactOperator_of_tendsto (hmcont.tendsto.comp hat) (hcompact.mono fun _ h => h.1),
    isCompactOperator_of_tendsto (hdcont.tendsto.comp hat) (hcompact.mono fun _ h => h.2)⟩

/-- The actual spectral sequence derivative compactness holds at every real Hilbert source. -/
theorem source_spectral_sequence_derivatives_compact_of_realType
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    IsCompactOperator (fderiv ℂ (sourcePeriodicMidpointDisplacement (by simp) (by norm_num)) φ) ∧
      IsCompactOperator
        (fderiv ℂ (sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet) φ -
          fderiv ℂ (sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet) 0) := by
  obtain ⟨_,_,hr,h⟩ := exists_source_spectral_sequence_compact_derivative_domain
  exact h φ (hr hφ)

end NLS.ZakharovShabat
