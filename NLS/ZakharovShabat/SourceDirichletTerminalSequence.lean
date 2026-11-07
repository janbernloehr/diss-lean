import NLS.ZakharovShabat.SourceDirichletOmittedInverseSequence
import NLS.ZakharovShabat.SourceLemma9_2
import NLS.ZakharovShabat.SourceMidpointSequenceAnalytic
import NLS.ZakharovShabat.SourceBirkhoffSpectralTerminal

/-! The literal signed spectral terminal is analytic in the original
finite-exponent sequence norm. All indices share the original angular
domain, and no gap or action occurs in a denominator. -/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual moving anti-discriminant samples are Banach analytic wherever
all actual Dirichlet roots are analytic. -/
theorem analyticOnNhd_sourceDirichletAntiDiscriminantSamples
    (hp : p ≠ ⊤) (hp1 : 1 < p) {W : Set (CoeffPair p)} (hW : IsOpen W)
    (hroots : ∀ n, AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) W) :
    AnalyticOnNhd ℂ (sourceDirichletAntiDiscriminantSamples hp hp1) W := by
  intro φ hφ
  obtain ⟨U,hU,hφU,K,_,H⟩ := sourceLemma9_2 hp hp1 φ
  apply (Coeff.analyticOnNhd_of_bounded_coordinatewise
    (sourceDirichletAntiDiscriminantSamples hp hp1) (hW.inter hU) ?_ K ?_) φ ⟨hφ,hφU⟩
  · intro n ψ hψ
    exact (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1 _ (mem_univ _)).comp
      (f := fun χ : CoeffPair p => (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet χ n,χ))
      ((hroots n ψ hψ.1).prod analyticAt_id)
  · intro ψ hψ
    exact H.value_norm ψ hψ.2

/-- The actual full terminal sequence, with its bounded inverse-product factor. -/
def sourceGapWeightedEtaTerminalSequence (hp : p ≠ ⊤) (hp1 : 1 < p)
    (sign : ℂ) (ψ : CoeffPair p) : Coeff p :=
  (-2 : ℂ) • (sourceBoundaryDisplacement hp hp1 .dirichlet ψ-
    sourcePeriodicMidpointDisplacement hp hp1 ψ+
      (sign*I/2) • Coeff.multiplierBilinear
        (sourceDirichletOmittedInverseSymbol hp hp1 ψ)
        (sourceDirichletAntiDiscriminantSamples hp hp1 ψ))

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The full midpoint displacement is analytic on the unchanged original domain. -/
theorem periodic_midpoint_displacement_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    AnalyticOnNhd ℂ (sourcePeriodicMidpointDisplacement hp hp1) W := by
  intro φ hφ
  let D := H.original_theta_common_domain
  obtain ⟨_,_,U,hU,hφU,R,_,hbound⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (ε := 1) (by norm_num)
  apply (Coeff.analyticOnNhd_of_bounded_coordinatewise
    (sourcePeriodicMidpointDisplacement hp hp1) (D.source_open.inter hU) ?_ R ?_) φ ⟨hφ,hφU⟩
  · intro n ψ hψ
    simp only [sourcePeriodicMidpointDisplacement_apply]
    exact ((D.symmetric_analytic ψ (D.source_subset hψ.1) n).1).sub analyticAt_const
  · intro ψ hψ
    exact (hbound ψ hψ.2).1

/-- Each coefficient is exactly the literal terminal, with the original sign and scale. -/
theorem gapWeightedEtaTerminalSequence_apply (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) (sign : ℂ) :
    sourceGapWeightedEtaTerminalSequence hp hp1 sign ψ n =
      sourceGapWeightedEtaTerminalCoordinate hp hp1 n sign ψ := by
  change -2*(sourceBoundaryDisplacement hp hp1 .dirichlet ψ n-
    sourcePeriodicMidpointDisplacement hp hp1 ψ n+
    (sign*I/2)*(sourceDirichletOmittedInverseSymbol hp hp1 ψ n*
      sourceDirichletAntiDiscriminantSamples hp hp1 ψ n)) = _
  rw [H.dirichlet_omitted_inverse_symbol_apply ψ hψ n]
  simp only [sourceBoundaryDisplacement_apply,sourcePeriodicMidpointDisplacement_apply,
    sourceDirichletAntiDiscriminantSamples_apply,sourceGapWeightedEtaTerminalCoordinate,
    sourceDirichletEtaSineNumerator,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Both signed terminals are analytic into the original coefficient space,
on one unchanged complex domain before all indices and all signs. -/
theorem gapWeightedEtaTerminalSequence_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (sign : ℂ) : AnalyticOnNhd ℂ (sourceGapWeightedEtaTerminalSequence hp hp1 sign) W := by
  let D := H.original_theta_common_domain
  have ha := analyticOnNhd_sourceDirichletAntiDiscriminantSamples hp hp1 D.source_open
    (fun n ψ hψ => D.roots_analytic .dirichlet n ψ (D.source_subset hψ))
  intro ψ hψ
  exact (((D.boundary_analytic .dirichlet ψ (D.source_subset hψ)).sub
    (H.periodic_midpoint_displacement_analytic ψ hψ)).add
      ((((Coeff.multiplierBilinear (p := p)).analyticAt_bilinear _).comp
        ((H.dirichlet_omitted_inverse_symbol_analytic ψ hψ).prod (ha ψ hψ))).const_smul
          (c := sign*I/2))).const_smul (c := (-2 : ℂ))

/-- The construction supplies a common complex domain containing the entire
physical source locus, with exact coefficients for every sign and index. -/
theorem exists_gapWeightedEtaTerminalSequence_analytic_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ sign : ℂ, AnalyticOnNhd ℂ (sourceGapWeightedEtaTerminalSequence hp hp1 sign) W ∧
        ∀ ψ ∈ W, ∀ n, sourceGapWeightedEtaTerminalSequence hp hp1 sign ψ n =
          sourceGapWeightedEtaTerminalCoordinate hp hp1 n sign ψ := by
  obtain ⟨W₀,_,_,_,W,hW,_,hreal,s,H⟩ := sourceLemma12_12 hp hp1
  exact ⟨W,hW,hreal,fun sign => ⟨H.gapWeightedEtaTerminalSequence_analytic sign,
    fun ψ hψ n => H.gapWeightedEtaTerminalSequence_apply ψ hψ n sign⟩⟩

end SourceLemma12_12Data
end NLS.ZakharovShabat
