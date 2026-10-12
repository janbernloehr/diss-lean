import NLS.ZakharovShabat.SourceHilbertGradientComplexSummability
import NLS.ZakharovShabat.L2SourceG7BelowTwo

/-! # Physical G.7 summability below two on complex neighborhoods

Analytic Hilbert coordinate identities justify restriction of the actual
derivatives at complex potentials. The existing physical realizations and
new whole-sequence estimates hold on one common source neighborhood.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Restrict both Hilbert derivatives on a common complex domain, retaining
the original source exponent and actual free reference. -/
theorem exists_global_source_gradients_below_two_complex_memlp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ ∈ W, ∀ a : Domain 2,
        periodOnePotential (CoeffPair.exponentInclusion hp2 φ) = domainInclusion a →
        Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint
          hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ) p ∧
        Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ-
          sourceFreeDirichletCotangent p n) p := by
  obtain ⟨U,hU,hUr,hmid⟩ := exists_global_hilbert_midpoint_outer_complex
  obtain ⟨V,hV,hVr,hdir⟩ := exists_global_hilbert_dirichlet_outer_complex
  obtain ⟨A,hA,_,hAr,hAn⟩ := exists_global_source_analytic_midpoint_squaredGap
    (p := 2) (by simp) (by norm_num)
  obtain ⟨B,hB,hBr,hroots⟩ := exists_sourceBoundaryRoots_simple_common_domain
    (p := 2) (by simp) (by norm_num)
  refine ⟨(CoeffPair.exponentInclusion hp2) ⁻¹' ((U ∩ V) ∩ (A ∩ B)),
    ((hU.inter hV).inter (hA.inter hB)).preimage (CoeffPair.exponentInclusion hp2).continuous,?_,?_⟩
  · intro φ hφ
    have hr := (realTypeSourceExponentInclusion hp2 ⟨φ,hφ⟩).property
    exact ⟨⟨hUr hr,hVr hr⟩,⟨hAr hr,hBr hr⟩⟩
  intro φ hφ a ha
  have hs : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hm := hmid p.toReal hs _ hφ.1.1 a ha
  have hd := hdir p.toReal hs _ hφ.1.2 a ha
  rw [ENNReal.ofReal_toReal hp] at hm hd
  constructor
  · have h := memlp_cotangent_exponent_restriction hp2 _ hm
    convert h using 1
    funext n
    exact fderiv_midpoint_below_two_of_hilbert_differentiable hp hp1 hp2 φ n
      (hAn _ hφ.2.1 n).1.differentiableAt
  · have h := memlp_cotangent_exponent_restriction hp2 _ hd
    convert h using 1
    funext n
    rw [fderiv_dirichlet_below_two_of_hilbert_differentiable hp hp1 hp2 φ n
      (hroots _ hφ.2.2 .dirichlet n).1.differentiableAt,
      sourceFreeDirichletCotangent_exponent hp2]
    rfl

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Both physical G.7 coefficient sequences are summable on one complex
neighborhood for 1<p<=2, with nonzero Dirichlet normalization at every index. -/
theorem exists_global_sourceG7_below_two_physical_complex
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ ∈ W, ∀ a : Domain 2,
        periodOnePotential (CoeffPair.exponentInclusion hp2 φ) = domainInclusion a →
        Memℓp (fun n : ℤ => sourceG7MidpointGradient (q := q) hp hp1 φ n) p ∧
        Memℓp (fun n : ℤ => sourceG7DirichletGradientError (q := q) hp hp1 φ n) p ∧
        ∀ n : ℤ,
          L2RootGradientFourierRealizes (sourceMidpointPhysicalGradientBelowTwo hp2 φ n)
            (sourceG7MidpointGradient (q := q) hp hp1 φ n) ∧
          let u := sourcePhysicalL2 (CoeffPair.exponentInclusion hp2 φ)
          let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
          l2DirichletNormalization u z ≠ 0 ∧
            L2RootGradientFourierRealizes (l2DirichletGradientRemainder u z ((Real.pi : ℂ)*n))
              (sourceG7DirichletGradientError (q := q) hp hp1 φ n) := by
  obtain ⟨W,hW,hWr,hseq⟩ := exists_global_source_gradients_below_two_complex_memlp hp hp1 hp2
  obtain ⟨U,hU,hUr,hu⟩ := exists_global_sourceG7_midpoint_below_two_realization (q := q) hp hp1 hp2
  obtain ⟨V,hV,hVr,hv⟩ := exists_global_sourceG7_dirichlet_below_two_realization (q := q) hp hp1 hp2
  refine ⟨W ∩ (U ∩ V),hW.inter (hU.inter hV),fun φ hφ => ⟨hWr hφ,hUr hφ,hVr hφ⟩,?_⟩
  intro φ hφ a ha
  obtain ⟨hm,hd⟩ := hseq φ hφ.1 a ha
  have hq : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne'
  have hmc := CoeffPair.memlp_conjugateGradient (q := q) hp hq _ hm
  have hdc := CoeffPair.memlp_conjugateGradient (q := q) hp hq _ hd
  refine ⟨?_,?_,fun n => ⟨hu φ hφ.2.1 n,hv φ hφ.2.2 n⟩⟩
  · apply Memℓp.of_norm
    simpa only [sourceG7MidpointGradient,norm_sourceG7SignedCoordinates,sourceMidpointConjugateGradient] using hmc.norm
  · apply Memℓp.of_norm
    simpa only [sourceG7DirichletGradientError,norm_sourceG7SignedCoordinates,sourceDirichletConjugateGradientError] using hdc.norm

end NLS.ZakharovShabat
