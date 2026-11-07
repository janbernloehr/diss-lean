import NLS.Articles.KdVPseudomeasures.PeriodicSourceCircles
import NLS.Articles.KdVPseudomeasures.SpectralComplexCanonical
import NLS.KdV.SingularHillSpectralBasis

/-! Source spectral bases in the actual periodic physical L2 space, at the
canonical source label lambda_n^+. One cutoff precedes every potential on
each exact original complex endpoint norm ball. The quantitative eta estimate
and periodic projection convergence remain separate obligations. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The source orthonormal spectral basis exists uniformly above ONE
original endpoint norm-ball cutoff. Its first member is an ACTUAL original
H1 eigenfunction at the CANONICAL original lambda_n^+; both basis directions
retain original H1 representatives, even at nonsemisimple complex eigenvalues. -/
theorem exists_uniform_sourcePeriodicSpectralBasis (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) →
        sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆
          singularHillResolventSet (sourceComplexHminusOne r hr q) ∧
        Module.finrank ℂ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q)
          (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range = 2 ∧
        ∃ f : FourierLebesgueSpace (2:ℝ) 1 2,
          singularHillOperator (sourceComplexHminusOne r hr q) f =
            sourceHillComplexLabels r hr q (2*(n:ℕ)) • singularHillDomainInclusion f ∧
          ‖singularHillL2DomainInclusion f‖ = 1 ∧
          (1/2:ℝ) * (∫ x in (0:ℝ)..2, ‖circlePullback (singularHillL2DomainInclusion f) x‖^2) = 1 ∧
          ∃ b : OrthonormalBasis (Fin 2) ℂ (singularHillL2RieszProjection
              (sourceComplexHminusOne r hr q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range,
            (b 0).val = singularHillL2DomainInclusion f ∧
            ∀ i : Fin 2, ∃ g : FourierLebesgueSpace (2:ℝ) 1 2,
              singularHillL2DomainInclusion g = (b i).val := by
  obtain ⟨N,hN,hlabels⟩ := source_uniform_canonical_complex_labels r hr R
  refine ⟨N,hN,?_⟩
  intro q hq n hn
  obtain ⟨p,_,hp⟩ := (hlabels q hq).high_pair (n:ℕ) hn
  obtain ⟨hc,hk⟩ := SourceHillComplexPair.sourceCircle_rank_two r hr q n p
  have hi := p.right_mem_sourceBall r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q) n.property
  rw [freeHillValue_natCast_complex,← hp] at hi
  have hsp : sourceHillComplexLabels r hr q (2*(n:ℕ)) ∈
      singularHillSpectrum (sourceComplexHminusOne r hr q) := (hlabels q hq).spectral _
  obtain ⟨f,hf,hfn,b,hb,hdom⟩ := exists_singularHill_spectral_orthonormalBasis
    (sourceComplexHminusOne r hr q) _ (n:ℝ) (by exact_mod_cast n.property) hc hk
      _ hsp hi
  refine ⟨hc,hk,f,hf,hfn,?_,b,hb,hdom⟩
  rw [← norm_sq_singularHillPhysicalL2,hfn,one_pow]

end NLS.Articles.KdVPseudomeasures
