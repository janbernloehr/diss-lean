import NLS.Articles.KdVPseudomeasures.PeriodicSpectralBasis
import NLS.KdV.SingularHillEigenResidual

/-! The upper-triangular equation of source Lemma 2.13 for the actual
canonical original complex pair and actual source-normalized spectral basis.
The quantitative eta bound remains a separate estimate. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- For every actual high canonical source pair, ANY source orthonormal
basis starting with its lambda_n^+ eigenfunction has the claimed native
eta/gamma equation. This includes coincident roots and associated vectors. -/
theorem exists_sourcePeriodicEigenResidual (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (n : ℕ+)
    (p : SourceHillComplexPair r hr q n)
    (hl : sourceHillComplexLabels r hr q (2*(n:ℕ)-1) = p.left)
    (hu : sourceHillComplexLabels r hr q (2*(n:ℕ)) = p.right)
    (b : OrthonormalBasis (Fin 2) ℂ (singularHillL2RieszProjection
      (sourceComplexHminusOne r hr q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range)
    (f phi : FourierLebesgueSpace (2:ℝ) 1 2)
    (hb0 : (b 0).val = singularHillL2DomainInclusion f)
    (hb1 : (b 1).val = singularHillL2DomainInclusion phi)
    (hf : singularHillOperator (sourceComplexHminusOne r hr q) f =
      sourceHillComplexLabels r hr q (2*(n:ℕ)) • singularHillDomainInclusion f) :
    ∃ eta : ℂ, singularHillOperator (sourceComplexHminusOne r hr q) phi -
        sourceHillComplexLabels r hr q (2*(n:ℕ)) • singularHillDomainInclusion phi =
      -(sourceHillComplexLabels r hr q (2*(n:ℕ)) -
        sourceHillComplexLabels r hr q (2*(n:ℕ)-1)) • singularHillDomainInclusion phi +
          eta • singularHillDomainInclusion f := by
  have hc := (SourceHillComplexPair.sourceCircle_rank_two r hr q n p).1
  have hmsp : sourceHillComplexLabels r hr q (2*(n:ℕ)-1) ∈
      singularHillSpectrum (sourceComplexHminusOne r hr q) := by
    rw [hl]
    have hs : p.left ∈ sourceHillSpectrum r hr q := by
      rw [sourceHillSpectrum_eq]
      exact p.left_spectral
    exact hs
  have hmi := p.left_mem_sourceBall r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q) n.property
  rw [freeHillValue_natCast_complex,← hl] at hmi
  apply exists_singularHill_eigen_residual (sourceComplexHminusOne r hr q) _ (n:ℝ)
    (by exact_mod_cast n.property) hc _ _ hmsp hmi _ b f phi hb0 hb1 hf
  intro mu hmu hsp
  have hstrip : mu ∈ reducedHillStrip (n:ℕ) := by
    apply freeHillSourceDisk_subset_strip (n:ℕ) n.property
    rw [freeHillValue_natCast_complex]
    exact ball_subset_closedBall hmu
  have hsource : mu ∈ sourceHillSpectrum r hr q := hsp
  rcases (SourceHillComplexPair.spectrum_iff r hr q (n:ℕ) p mu hstrip).mp hsource with h | h
  · exact Or.inr (h.trans hl.symm)
  · exact Or.inl (h.trans hu.symm)

/-- The actual canonical source eta/gamma identity has ONE cutoff before
EVERY original complex endpoint potential in a specified norm ball and ALL
later original positive indices. Both native basis vectors have source L2
norm ONE and form an ACTUAL orthonormal basis of the FULL spectral range. -/
theorem exists_uniform_sourcePeriodicEigenResidual (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) →
        ∃ f phi : FourierLebesgueSpace (2:ℝ) 1 2, ∃ eta : ℂ,
          singularHillOperator (sourceComplexHminusOne r hr q) f =
            sourceHillComplexLabels r hr q (2*(n:ℕ)) • singularHillDomainInclusion f ∧
          ‖singularHillL2DomainInclusion f‖ = 1 ∧
          ‖singularHillL2DomainInclusion phi‖ = 1 ∧
          (∃ b : OrthonormalBasis (Fin 2) ℂ (singularHillL2RieszProjection
              (sourceComplexHminusOne r hr q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range,
            (b 0).val = singularHillL2DomainInclusion f ∧
            (b 1).val = singularHillL2DomainInclusion phi) ∧
          singularHillOperator (sourceComplexHminusOne r hr q) phi -
              sourceHillComplexLabels r hr q (2*(n:ℕ)) • singularHillDomainInclusion phi =
            -(sourceHillComplexLabels r hr q (2*(n:ℕ)) -
              sourceHillComplexLabels r hr q (2*(n:ℕ)-1)) • singularHillDomainInclusion phi +
                eta • singularHillDomainInclusion f := by
  obtain ⟨NB,hNB,hbasis⟩ := exists_uniform_sourcePeriodicSpectralBasis r hr R
  obtain ⟨NL,hNL,hlabels⟩ := source_uniform_canonical_complex_labels r hr R
  refine ⟨max NB NL,le_trans hNB (le_max_left _ _),?_⟩
  intro q hq n hn
  obtain ⟨_,_,f,hf,hfn,_,b,hb,hdom⟩ := hbasis q hq n ((le_max_left _ _).trans hn)
  obtain ⟨phi,hphi⟩ := hdom 1
  obtain ⟨p,hl,hu⟩ := (hlabels q hq).high_pair (n:ℕ) ((le_max_right _ _).trans hn)
  obtain ⟨eta,heta⟩ := exists_sourcePeriodicEigenResidual r hr q n p hl hu b f phi hb hphi.symm hf
  have hphin : ‖singularHillL2DomainInclusion phi‖ = 1 := by
    rw [hphi]
    exact b.orthonormal.norm_eq_one 1
  exact ⟨f,phi,eta,hf,hfn,hphin,⟨b,hb,hphi.symm⟩,heta⟩

end NLS.Articles.KdVPseudomeasures
