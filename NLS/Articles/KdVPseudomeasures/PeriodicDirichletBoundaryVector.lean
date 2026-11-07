import NLS.Articles.KdVPseudomeasures.PeriodicSpectralParity
import NLS.Articles.KdVPseudomeasures.PeriodicSpectralRegularity
import NLS.KdV.SingularHillBoundaryVector

/-! The ACTUAL normalized high periodic spectral vector with zero boundary
values and its faithful native Dirichlet restriction, on original source norm balls. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- ONE original endpoint norm-ball cutoff produces the ACTUAL boundary-zero
periodic spectral vector and its UNIQUE original zero-trace interval restriction.
Both physical L2 norms are EXACTLY ONE. The full original stronger distribution,
source circle, positive index and mode parity are retained. -/
theorem exists_uniform_sourcePeriodicDirichletBoundaryVector (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      IsPeriodicDistribution 1 q.val.toTempered → ∀ n : ℕ+, N ≤ (n:ℕ) →
        ∃ G : FourierLebesgueSpace (2:ℝ) 1 2, ∃ g : UnitDirichletH1,
          ‖singularHillL2DomainInclusion G‖=1 ∧ ‖unitDirichletL2Inclusion g‖=1 ∧
          singularHillL2DomainInclusion G ∈ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q)
            (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range ∧
          singularHillContinuousDomainInclusion G (0 : AddCircle (2:ℝ))=0 ∧
          singularHillContinuousDomainInclusion G ((1:ℝ) : AddCircle (2:ℝ))=0 ∧
          (∀ x : ℝ, singularHillContinuousDomainInclusion G ((x+1:ℝ) : AddCircle (2:ℝ))=
            wave (n:ℤ) 1*singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))) ∧
          (∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x=singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))) ∧
          (∃ u : FourierLebesgueSpace (2:ℝ) (-r+2) ⊤, u.val=G.val) := by
  obtain ⟨NP,hNP,hmin,hparity⟩ := exists_uniform_sourcePeriodicRange_parity r hr R Nmin
  obtain ⟨NC,_,hcircles⟩ := exists_uniform_sourcePeriodicCircle_rank_two r hr R
  refine ⟨max NP NC,hNP.trans (le_max_left _ _),hmin.trans (le_max_left _ _),?_⟩
  intro q hq hp n hn
  have hc := (hcircles q hq n ((le_max_right _ _).trans hn)).1
  have hd := (hcircles q hq n ((le_max_right _ _).trans hn)).2
  have hpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast n.property
  obtain ⟨G,hGn,hGmem,hG0⟩ := exists_singularHill_boundaryZero_spectralVector (sourceComplexHminusOne r hr q) _ _ hpos hc hd
  have hGparity := hparity q hq hp n ((le_max_left _ _).trans hn) _ hGmem
  obtain ⟨g,hg,hgn⟩ := exists_hillH1_DirichletRestriction_norm (n:ℤ) G hGparity hG0
  obtain ⟨u,hu⟩ := sourcePeriodicH1Vector_regular r hr q _ _ hpos hc G hGmem
  have hG1 : singularHillContinuousDomainInclusion G ((1:ℝ) : AddCircle (2:ℝ))=0 := by
    simpa [hG0] using hillH1Continuous_translate_one_of_parity (n:ℤ) G hGparity 0
  exact ⟨G,g,hGn,hgn.trans hGn,hGmem,hG0,hG1,hillH1Continuous_translate_one_of_parity (n:ℤ) G hGparity,hg,⟨u,hu⟩⟩

end NLS.Articles.KdVPseudomeasures
