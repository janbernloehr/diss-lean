import NLS.Articles.KdVPseudomeasures.PeriodicDirichletOverlap
import NLS.Articles.KdVPseudomeasures.PeriodicEtaBound
import NLS.KdV.HillDirichletSignedRestriction
import NLS.KdV.SingularHillSpectralCoordinates
import NLS.KdV.SingularHillCombinationResidual

/-! Full source Lemma2.15 with the necessary correction to printed(31):
the spectral coordinate beta multiplies BOTH residual terms. The proof
immediately below printed(31) has precisely this corrected coefficient. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat

/-- Corrected FULL source Lemma2.15. The actual canonical spectral basis,
native zero-boundary vector, faithful interval representative, unit coefficient
energy, exact projected physical identity and overlap bounds are constructed
together. ONE cutoff precedes the entire ORIGINAL complex endpoint ball
and may exceed ANY supplied prior cutoff. The final identity holds for ANY
normalized actual Dirichlet eigenfunction at the original same-index label. -/
theorem sourceLemma2_15_corrected (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ∀ n : ℕ+, N ≤ (n:ℕ) →
      let Q := sourceComplexHminusOne r hr q
      let z := sourceHillComplexLabels r hr q (2*(n:ℕ))
      let gamma := z-sourceHillComplexLabels r hr q (2*(n:ℕ)-1)
      let a := sourceOriginalComplexPotential r hr q hp
      ∃ f phi G : FourierLebesgueSpace (2:ℝ) 1 2, ∃ g : UnitDirichletH1,
      ∃ eta alpha beta : ℂ,
        singularHillOperator Q f = z • singularHillDomainInclusion f ∧
        ‖singularHillL2DomainInclusion f‖ = 1 ∧ ‖singularHillL2DomainInclusion phi‖ = 1 ∧
        (∃ b : OrthonormalBasis (Fin 2) ℂ (singularHillL2RieszProjection Q
            (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range,
          (b 0).val = singularHillL2DomainInclusion f ∧ (b 1).val = singularHillL2DomainInclusion phi) ∧
        (∃ u w : FourierLebesgueSpace (2:ℝ) (-r+2) ⊤, u.val = f.val ∧ w.val = phi.val) ∧
        singularHillOperator Q phi-z • singularHillDomainInclusion phi =
          -gamma • singularHillDomainInclusion phi+eta • singularHillDomainInclusion f ∧
        G = alpha • f+beta • phi ∧ ‖alpha‖^2+‖beta‖^2 = 1 ∧ ‖beta‖ ≤ 1 ∧
        ‖singularHillL2DomainInclusion G‖ = 1 ∧ ‖unitDirichletL2Inclusion g‖ = 1 ∧
        singularHillContinuousDomainInclusion G (0 : AddCircle (2:ℝ)) = 0 ∧
        singularHillContinuousDomainInclusion G ((1:ℝ) : AddCircle (2:ℝ)) = 0 ∧
        (∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x =
          singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))) ∧
        ∀ v : UnitDirichletH1,
          singularDirichletOperator Q v = originalComplexDirichletLabels a n • singularDirichletDomainInclusion v →
          ‖unitDirichletL2Inclusion v‖ = 1 →
          ∃ nu : ℂ, originalDirichletRieszProjection a n (unitDirichletL2Inclusion g) =
              nu • unitDirichletL2Inclusion v ∧ (1/2:ℝ) ≤ ‖nu‖ ∧ ‖nu‖ ≤ 3/2 ∧
            (nu*(originalComplexDirichletLabels a n-z)) • unitDirichletL2Inclusion v =
              (beta*eta) • originalDirichletRieszProjection a n (hillH1IntervalL2 f)-
                (beta*gamma) • originalDirichletRieszProjection a n (hillH1IntervalL2 phi) := by
  obtain ⟨NA,_,hmin,hbasis⟩ := sourceLemma2_13 r hr R Nmin
  obtain ⟨NB,_,hAB,hboundary⟩ := exists_uniform_sourcePeriodicDirichletBoundaryVector r hr R NA
  obtain ⟨NO,_,hBO,hoverlap⟩ := exists_uniform_sourcePeriodicDirichlet_overlap r hr R NB
  obtain ⟨NP,hNP,hOP,hparity⟩ := exists_uniform_sourcePeriodicRange_parity r hr R NO
  obtain ⟨ND,_,hcircles⟩ := exists_uniform_sourceEndpointDirichlet_sourceCircles r hr R
  let N := max NP ND
  refine ⟨N,hNP.trans (le_max_left _ _),by dsimp [N];omega,?_⟩
  intro q hq hp n hn Q z gamma a
  have hnP : NP ≤ (n:ℕ) := (le_max_left _ _).trans hn
  have hnD : ND ≤ (n:ℕ) := (le_max_right _ _).trans hn
  have hnO : NO ≤ (n:ℕ) := hOP.trans hnP
  have hnB : NB ≤ (n:ℕ) := hBO.trans hnO
  have hnA : NA ≤ (n:ℕ) := hAB.trans hnB
  obtain ⟨f,phi,eta,hf,hfn,hpn,⟨b,hb0,hb1⟩,hstrong,heta,_⟩ := hbasis q hq n hnA
  obtain ⟨G,g,hGn,hgn,hG,hG0,hG1,hGt,hsame,_⟩ := hboundary q hq hp n hnB
  obtain ⟨alpha,beta,hcoords,henergy,_,hbeta⟩ :=
    exists_singularHill_unit_spectral_coordinates Q _ _ f phi G b hb0 hb1 hG hGn
  have hfr : singularHillL2DomainInclusion f ∈ (singularHillL2RieszProjection Q
      (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range := by rw [← hb0];exact (b 0).property
  have hpr : singularHillL2DomainInclusion phi ∈ (singularHillL2RieszProjection Q
      (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range := by rw [← hb1];exact (b 1).property
  have hft := hillH1Continuous_translate_one_of_parity (n:ℤ) f
    (hparity q hq hp n hnP _ hfr)
  have hpt := hillH1Continuous_translate_one_of_parity (n:ℤ) phi
    (hparity q hq hp n hnP _ hpr)
  have hres : singularHillOperator Q G-z • singularHillDomainInclusion G =
      (beta*eta) • singularHillDomainInclusion f-(beta*gamma) • singularHillDomainInclusion phi := by
    rw [hcoords]
    exact singularHill_combination_residual Q z gamma eta alpha beta f phi hf heta
  refine ⟨f,phi,G,g,eta,alpha,beta,hf,hfn,hpn,⟨b,hb0,hb1⟩,hstrong,heta,hcoords,henergy,hbeta,
    hGn,hgn,hG0,hG1,hsame,?_⟩
  intro v hv hvn
  obtain ⟨nu,hnu,hlow,hhi⟩ := hoverlap q hq hp n hnO G g hGn hgn hG hG0 hsame v hv hvn
  have hc := (hcircles q hq hp n hnD).1
  refine ⟨nu,hnu,hlow,hhi,?_⟩
  exact singularDirichlet_projected_residual_of_signed_periodic Q (n:ℤ) z (beta*eta) (beta*gamma)
    (((Real.pi:ℂ)*(n:ℕ))^2) (originalComplexDirichletLabels a n) nu (n:ℝ)
    (by exact_mod_cast n.property.le) hc G f phi g v hGt hft hpt hsame hres hv hnu

end NLS.Articles.KdVPseudomeasures
