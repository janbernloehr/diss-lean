import NLS.Articles.KdVPseudomeasures.PeriodicDirichletIdentity
import NLS.Articles.KdVPseudomeasures.DirichletProjectionNorm
import NLS.KdV.HillH1IntervalNorm
import NLS.FunctionalAnalysis.ProjectedResidualBound

/-! The full complex original midpoint estimate from the corrected
ACTUAL projected identity, the source eta bound and exact physical norms. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat

/-- Literal original positive-index periodic midpoint minus Dirichlet label. -/
def sourceComplexDirichletMidpoint (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) (n : ℕ+) : ℂ :=
  (sourceHillComplexLabels r hr q (2*(n:ℕ))+sourceHillComplexLabels r hr q (2*(n:ℕ)-1))/2-
    originalComplexDirichletLabels (sourceOriginalComplexPotential r hr q hp) n

/-- ONE original endpoint ball cutoff bounds the ACTUAL complex midpoint
by the ACTUAL canonical gap and both ACTUAL off-diagonal couplings.
No reality, gap nonvanishing, supplied norm or operator comparison is assumed. -/
theorem exists_uniform_sourceComplexMidpoint_coupling_bound
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ∀ n : ℕ+, N ≤ (n:ℕ) →
        let z := sourceHillComplexLabels r hr q (2*(n:ℕ))
        let gamma := z-sourceHillComplexLabels r hr q (2*(n:ℕ)-1)
        ‖sourceComplexDirichletMidpoint r hr q hp n‖ ≤
          128*(‖gamma‖+
            ‖endpointUpperCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q,z)‖+
            ‖endpointLowerCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q,z)‖) := by
  obtain ⟨NE,_,hmin,hE⟩ := exists_uniform_sourcePeriodicEta_bound r hr R Nmin
  obtain ⟨NI,_,hEI,hI⟩ := sourceLemma2_15_corrected r hr R NE
  obtain ⟨NR,hNR,hIR,hParity⟩ := exists_uniform_sourcePeriodicRange_parity r hr R NI
  obtain ⟨NP,_,hP⟩ := exists_uniform_sourceDirichletProjection_norm_le_three r hr R
  refine ⟨max NR NP,hNR.trans (le_max_left _ _),by omega,?_⟩
  intro q hq hp n hn z gamma
  have hnR : NR ≤ (n:ℕ) := (le_max_left _ _).trans hn
  have hnI : NI ≤ (n:ℕ) := hIR.trans hnR
  have hnE : NE ≤ (n:ℕ) := hEI.trans hnI
  obtain ⟨f,phi,G,g,eta,alpha,beta,hf,hfn,hpn,⟨b,hb0,hb1⟩,_,heta,_,_,hbeta,_,_,_,_,_,hV⟩ :=
    hI q hq hp n hnI
  let a := sourceOriginalComplexPotential r hr q hp
  obtain ⟨v,hv,hvn,_⟩ := exists_normalized_originalComplexDirichlet_eigenfunction a n
  obtain ⟨nu,_,hnu,_,hres⟩ := hV v hv hvn
  have hfr : singularHillL2DomainInclusion f ∈ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q)
      (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range := by rw [← hb0];exact (b 0).property
  have hpr : singularHillL2DomainInclusion phi ∈ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q)
      (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range := by rw [← hb1];exact (b 1).property
  have hfnI : ‖hillH1IntervalL2 f‖ = 1 :=
    (norm_hillH1IntervalL2_of_parity (n:ℤ) f (hParity q hq hp n hnR _ hfr)).trans hfn
  have hpnI : ‖hillH1IntervalL2 phi‖ = 1 :=
    (norm_hillH1IntervalL2_of_parity (n:ℤ) phi (hParity q hq hp n hnR _ hpr)).trans hpn
  have hsep := NLS.FunctionalAnalysis.norm_separation_of_projected_residual
    (originalDirichletRieszProjection a n) (hillH1IntervalL2 f) (hillH1IntervalL2 phi)
    (unitDirichletL2Inclusion v) (originalComplexDirichletLabels a n) z beta eta gamma nu 3
    (hP q hq hp n ((le_max_right _ _).trans hn)) hfnI hpnI hvn hbeta hnu hres
  have hetaB := hE q hq n hnE f phi hfn hpn hf eta heta
  have hid : (z+sourceHillComplexLabels r hr q (2*(n:ℕ)-1))/2-originalComplexDirichletLabels a n =
      -(originalComplexDirichletLabels a n-z)-gamma/2 := by dsimp [gamma];ring
  change ‖(z+sourceHillComplexLabels r hr q (2*(n:ℕ)-1))/2-originalComplexDirichletLabels a n‖ ≤ _
  rw [hid]
  have ht := norm_sub_le (-(originalComplexDirichletLabels a n-z)) (gamma/2)
  simp only [norm_neg,norm_div,Complex.norm_ofNat] at ht
  dsimp only [z,gamma] at hsep hetaB ⊢
  nlinarith [norm_nonneg (sourceHillComplexLabels r hr q (2*(n:ℕ))-sourceHillComplexLabels r hr q (2*(n:ℕ)-1)),
    norm_nonneg (endpointUpperCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q,z)),
    norm_nonneg (endpointLowerCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q,z))]

end NLS.Articles.KdVPseudomeasures
