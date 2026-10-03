import NLS.ZakharovShabat.SourceDirichletComplexGradient

/-! # Canonical H¹ Dirichlet gradient coefficients near the real source locus

On one common open complex source domain, the actual canonical root
cotangent has both normalized physical Fourier coefficients. The Sobolev
representative and nonzero normalization are constructed within the proof.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A common neighborhood supplies the actual H¹ Dirichlet gradient at every
signed index, including nearby complex sources and the finite central block. -/
theorem exists_global_source_dirichlet_sobolev_normalized_gradient
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ W →
      ∀ (a : Domain 2), periodOnePotential φ = domainInclusion a →
      ∀ n : ℤ,
        let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n
        let L := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
          (CoeffPair.exponentInclusion h2p φ)
        classicalDirichletNormalization (classicalSobolevPotential a) z ≠ 0 ∧
          ∀ k : ℤ,
            L (CoeffPair.inlCLM (lp.single p k 1)) =
              unitFourierCoefficient (fun t => (classicalDirichletNormalizedGradient (classicalSobolevPotential a) z t).1) (-k) ∧
            L (CoeffPair.inrCLM (lp.single p k 1)) =
              unitFourierCoefficient (fun t => (classicalDirichletNormalizedGradient (classicalSobolevPotential a) z t).2) (-k) := by
  obtain ⟨W,hW,hreal,hgradient⟩ := exists_global_source_dirichlet_normalized_integral hp hp1 h2p
  refine ⟨W,hW,hreal,?_⟩
  intro φ hφ a ha n
  dsimp only
  obtain ⟨hQ,hint⟩ := hgradient φ hφ (classicalSobolevPotential a)
    (physicalBase_source_sobolev_compatibility φ a ha) n
  refine ⟨hQ,?_⟩
  intro k
  constructor
  · have hdir : CoeffPair.inlCLM (lp.single p k (1 : ℂ)) =
        CoeffPair.exponentInclusion h2p (CoeffPair.ofFinsupp (p := 2) (Finsupp.single k 1,0)) := by
      rw [CoeffPair.exponentInclusion_ofFinsupp]
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
    rw [hdir,hint _ _ (finiteSource_physical_compatibility (Finsupp.single k 1,0)).1]
    unfold unitFourierCoefficient
    rw [show -(2*(-k)) = 2*k by ring]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    simp [NLS.LinearVolterra.extend,projIcc_of_mem _ ht',finiteSourceCurve,BoundaryCondition.periodOnePair,polynomial]
  · have hdir : CoeffPair.inrCLM (lp.single p k (1 : ℂ)) =
        CoeffPair.exponentInclusion h2p (CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single k 1)) := by
      rw [CoeffPair.exponentInclusion_ofFinsupp]
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
    rw [hdir,hint _ _ (finiteSource_physical_compatibility (0,Finsupp.single k 1)).1]
    unfold unitFourierCoefficient
    rw [show -(2*(-k)) = 2*k by ring]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    simp [NLS.LinearVolterra.extend,projIcc_of_mem _ ht',finiteSourceCurve,BoundaryCondition.periodOnePair,polynomial]

end NLS.ZakharovShabat
