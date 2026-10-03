import NLS.ZakharovShabat.SourceDirichletComplexFourierGradient
import NLS.ZakharovShabat.ClassicalDirichletGradientFourier
import NLS.SequenceSpaces.SourceCotangentNormBound
import NLS.Fourier.IntervalCoefficientLinearity

/-! # The genuine Dirichlet derivative error and its physical Fourier bound

On a common complex neighborhood of the real source locus, subtracting the
actual derivative at zero subtracts exactly the normalized free waves.
The physical Fourier coefficients occur at reversed indices. Hölder
duality then controls the actual source operator norm.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The H¹ representative of the zero potential is the zero curve. -/
@[simp] theorem classicalSobolevPotential_zero : classicalSobolevPotential (0 : Domain 2) = 0 := by
  apply norm_le_zero_iff.mp
  simpa using norm_classicalSobolevPotential_le (0 : Domain 2)

/-- One domain identifies both Fourier components of the actual derivative
error against the zero-source derivative at every signed root. -/
theorem exists_global_source_dirichlet_fderiv_error_fourier
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    {q : ℝ≥0∞} (hq : 1 < q) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ W →
      ∀ (a : Domain 2), periodOnePotential φ = domainInclusion a → ∀ n k : ℤ,
        let μ := fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
        let L := fderiv ℂ μ (CoeffPair.exponentInclusion h2p φ)-fderiv ℂ μ 0
        L (CoeffPair.inlCLM (lp.single p k 1)) =
          classicalDirichletGradientFourierCoefficients hq (classicalSobolevPotential a)
            (μ (CoeffPair.exponentInclusion h2p φ)) ((Real.pi : ℂ)*n) (ContinuousLinearMap.fst ℝ ℂ ℂ) (-k) ∧
        L (CoeffPair.inrCLM (lp.single p k 1)) =
          classicalDirichletGradientFourierCoefficients hq (classicalSobolevPotential a)
            (μ (CoeffPair.exponentInclusion h2p φ)) ((Real.pi : ℂ)*n) (ContinuousLinearMap.snd ℝ ℂ ℂ) (-k) := by
  obtain ⟨W,hW,hreal,hgradient⟩ := exists_global_source_dirichlet_sobolev_normalized_gradient hp hp1 h2p
  refine ⟨W,hW,hreal,?_⟩
  have hzero : CoeffPair.exponentInclusion h2p (0 : CoeffPair 2) ∈ W := by
    simpa using hreal (show (0 : CoeffPair p) ∈ realTypeSourceLocus p by intro k; simp)
  have hcoeff (f : ℝ → ℂ) (k : ℤ) : intervalFourierCoefficient 1 f k = unitFourierCoefficient f k := by
    rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),unitFourierCoefficient_eq_fourierCoeffOn]
  intro φ hφ a ha n k
  dsimp only
  have hd := (hgradient φ hφ a ha n).2 k
  have h0 := (hgradient 0 hzero 0 (by simp) n).2 k
  simp only [map_zero,canonicalPeriodOneBoundaryRoots_zero,classicalSobolevPotential_zero] at h0
  have hactual := (contDiff_classicalDirichletNormalizedGradient (classicalSobolevPotential a)
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n)).continuous
  have hfree := (contDiff_classicalDirichletNormalizedGradient 0 ((Real.pi : ℂ)*n)).continuous
  constructor
  · rw [sub_apply,hd.1,h0.1]
    change _ = intervalFourierCoefficient 1
      (fun t => (classicalDirichletNormalizedGradient (classicalSobolevPotential a)
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n) t).1-
        (classicalDirichletNormalizedGradient 0 ((Real.pi : ℂ)*n) t).1) (-k)
    rw [intervalFourierCoefficient_sub 1 _ _ hactual.fst hfree.fst,hcoeff,hcoeff]
  · rw [sub_apply,hd.2,h0.2]
    change _ = intervalFourierCoefficient 1
      (fun t => (classicalDirichletNormalizedGradient (classicalSobolevPotential a)
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n) t).2-
        (classicalDirichletNormalizedGradient 0 ((Real.pi : ℂ)*n) t).2) (-k)
    rw [intervalFourierCoefficient_sub 1 _ _ hactual.snd hfree.snd,hcoeff,hcoeff]

/-- Physical conjugate Fourier norms bound the genuine source derivative
error, with no simplicity or candidate-gradient premise at the source. -/
theorem exists_global_source_dirichlet_fderiv_error_fourier_bound
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (hq : 1 < q) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ W →
      ∀ (a : Domain 2), periodOnePotential φ = domainInclusion a → ∀ n : ℤ,
        let μ := fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
        ‖fderiv ℂ μ (CoeffPair.exponentInclusion h2p φ)-fderiv ℂ μ 0‖ ≤
          ‖classicalDirichletGradientFourierCoefficients hq (classicalSobolevPotential a)
            (μ (CoeffPair.exponentInclusion h2p φ)) ((Real.pi : ℂ)*n) (ContinuousLinearMap.fst ℝ ℂ ℂ)‖+
          ‖classicalDirichletGradientFourierCoefficients hq (classicalSobolevPotential a)
            (μ (CoeffPair.exponentInclusion h2p φ)) ((Real.pi : ℂ)*n) (ContinuousLinearMap.snd ℝ ℂ ℂ)‖ := by
  obtain ⟨W,hW,hreal,hcoeff⟩ := exists_global_source_dirichlet_fderiv_error_fourier hp hp1 h2p hq
  refine ⟨W,hW,hreal,?_⟩
  intro φ hφ a ha n
  dsimp only
  simpa only [LinearIsometryEquiv.norm_map] using CoeffPair.norm_cotangent_le_of_single hp _
    (Coeff.reflection (classicalDirichletGradientFourierCoefficients hq (classicalSobolevPotential a)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n)
      ((Real.pi : ℂ)*n) (ContinuousLinearMap.fst ℝ ℂ ℂ)))
    (Coeff.reflection (classicalDirichletGradientFourierCoefficients hq (classicalSobolevPotential a)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n)
      ((Real.pi : ℂ)*n) (ContinuousLinearMap.snd ℝ ℂ ℂ)))
    (fun k => (hcoeff φ hφ a ha n k).1) (fun k => (hcoeff φ hφ a ha n k).2)

end NLS.ZakharovShabat
