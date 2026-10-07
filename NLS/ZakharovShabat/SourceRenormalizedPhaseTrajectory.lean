import NLS.ZakharovShabat.SourceComplexBirkhoffMap
import NLS.ZakharovShabat.SourceMomentReality
import NLS.ZakharovShabat.SourceAbelianMomentSquaredGapAtlas

/-! # Renormalized NLS trajectories in actual complex Birkhoff coordinates

At every finite source exponent above one, the actual spectral frequencies
produce global-in-time coordinate trajectories. The full time-source map is
continuous in the sequence norm, preserves the original actions and the
complex-coordinate reality condition. Source-space inversion and analytic
dependence of compact-time trajectories are separate subsequent steps.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
namespace SourceAbelianMomentAtlas

/-- The real renormalized NLS frequency, with the physical period-one quadratic term. -/
def phaseFrequency (A : SourceAbelianMomentAtlas hp hp1 W s)
    (φ : realTypeSourceSubmodule p) (n : ℤ) : ℝ :=
  (2*Real.pi*n)^2 + (A.renormalizedFrequency n φ.val).re

/-- The real-valued frequency agrees with the actual complex spectral formula. -/
theorem phaseFrequency_complex (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (A.phaseFrequency φ n : ℂ) = (2*(Real.pi : ℂ)*n)^2+A.renormalizedFrequency n φ.val := by
  have hω : ((A.renormalizedFrequency n φ.val).re : ℂ) = A.renormalizedFrequency n φ.val := by
    apply Complex.ext <;> simp [A.renormalizedFrequency_im_eq_zero hs φ n]
  simp only [phaseFrequency,ofReal_add,ofReal_pow,ofReal_mul,ofReal_ofNat,ofReal_intCast,hω]

/-- Coordinate continuity of the actual frequencies on the full real source space. -/
theorem continuous_phaseFrequency (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P) (n : ℤ) :
    Continuous (fun φ : realTypeSourceSubmodule p => A.phaseFrequency φ n) := by
  obtain ⟨U,_,_,hr,_,_,ha,_⟩ := A.exists_analytic_renormalizedFrequency hs hP hrealP
  apply continuous_iff_continuousAt.mpr
  intro φ
  exact continuousAt_const.add (Complex.continuous_re.continuousAt.comp
    (((ha n φ.val (hr φ.property)).continuousAt).comp
      (realTypeSourceSubmodule p).subtypeL.continuous.continuousAt))

/-- The global coordinate trajectory with the original source as initial parameter. -/
def renormalizedPhaseTrajectory (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) : Coeff p × Coeff p :=
  Birkhoff.phaseFlow (A.phaseFrequency φ) τ (sourceComplexBirkhoffMap hp hp1 t φ.val)

@[simp] theorem renormalizedPhaseTrajectory_zero (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (φ : realTypeSourceSubmodule p) :
    A.renormalizedPhaseTrajectory t φ 0 = sourceComplexBirkhoffMap hp hp1 t φ.val :=
  Birkhoff.phaseFlow_zero _ _

/-- The first coordinate is exactly equation (4.14), with the actual moment-sum frequency. -/
theorem renormalizedPhaseTrajectory_fst (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    (A.renormalizedPhaseTrajectory t φ τ).1 n =
      Complex.exp ((τ : ℂ)*I*((2*(Real.pi : ℂ)*n)^2+A.renormalizedFrequency n φ.val)) *
        (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n := by
  rw [renormalizedPhaseTrajectory,Birkhoff.phaseFlow_fst,ofReal_mul,A.phaseFrequency_complex hs]
  congr 2
  ring

/-- The second coordinate has precisely the opposite frequency sign. -/
theorem renormalizedPhaseTrajectory_snd (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    (A.renormalizedPhaseTrajectory t φ τ).2 n =
      Complex.exp (-(τ : ℂ)*I*((2*(Real.pi : ℂ)*n)^2+A.renormalizedFrequency n φ.val)) *
        (sourceComplexBirkhoffMap hp hp1 t φ.val).2 n := by
  rw [renormalizedPhaseTrajectory,Birkhoff.phaseFlow_snd,ofReal_mul,ofReal_neg,A.phaseFrequency_complex hs]
  congr 2
  ring

variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every trajectory retains the actual original spectral actions. -/
theorem renormalizedPhaseTrajectory_action (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    (A.renormalizedPhaseTrajectory t φ τ).1 n*(A.renormalizedPhaseTrajectory t φ τ).2 n =
      sourceComplexAction hp hp1 n φ.val :=
  (Birkhoff.phaseFlow_action _ _ _ _).trans (D.complex_map_action φ.val (D.real_subset φ.property) n)

/-- Reality is preserved for every real time and every real source. -/
theorem renormalizedPhaseTrajectory_real (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    Birkhoff.IsConjugatePair (A.renormalizedPhaseTrajectory t φ τ) :=
  Birkhoff.phaseFlow_real _ _ _ (D.complex_map_real φ)

/-- Joint time-source continuity holds in the full finite-exponent sequence norm. -/
theorem continuous_renormalizedPhaseTrajectory (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    Continuous (fun x : ℝ × realTypeSourceSubmodule p => A.renormalizedPhaseTrajectory t x.2 x.1) :=
  Birkhoff.continuous_phaseFlow_family hp A.phaseFrequency
    (fun φ => sourceComplexBirkhoffMap hp hp1 t φ.val)
    (A.continuous_phaseFrequency hs hP hrealP) D.continuous_complex_map_real

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
