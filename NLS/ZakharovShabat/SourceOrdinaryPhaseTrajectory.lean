import NLS.ZakharovShabat.SourceComplexBirkhoffMap
import NLS.ZakharovShabat.SourceOrdinaryMass
import NLS.ZakharovShabat.SourceMomentReality
import NLS.ZakharovShabat.SourceAbelianMomentSquaredGapAtlas

/-! # Ordinary NLS trajectories in actual complex Birkhoff coordinates

The ordinary frequencies add four times the physical mass to the
renormalized frequencies. For p ≤ 2 the correction is analytic and equals
the total spectral action. Opposite phase signs retain the actual actions.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
namespace SourceAbelianMomentAtlas

/-- The ordinary NLS frequency, including four times the physical mass. -/
def ordinaryPhaseFrequency (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) (n : ℤ) : ℝ :=
  (2*Real.pi*n)^2 + (A.renormalizedFrequency n φ.val).re + 4*sourceOrdinaryMass hp2 φ

/-- The real-valued frequency agrees with the actual complex spectral formula. -/
theorem ordinaryPhaseFrequency_complex (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (A.ordinaryPhaseFrequency hp2 φ n : ℂ) = (2*(Real.pi : ℂ)*n)^2+A.renormalizedFrequency n φ.val + 4*sourceOrdinaryComplexMass hp2 φ.val := by
  have hω : ((A.renormalizedFrequency n φ.val).re : ℂ) = A.renormalizedFrequency n φ.val := by
    apply Complex.ext <;> simp [A.renormalizedFrequency_im_eq_zero hs φ n]
  simp only [ordinaryPhaseFrequency,ofReal_add,ofReal_pow,ofReal_mul,ofReal_ofNat,ofReal_intCast,hω,sourceOrdinaryMass_complex]

/-- Coordinate continuity of the actual frequencies on the full real source space. -/
theorem continuous_ordinaryPhaseFrequency (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P) (hp2 : p ≤ 2) (n : ℤ) :
    Continuous (fun φ : realTypeSourceSubmodule p => A.ordinaryPhaseFrequency hp2 φ n) := by
  obtain ⟨U,_,_,hr,_,_,ha,_⟩ := A.exists_analytic_renormalizedFrequency hs hP hrealP
  apply continuous_iff_continuousAt.mpr
  intro φ
  exact (continuousAt_const.add (Complex.continuous_re.continuousAt.comp
    (((ha n φ.val (hr φ.property)).continuousAt).comp
      (realTypeSourceSubmodule p).subtypeL.continuous.continuousAt))).add
      (continuousAt_const.mul ((analytic_sourceOrdinaryMass hp2 φ (mem_univ _)).continuousAt))

/-- The global coordinate trajectory with the original source as initial parameter. -/
def ordinaryPhaseTrajectory (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) (τ : ℝ) : Coeff p × Coeff p :=
  Birkhoff.phaseFlow (A.ordinaryPhaseFrequency hp2 φ) τ (sourceComplexBirkhoffMap hp hp1 t φ.val)

@[simp] theorem ordinaryPhaseTrajectory_zero (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    A.ordinaryPhaseTrajectory t hp2 φ 0 = sourceComplexBirkhoffMap hp hp1 t φ.val :=
  Birkhoff.phaseFlow_zero _ _

/-- The first ordinary coordinate has the positive phase with the physical mass correction. -/
theorem ordinaryPhaseTrajectory_fst (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    (A.ordinaryPhaseTrajectory t hp2 φ τ).1 n =
      Complex.exp ((τ : ℂ)*I*((2*(Real.pi : ℂ)*n)^2+A.renormalizedFrequency n φ.val+4*sourceOrdinaryComplexMass hp2 φ.val)) *
        (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n := by
  rw [ordinaryPhaseTrajectory,Birkhoff.phaseFlow_fst,ofReal_mul,A.ordinaryPhaseFrequency_complex hs hp2]
  congr 2
  ring

/-- The second coordinate has precisely the opposite frequency sign. -/
theorem ordinaryPhaseTrajectory_snd (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    (A.ordinaryPhaseTrajectory t hp2 φ τ).2 n =
      Complex.exp (-(τ : ℂ)*I*((2*(Real.pi : ℂ)*n)^2+A.renormalizedFrequency n φ.val+4*sourceOrdinaryComplexMass hp2 φ.val)) *
        (sourceComplexBirkhoffMap hp hp1 t φ.val).2 n := by
  rw [ordinaryPhaseTrajectory,Birkhoff.phaseFlow_snd,ofReal_mul,ofReal_neg,A.ordinaryPhaseFrequency_complex hs hp2]
  congr 2
  ring

variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every trajectory retains the actual original spectral actions. -/
theorem ordinaryPhaseTrajectory_action (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    (A.ordinaryPhaseTrajectory t hp2 φ τ).1 n*(A.ordinaryPhaseTrajectory t hp2 φ τ).2 n =
      sourceComplexAction hp hp1 n φ.val :=
  (Birkhoff.phaseFlow_action _ _ _ _).trans (D.complex_map_action φ.val (D.real_subset φ.property) n)

/-- Reality is preserved for every real time and every real source. -/
theorem ordinaryPhaseTrajectory_real (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    Birkhoff.IsConjugatePair (A.ordinaryPhaseTrajectory t hp2 φ τ) :=
  Birkhoff.phaseFlow_real _ _ _ (D.complex_map_real φ)

/-- Joint time-source continuity holds in the full finite-exponent sequence norm. -/
theorem continuous_ordinaryPhaseTrajectory (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2) :
    Continuous (fun x : ℝ × realTypeSourceSubmodule p => A.ordinaryPhaseTrajectory t hp2 x.2 x.1) :=
  Birkhoff.continuous_phaseFlow_family hp (A.ordinaryPhaseFrequency hp2)
    (fun φ => sourceComplexBirkhoffMap hp hp1 t φ.val)
    (A.continuous_ordinaryPhaseFrequency hs hP hrealP hp2) D.continuous_complex_map_real

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
