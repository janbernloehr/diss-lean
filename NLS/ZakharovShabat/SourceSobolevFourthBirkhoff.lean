import NLS.ZakharovShabat.SourceSobolevFourthHamiltonian
import NLS.ZakharovShabat.SourceFiniteGapSobolevOpening
import NLS.ZakharovShabat.SourceFiniteGapFourthClosedFrequency

/-! # The physical H₄ in the full fractional Birkhoff chart

The global weighted inverse transports the independently constructed physical
H₄ to every H^(3/2) Birkhoff target. The native opening line agrees with the
physical finite-gap hierarchy at every amplitude, including the closed endpoint.
No action-only factorization or full-domain frequency identity is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Real rectangular Birkhoff coordinates with the exact H^(3/2) weight. -/
abbrev FourthSobolevBirkhoffTarget := WithLp (2:ℝ≥0∞)
  (WeightedRealCoeff (sourceFrequencyWeight fourthSobolevSpectralWeight) 2 ×
    WeightedRealCoeff (sourceFrequencyWeight fourthSobolevSpectralWeight) 2)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Pull back the physical fractional Hamiltonian by the actual global weighted inverse. -/
def sobolevFourthBirkhoffHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z : FourthSobolevBirkhoffTarget) : ℂ :=
  sourceSobolevFourthHamiltonian
    ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm z)

/-- The same independently constructed physical Hamiltonian in its real scalar codomain. -/
def realSobolevFourthBirkhoffHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z : FourthSobolevBirkhoffTarget) : ℝ :=
  sourceRealSobolevFourthHamiltonian
    ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm z)

/-- Its physical scalar inclusion is exact at every fractional Birkhoff target. -/
theorem realSobolevFourthBirkhoffHamiltonian_complex
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z : FourthSobolevBirkhoffTarget) :
    (D.realSobolevFourthBirkhoffHamiltonian z : ℂ) = D.sobolevFourthBirkhoffHamiltonian z :=
  sourceRealSobolevFourthHamiltonian_complex _

/-- Physical H₄ is analytic throughout the full native fractional target. -/
theorem analyticOnNhd_sobolevFourthBirkhoffHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) :
    AnalyticOnNhd ℝ D.sobolevFourthBirkhoffHamiltonian univ := by
  intro z hz
  exact (analyticOnNhd_sourceSobolevFourthHamiltonian _ (mem_univ _)).comp
    (D.originalWeightedRealSobolevEquiv_symm_analytic (by rfl) (3/2) (by norm_num) z hz)

/-- Real analyticity also holds into the actual real scalar codomain. -/
theorem analyticOnNhd_realSobolevFourthBirkhoffHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) :
    AnalyticOnNhd ℝ D.realSobolevFourthBirkhoffHamiltonian univ := by
  intro z hz
  exact (analyticOnNhd_sourceRealSobolevFourthHamiltonian _ (mem_univ _)).comp
    (D.originalWeightedRealSobolevEquiv_symm_analytic (by rfl) (3/2) (by norm_num) z hz)

/-- The original weighted Birkhoff map recovers the physical source value. -/
theorem sobolevFourthBirkhoffHamiltonian_map
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) :
    D.sobolevFourthBirkhoffHamiltonian (D.originalWeightedRealMap fourthSobolevSpectralWeight a) =
      sourceSobolevFourthHamiltonian a := by
  exact congrArg sourceSobolevFourthHamiltonian
    ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm_apply_apply a)

/-- The actual physical Hamiltonian along the raw one-mode amplitude line. -/
def sobolevFourthOpeningHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) (t : ℝ) : ℂ :=
  sourceSobolevFourthHamiltonian (D.sobolevGapOpening (by rfl) (3/2) (by norm_num) a n t)

/-- The raw weighted amplitude line is the same curve in the Birkhoff target. -/
theorem sobolevFourthOpeningHamiltonian_eq_birkhoff
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) (t : ℝ) :
    D.sobolevFourthOpeningHamiltonian a n t = D.sobolevFourthBirkhoffHamiltonian
      (NLS.Birkhoff.weightedActionOpening (sourceFrequencyWeight fourthSobolevSpectralWeight)
        (D.originalWeightedRealMap fourthSobolevSpectralWeight a) n t) := rfl

/-- The physical fractional Hamiltonian is analytic along the entire opening line. -/
theorem analyticOnNhd_sobolevFourthOpeningHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) :
    AnalyticOnNhd ℝ (D.sobolevFourthOpeningHamiltonian a n) univ := by
  intro t ht
  exact (analyticOnNhd_sourceSobolevFourthHamiltonian _ (mem_univ _)).comp
    (D.analyticOnNhd_sobolevGapOpening (by rfl) (3/2) (by norm_num) a n t ht)

private theorem fourth_finiteGapHamiltonian_congr
    (φ ψ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hg : ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (h : φ = ψ) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 4 =
      sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) ψ hg 4 := by
  subst ψ
  rfl

/-- On every finite-gap source the complete amplitude function equals the
independent physical Riccati H₄ function, not just its value at zero. -/
theorem sobolevFourthOpeningHamiltonian_eq_finiteGap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈
      sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    D.sobolevFourthOpeningHamiltonian a n =
      D.physicalGapOpeningHamiltonian (originalWeightedRealSource fourthSobolevSpectralWeight a) hf n 4 := by
  funext t
  have he : originalWeightedRealSource fourthSobolevSpectralWeight
      (D.sobolevGapOpening (by rfl) (3/2) (by norm_num) a n t) =
      D.hilbertGapOpening (originalWeightedRealSource fourthSobolevSpectralWeight a) n t :=
    D.originalWeightedRealSource_sobolevGapOpening_hilbert (3/2) (by norm_num) a n t
  have hfinite : originalWeightedRealSource fourthSobolevSpectralWeight
      (D.sobolevGapOpening (by rfl) (3/2) (by norm_num) a n t) ∈
      sourceFiniteGapLocus (by simp) (by norm_num) := by
    rw [he]
    exact D.hilbertGapOpening_mem_finiteGap _ hf n t
  exact (sourceSobolevFourthHamiltonian_eq_finiteGap _ hfinite).trans
    (fourth_finiteGapHamiltonian_congr _ _ hfinite
      (D.hilbertGapOpening_mem_finiteGap _ hf n t) he)

/-- The native fractional second derivative at a closed finite-gap action is
exactly the independently defined physical closed H₄ frequency. -/
theorem second_deriv_sobolevFourthOpeningHamiltonian_finiteGap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈
      sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
      (periodOnePotential_mem _) n = 0) :
    deriv (deriv (D.sobolevFourthOpeningHamiltonian a n)) 0 =
      D.finiteGapFourthClosedFrequency (originalWeightedRealSource fourthSobolevSpectralWeight a) hf n hn := by
  rw [D.sobolevFourthOpeningHamiltonian_eq_finiteGap a hf n]
  rfl

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
