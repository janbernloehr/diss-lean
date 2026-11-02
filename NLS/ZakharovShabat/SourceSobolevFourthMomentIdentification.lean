import NLS.ZakharovShabat.SourceSobolevFourthFrequencyRegularity
import NLS.ZakharovShabat.SourceSobolevFourthLowerHamiltonians
import NLS.ZakharovShabat.SourceWeightedFiniteGapEquality

/-! # The full physical H₄ action frequencies satisfy the second-moment identity

The frequency is independently defined by physical Hamiltonian derivatives.
Its verified action-factor regularity, the independently calibrated lower
Hamiltonians, and native weighted finite-gap approximation extend Lemma 5.2
to every original H^(3/2) source, including every closed selected action.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V X : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The physical action frequency with exactly the article's three
renormalization terms, using independently defined mass and momentum. -/
def normalizedSobolevFourthFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) : ℂ :=
  D.sobolevFourthFrequency a n - 6*sourceFourthSobolevMomentum a -
    (12*Real.pi:ℂ)*n*sourceFourthSobolevMass a - (2*(n:ℂ)*Real.pi)^3

/-- The independently normalized physical frequency is real analytic on
its whole original fractional source, including collapsed gaps. -/
theorem analyticAt_normalizedSobolevFourthFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) :
    AnalyticAt ℝ (fun b => D.normalizedSobolevFourthFrequency b n) a :=
  (((D.analyticAt_sobolevFourthFrequency a n).sub
    (analyticAt_const.mul (analyticAt_sourceFourthSobolevMomentum a))).sub
      (analyticAt_const.mul (analyticAt_sourceFourthSobolevMass a))).sub analyticAt_const

/-- Lemma 5.2 on the full original physical H₄ domain. The moment analyticity
hypothesis is supplied by the constructed article atlas; no physical
frequency equality or approximation hypothesis is assumed. -/
theorem normalizedSobolevFourthFrequency_eq_moments
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) X u)
    (hs : SourcePsiNormalizedComplexExtension (by simp) (by norm_num) V u)
    (U : Set (CoeffPair 2)) (hreal : realTypeSourceLocus 2 ⊆ U)
    (han : ∀ n : ℤ, AnalyticOnNhd ℂ (fun ψ => -12*(∑' k : ℤ, (k:ℂ)*A.moment n k 2 ψ)) U)
    (a : NativeFourthSobolevSource) (n : ℤ) :
    D.normalizedSobolevFourthFrequency a n =
      -12*(∑' k : ℤ, (k:ℂ)*A.moment n k 2
        (originalWeightedRealSource fourthSobolevSpectralWeight a).val) := by
  let L : NativeFourthSobolevSource →L[ℝ] CoeffPair 2 :=
    ((originalWeightedSourceCLM (p := 2) fourthSobolevSpectralWeight).restrictScalars ℝ).comp
      (weightedRealSourceSubmodule (p := 2) fourthSobolevSpectralWeight).subtypeL
  let g : NativeFourthSobolevSource → ℂ :=
    fun b => -12*(∑' k : ℤ, (k:ℂ)*A.moment n k 2 (L b))
  have hf : Continuous (fun b => D.normalizedSobolevFourthFrequency b n) :=
    continuous_iff_continuousAt.mpr fun b => (D.analyticAt_normalizedSobolevFourthFrequency b n).continuousAt
  have hL (b : NativeFourthSobolevSource) : L b =
      (originalWeightedRealSource fourthSobolevSpectralWeight b).val := rfl
  have hg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro b
    have hm : AnalyticAt ℂ (fun ψ => -12*(∑' k : ℤ, (k:ℂ)*A.moment n k 2 ψ)) (L b) := by
      rw [hL]
      exact han n _ (hreal (originalWeightedRealSource fourthSobolevSpectralWeight b).property)
    exact ((hm.restrictScalars (𝕜 := ℝ)).comp (L.analyticAt b)).continuousAt
  apply eq_of_continuous_weighted_finiteGap (by simp) (by norm_num) fourthSobolevSpectralWeight
    (fun b => D.normalizedSobolevFourthFrequency b n) g hf hg ?_ a
  intro b hb
  unfold normalizedSobolevFourthFrequency
  rw [D.sobolevFourthFrequency_eq_finiteGap b hb n,
    sourceFourthSobolevMass_eq_finiteGap b hb,sourceFourthSobolevMomentum_eq_finiteGap b hb]
  exact D.finiteGap_lemma5_2 A hs (originalWeightedRealSource fourthSobolevSpectralWeight b) hb n

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
