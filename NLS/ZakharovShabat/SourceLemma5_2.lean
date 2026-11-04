import NLS.ZakharovShabat.SourceFiniteGapFourthClosedFrequency

/-! # Article Lemma 5.2 for independently defined physical H₄ frequencies

Open actions use the negative physical action-reduction derivative.
Closed actions use the physical second amplitude derivative. Both have
the same exact weighted-moment formula and coordinate-independent value.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V X : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The physical H₄ frequency at every finite-gap action, including closed ones. -/
def finiteGapFourthFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) : ℂ :=
  if hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0 then D.finiteGapFourthClosedFrequency φ hf n hn
    else D.finiteGapFourthOpenFrequency φ hf n hn

/-- Lemma 5.2 with the exact three renormalization terms, at every selected index. -/
theorem finiteGap_lemma5_2
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) X u)
    (hs : SourcePsiNormalizedComplexExtension (by simp) (by norm_num) V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    D.finiteGapFourthFrequency φ hf n-
      6*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 2-
      (12*Real.pi:ℂ)*n*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1-
      (2*(n:ℂ)*Real.pi)^3 = -12*(∑' k : ℤ, (k:ℂ)*A.moment n k 2 φ.val) := by
  unfold finiteGapFourthFrequency
  split
  · exact (D.finiteGapFourthClosedFrequency_eq_limit_and_moments A hs φ hf n _).2.1
  · exact D.finiteGapFourthOpenFrequency_renormalized_eq_moments A hs φ hf n _

/-- The actual physical H₄ frequency does not depend on the Birkhoff chart. -/
theorem finiteGapFourthFrequency_independent_coordinates
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (D' : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    D.finiteGapFourthFrequency φ hf n = D'.finiteGapFourthFrequency φ hf n := by
  classical
  obtain ⟨Y,Z,_,_,_,_,v,hs,hlocal⟩ := exists_sourceAbelianMoment_localCharts (p := 2) (by simp) (by norm_num)
  choose L hL using hlocal
  let A : SourceAbelianMomentAtlas (by simp) (by norm_num) Y v := ⟨L⟩
  have hD := D.finiteGap_lemma5_2 A hs φ hf n
  have hD' := D'.finiteGap_lemma5_2 A hs φ hf n
  linear_combination hD-hD'

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
