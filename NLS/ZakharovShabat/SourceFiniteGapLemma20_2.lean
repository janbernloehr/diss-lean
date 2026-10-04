import NLS.ZakharovShabat.SourceFiniteGapClosedFrequency

/-! # Lemma 20.2 for physical finite-gap Hilbert frequencies

At an open action use the physical first action derivative; at a closed
action use the physical second amplitude derivative. Both cases have the
same moment formula, and the resulting frequency is independent of the
Birkhoff realization. No frequency is defined using that formula.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V X : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The physical finite-gap frequency, including collapsed selected actions. -/
def finiteGapFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) : ℂ :=
  if hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0 then D.finiteGapClosedFrequency φ hf n hn
    else D.finiteGapOpenFrequency φ hf n hn

/-- Lemma 20.2 for every selected index, including closed gaps. -/
theorem finiteGap_lemma20_2
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) X u)
    (hs : SourcePsiNormalizedComplexExtension (by simp) (by norm_num) V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    D.finiteGapFrequency φ hf n -
      4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 - (2*(n : ℂ)*Real.pi)^2 =
        -(4/(2*Real.pi) : ℂ)*(∑' k : ℤ, A.moment n k 2 φ.val) := by
  unfold finiteGapFrequency
  split
  · exact (D.finiteGapClosedFrequency_eq_limit_and_moments A hs φ hf n _).2.1
  · exact D.finiteGapOpenFrequency_renormalized_eq_moments A hs φ hf n _

/-- The physical frequency does not depend on the chosen Birkhoff data. -/
theorem finiteGapFrequency_independent_coordinates
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (D' : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    D.finiteGapFrequency φ hf n = D'.finiteGapFrequency φ hf n := by
  classical
  obtain ⟨Y,Z,_,_,_,_,v,hs,hlocal⟩ := exists_sourceAbelianMoment_localCharts (p := 2) (by simp) (by norm_num)
  choose L hL using hlocal
  let A : SourceAbelianMomentAtlas (by simp) (by norm_num) Y v := ⟨L⟩
  have hD := D.finiteGap_lemma20_2 A hs φ hf n
  have hD' := D'.finiteGap_lemma20_2 A hs φ hf n
  linear_combination hD-hD'

/-- All gaps are closed at the zero source, yet the physical frequency
retains the nonzero free dispersion `(2*n*pi)^2`. -/
theorem finiteGapFrequency_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (hf : (0 : realTypeSourceSubmodule 2) ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    D.finiteGapFrequency 0 hf n = (2*(n : ℂ)*Real.pi)^2 := by
  classical
  obtain ⟨Y,Z,_,_,_,_,v,hs,hlocal⟩ := exists_sourceAbelianMoment_localCharts (p := 2) (by simp) (by norm_num)
  choose L hL using hlocal
  let A : SourceAbelianMomentAtlas (by simp) (by norm_num) Y v := ⟨L⟩
  have he := D.finiteGap_lemma20_2 A hs 0 hf n
  have hgap (k : ℤ) : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (0 : CoeffPair 2)) (periodOnePotential_mem 0) k = 0 := by
    simpa only [map_zero] using canonicalPeriodicGap_zero (p := 2) (by simp) (by norm_num) k
  have hmom (k : ℤ) : A.moment n k 2 0 = 0 :=
    A.moment_succ_of_collapsed 0 (A.realType_subset_domain (0 : realTypeSourceSubmodule 2).property) n k (hgap k) 1
  have hmass : sourceHilbertMass (0 : CoeffPair 2) = 0 := by
    rw [sourceHilbertMass_eq_half_norm_sq_of_realType 0 (0 : realTypeSourceSubmodule 2).property]
    norm_num
  rw [sourceFiniteGapNLSHamiltonian_one_eq_mass] at he
  simp only [Submodule.coe_zero,hmass,mul_zero,sub_zero,hmom,tsum_zero] at he
  exact sub_eq_zero.mp he

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
