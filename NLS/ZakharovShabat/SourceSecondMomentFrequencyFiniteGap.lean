import NLS.ZakharovShabat.SourceSecondMomentFrequencyAnalytic
import NLS.ZakharovShabat.SourceFiniteGapAnalyticUniqueness
import NLS.ZakharovShabat.SourceFiniteGapLemma20_2

/-! # Theorem 20.4 and physical finite-gap Hilbert frequencies

The analytic moment sum agrees with the independently defined physical
frequency after subtracting mass and free dispersion. Finite-gap density
and the real-form identity principle prove uniqueness on the connected
domain. The physical identification in this file is for p = 2.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ZakharovShabat

namespace SourceAbelianMomentAtlas
variable {W₀ B W X V : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The moment-sum frequency agrees with the physical finite-gap
frequency at open and closed actions, with the exact renormalization. -/
theorem renormalizedFrequency_eq_physical_finiteGap
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) X u)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (hs : SourcePsiNormalizedComplexExtension (by simp) (by norm_num) V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    A.renormalizedFrequency n φ.val = D.finiteGapFrequency φ hf n -
      4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 - (2*(n:ℂ)*Real.pi)^2 :=
  (D.finiteGap_lemma20_2 A hs φ hf n).symm

/-- The Hilbert version of Theorem 20.4: absolute and local uniform
convergence, complex and real analyticity, physical finite-gap agreement,
and uniqueness of the analytic extension on a connected domain. -/
theorem exists_hilbert_theorem20_4
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) X u)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) V u)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2 ⊆ V) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧
      U ⊆ A.domain ∩ V ∧
      (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k => ‖A.moment n k 2 ψ‖)) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (A.renormalizedFrequency n) U ∧
        AnalyticOnNhd ℝ (A.renormalizedFrequency n) U) ∧
      (∀ φ ∈ U, ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧ ∀ n : ℤ,
        TendstoUniformlyOn
          (fun (N : ℕ) ψ => -(4/(2*Real.pi):ℂ)*
            ∑ k ∈ Finset.Icc (-(N : ℤ)) N, A.moment n k 2 ψ)
          (A.renormalizedFrequency n) atTop T) ∧
      (∀ (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ),
        A.renormalizedFrequency n φ.val = D.finiteGapFrequency φ hf n -
          4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 - (2*(n:ℂ)*Real.pi)^2) ∧
      ∀ (n : ℤ) (F : CoeffPair 2 → ℂ), AnalyticOnNhd ℂ F U →
        (∀ (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)),
          F φ.val = D.finiteGapFrequency φ hf n -
            4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 - (2*(n:ℂ)*Real.pi)^2) →
        EqOn F (A.renormalizedFrequency n) U := by
  obtain ⟨U,hU,hUc,hreal,hUV,hsum,hanalytic,huniform⟩ :=
    A.exists_analytic_renormalizedFrequency hs hV hrealV
  have hfinite := A.renormalizedFrequency_eq_physical_finiteGap D hs.toSourcePsiNormalizedComplexExtension
  refine ⟨U,hU,hUc,hreal,hUV,hsum,fun n => ⟨hanalytic n,(hanalytic n).restrictScalars⟩,
    huniform,hfinite,?_⟩
  intro n F hF hphysical
  apply eqOn_of_analytic_of_sourceFiniteGap (by simp) (by norm_num) hU hUc hreal hF (hanalytic n)
  intro φ hf
  exact (hphysical φ hf).trans (hfinite φ hf n).symm

/-- The renormalized sum vanishes at the zero source, including for
nonzero selected indices where the physical frequency has free dispersion. -/
theorem renormalizedFrequency_zero
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) X u) (n : ℤ) :
    A.renormalizedFrequency n 0 = 0 := by
  have hgap (k : ℤ) : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (0 : CoeffPair 2)) (periodOnePotential_mem 0) k = 0 := by
    simpa only [map_zero] using canonicalPeriodicGap_zero (p := 2) (by simp) (by norm_num) k
  have hmom (k : ℤ) : A.moment n k 2 0 = 0 :=
    A.moment_succ_of_collapsed 0 (A.realType_subset_domain (0 : realTypeSourceSubmodule 2).property) n k (hgap k) 1
  simp only [renormalizedFrequency,hmom,tsum_zero,mul_zero]

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
