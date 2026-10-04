import NLS.ZakharovShabat.SourceAbelianMomentSquaredGapAtlas
import NLS.ZakharovShabat.SourceSecondMomentFrequencyTheorem20_4

/-! # Unconditional construction in Theorem 20.4

Construct the moment atlas and squared-gap branch together, then sum its
actual moments. The result requires only a finite source exponent above
one. It agrees with every physical Birkhoff realization on finite-gap
sources and is uniquely determined by those values.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct all the data and conclusions of Theorem 20.4 for every
finite p > 1, without assuming an atlas or compatible psi extension. -/
theorem exists_sourceSecondMoment_theorem20_4 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ A : SourceAbelianMomentAtlas hp hp1 W s, ∃ U : Set (CoeffPair p),
        IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ A.domain ∧
        (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k => ‖A.moment n k 2 ψ‖)) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (A.renormalizedFrequency n) U ∧
          AnalyticOnNhd ℝ (A.renormalizedFrequency n) U) ∧
        (∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧ ∀ n : ℤ,
          TendstoUniformlyOn
            (fun (N : ℕ) ψ => -(4/(2*Real.pi):ℂ)*
              ∑ k ∈ Finset.Icc (-(N : ℤ)) N, A.moment n k 2 ψ)
            (A.renormalizedFrequency n) atTop T) ∧
        (∀ (W₀ B X : Set (CoeffPair 2)) (t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n)
          (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t)
          (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ),
          A.renormalizedFrequency n φ.val = D.finiteGapFrequencyAtExponent hp hp1 φ hf n -
            4*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1 - (2*(n:ℂ)*Real.pi)^2) ∧
        ∀ (n : ℤ) (F : CoeffPair p → ℂ), AnalyticOnNhd ℂ F U →
          (∀ (φ : realTypeSourceSubmodule p), φ ∈ sourceFiniteGapLocus hp hp1 →
            F φ.val = A.renormalizedFrequency n φ.val) → EqOn F (A.renormalizedFrequency n) U := by
  obtain ⟨W,V,_,_,hV,hrealV,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨U,hU,hUc,hreal,hUV,hsum,hanalytic,huniform⟩ :=
    A.exists_analytic_renormalizedFrequency hs hV hrealV
  refine ⟨W,s,A,U,hU,hUc,hreal,fun ψ hψ => (hUV hψ).1,hsum,
    fun n => ⟨hanalytic n,(hanalytic n).restrictScalars⟩,huniform,?_,?_⟩
  · intro W₀ B X t D φ hf n
    exact A.renormalizedFrequency_eq_physical_finiteGap_all_exponents D
      hs.toSourcePsiIsolatingComplexExtension φ hf n
  · intro n F hF hfinite
    exact eqOn_of_analytic_of_sourceFiniteGap hp hp1 hU hUc hreal hF (hanalytic n) hfinite

end NLS.ZakharovShabat
