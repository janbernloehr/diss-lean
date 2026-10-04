import NLS.ZakharovShabat.SourceAbelianMomentExponent
import NLS.ZakharovShabat.SourceFiniteGapFrequencyExponent
import NLS.ZakharovShabat.SourceSecondMomentFrequencyFiniteGap

/-! # Theorem 20.4 at all finite source exponents

The analytic moment sum is the unique extension of the independently
constructed physical finite-gap frequencies after subtracting the original
source's mass and free dispersion. Contour-moment compatibility transfers
the physical identity from the same potential's Hilbert representative.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The sum retains the coefficient-preserving real-source compatibility
of every moment, with its exact normalization. -/
theorem renormalizedFrequency_real_eq_of_coefficients
    {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
    {W P : Set (CoeffPair p)} {V Q : Set (CoeffPair q)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (A : SourceAbelianMomentAtlas hp hp1 W s) (B : SourceAbelianMomentAtlas hq hq1 V t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (ht : SourcePsiIsolatingComplexExtension hq hq1 Q t)
    (φ : realTypeSourceSubmodule p) (ψ : realTypeSourceSubmodule q)
    (hcoeff : ∀ j : ℤ, ψ.val.fst j = φ.val.fst j ∧ ψ.val.snd j = φ.val.snd j) (n : ℤ) :
    A.renormalizedFrequency n φ.val = B.renormalizedFrequency n ψ.val := by
  unfold renormalizedFrequency
  congr 1
  exact tsum_congr (fun k => A.moment_real_eq_of_coefficients B hs ht φ ψ hcoeff n k 2)

variable {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {W₀ B X : Set (CoeffPair 2)} {t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Lemma 20.2's physical finite-gap identity transported to every finite
source exponent above one, with the original physical mass Hamiltonian. -/
theorem renormalizedFrequency_eq_physical_finiteGap_all_exponents
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    A.renormalizedFrequency n φ.val = D.finiteGapFrequencyAtExponent hp hp1 φ hf n -
      4*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1 - (2*(n:ℂ)*Real.pi)^2 := by
  classical
  obtain ⟨Y,Z,_,_,_,_,u,hu,hlocal⟩ := exists_sourceAbelianMoment_localCharts (p := 2) (by simp) (by norm_num)
  choose L hL using hlocal
  let C : SourceAbelianMomentAtlas (by simp) (by norm_num) Y u := ⟨L⟩
  let ψ := sourceFiniteGapHilbertModel hp hp1 φ hf
  have hψ := sourceFiniteGapHilbertModel_mem hp hp1 φ hf
  have he := A.renormalizedFrequency_real_eq_of_coefficients C hs hu.toSourcePsiIsolatingComplexExtension
    φ ψ (sourceFiniteGapHilbertModel_coefficients hp hp1 φ hf) n
  have hphysical := C.renormalizedFrequency_eq_physical_finiteGap D hu ψ hψ n
  exact he.trans (by
    simpa only [ψ,SourceBirkhoffMapComplexData.finiteGapFrequencyAtExponent,
      sourceFiniteGapHilbertModel_hamiltonian_one] using hphysical)

/-- Theorem 20.4: absolute and locally uniform convergence, analyticity,
physical finite-gap agreement, and uniqueness at every finite p > 1. -/
theorem exists_theorem20_4
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧
      (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k => ‖A.moment n k 2 ψ‖)) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (A.renormalizedFrequency n) U ∧
        AnalyticOnNhd ℝ (A.renormalizedFrequency n) U) ∧
      (∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧ ∀ n : ℤ,
        TendstoUniformlyOn
          (fun (N : ℕ) ψ => -(4/(2*Real.pi):ℂ)*
            ∑ k ∈ Finset.Icc (-(N : ℤ)) N, A.moment n k 2 ψ)
          (A.renormalizedFrequency n) atTop T) ∧
      (∀ (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ),
        A.renormalizedFrequency n φ.val = D.finiteGapFrequencyAtExponent hp hp1 φ hf n -
          4*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1 - (2*(n:ℂ)*Real.pi)^2) ∧
      ∀ (n : ℤ) (F : CoeffPair p → ℂ), AnalyticOnNhd ℂ F U →
        (∀ (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1),
          F φ.val = D.finiteGapFrequencyAtExponent hp hp1 φ hf n -
            4*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1 - (2*(n:ℂ)*Real.pi)^2) →
        EqOn F (A.renormalizedFrequency n) U := by
  obtain ⟨U,hU,hUc,hreal,hUV,hsum,hanalytic,huniform⟩ :=
    A.exists_analytic_renormalizedFrequency hs hV hrealV
  have hfinite := A.renormalizedFrequency_eq_physical_finiteGap_all_exponents D hs.toSourcePsiIsolatingComplexExtension
  refine ⟨U,hU,hUc,hreal,hUV,hsum,fun n => ⟨hanalytic n,(hanalytic n).restrictScalars⟩,
    huniform,hfinite,?_⟩
  intro n F hF hphysical
  apply eqOn_of_analytic_of_sourceFiniteGap hp hp1 hU hUc hreal hF (hanalytic n)
  intro φ hf
  exact (hphysical φ hf).trans (hfinite φ hf n).symm

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
