import NLS.ZakharovShabat.SourceLemma5_2
import NLS.ZakharovShabat.SourceFiniteGapFrequencyExponent
import NLS.ZakharovShabat.SourceAbelianMomentExponent

/-! # Physical finite-gap H₄ frequencies at all finite exponents

The same Fourier coefficients determine a unique Hilbert representative.
Every physical hierarchy Hamiltonian is preserved, and the independently
defined open/closed action derivative retains the exact weighted-moment sum.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Physical H₄ action derivatives of the unique representative of the same potential. -/
def finiteGapFourthFrequencyAtExponent
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) : ℂ :=
  D.finiteGapFourthFrequency (sourceFiniteGapHilbertModel hp hp1 φ hf)
    (sourceFiniteGapHilbertModel_mem hp hp1 φ hf) n

/-- At p=2 the representative recovers the original physical derivative. -/
theorem finiteGapFourthFrequencyAtExponent_two
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    D.finiteGapFourthFrequencyAtExponent (by simp) (by norm_num) φ hf n = D.finiteGapFourthFrequency φ hf n := by
  unfold finiteGapFourthFrequencyAtExponent
  simp only [sourceFiniteGapHilbertModel_eq_of_coefficients (by simp) (by norm_num) φ hf φ
    (fun _ => ⟨rfl,rfl⟩)]

/-- The physical derivative value is independent of Birkhoff coordinates. -/
theorem finiteGapFourthFrequencyAtExponent_independent_coordinates
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V u)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    D.finiteGapFourthFrequencyAtExponent hp hp1 φ hf n = E.finiteGapFourthFrequencyAtExponent hp hp1 φ hf n :=
  D.finiteGapFourthFrequency_independent_coordinates E _ _ n

end SourceBirkhoffMapComplexData

/-- Lemma 5.2 at every finite source exponent, retaining the same physical
potential and both its mass and momentum Hamiltonians. -/
theorem SourceAbelianMomentAtlas.weighted_moments_eq_physical_fourth_finiteGap
    {hp : p ≠ ⊤} {hp1 : 1 < p} {X P : Set (CoeffPair p)}
    {u : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (A : SourceAbelianMomentAtlas hp hp1 X u)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P u)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    D.finiteGapFourthFrequencyAtExponent hp hp1 φ hf n-
      6*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2-
      (12*Real.pi:ℂ)*n*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1-
      (2*(n:ℂ)*Real.pi)^3 = -12*(∑' k : ℤ, (k:ℂ)*A.moment n k 2 φ.val) := by
  classical
  obtain ⟨Y,Z,_,_,_,_,v,hv,hlocal⟩ := exists_sourceAbelianMoment_localCharts (p := 2) (by simp) (by norm_num)
  choose L hL using hlocal
  let C : SourceAbelianMomentAtlas (by simp) (by norm_num) Y v := ⟨L⟩
  let ψ := sourceFiniteGapHilbertModel hp hp1 φ hf
  have hψ := sourceFiniteGapHilbertModel_mem hp hp1 φ hf
  have he : (∑' k : ℤ, (k:ℂ)*A.moment n k 2 φ.val) =
      ∑' k : ℤ, (k:ℂ)*C.moment n k 2 ψ.val := by
    apply tsum_congr
    intro k
    exact congrArg ((k:ℂ)*·) (A.moment_real_eq_of_coefficients C hs hv.toSourcePsiIsolatingComplexExtension
      φ ψ (sourceFiniteGapHilbertModel_coefficients hp hp1 φ hf) n k 2)
  have hphysical := D.finiteGap_lemma5_2 C hv ψ hψ n
  rw [← he] at hphysical
  simpa only [ψ,SourceBirkhoffMapComplexData.finiteGapFourthFrequencyAtExponent,
    sourceFiniteGapHilbertModel_hamiltonian] using hphysical

end NLS.ZakharovShabat
