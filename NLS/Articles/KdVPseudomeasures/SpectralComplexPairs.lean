import NLS.Articles.KdVPseudomeasures.SpectralComplexCentral
import NLS.KdV.PseudomeasureComplexPairs

/-! Actual lexicographic high pairs on the full original complex source. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV NLS.ComplexAnalysis

/-- The native physical pair parametrized by the exact original complex distribution. -/
def SourceHillComplexPair (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (n : ℕ) : Type :=
  EndpointHillComplexPair r hr.1 hr.2 (sourceEndpointCoefficients r q) n

/-- Construct an actual ordered source pair without a reality assumption. -/
def sourceHillComplexPair (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ) (hn : 1 ≤ n)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) : SourceHillComplexPair r hr q n :=
  endpointHillComplexPair r hr.1 hr.2 n (sourceEndpointCoefficients r q) hn
    (by simpa only [norm_sourceEndpointCoefficients] using hs)

variable (r : ℝ) (hr : AdmissiblePredualOrder r)
variable (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (n : ℕ)

/-- The pair exhausts the full actual original source spectrum on its corrected strip. -/
theorem SourceHillComplexPair.spectrum_iff (p : SourceHillComplexPair r hr q n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    z ∈ sourceHillSpectrum r hr q ↔ z = p.left ∨ z = p.right := by
  rw [sourceHillSpectrum_eq]
  exact EndpointHillComplexPair.spectrum_iff p z hz

/-- The repetitions are actual full physical algebraic multiplicities, also for Jordan chains. -/
theorem SourceHillComplexPair.multiplicities (p : SourceHillComplexPair r hr q n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    sourceHillAlgebraicMultiplicity r hr q z = ({p.left,p.right}:Multiset ℂ).count z := by
  rw [sourceHillAlgebraicMultiplicity_eq]
  exact EndpointHillComplexPair.multiplicities p z hz

/-- The pair is intrinsic to the original physical spectrum and source order. -/
theorem SourceHillComplexPair.unique (p s : SourceHillComplexPair r hr q n) : p = s :=
  EndpointHillComplexPair.unique r hr.1 hr.2 n (sourceEndpointCoefficients r q) p s

/-- The first high pair is strictly above its original central real-part separator. -/
theorem SourceHillComplexPair.above_own_separator (hn : 1 ≤ n) (p : SourceHillComplexPair r hr q n) :
    freeHillValue n-12*(n:ℝ) < p.left.re := by
  have hp : |p.left.re-freeHillValue n| ≤ 6*(n:ℝ) := p.left_mem
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  linarith [(abs_le.mp hp).1]

/-- Distinct mode numbers give strict separation in real part of the actual source pairs. -/
theorem SourceHillComplexPair.right_re_lt_left (hn : 1 ≤ n) (m : ℕ) (hnm : n < m)
    (p : SourceHillComplexPair r hr q n) (s : SourceHillComplexPair r hr q m) :
    p.right.re < s.left.re :=
  EndpointHillComplexPair.right_re_lt_left r hr.1 hr.2 n (sourceEndpointCoefficients r q)
    hn (sourceEndpointCoefficients r q) m hnm p s

/-- The high physical pairs exhaust the entire complex source spectrum above the separator. -/
theorem sourceHillSpectrum_complex_high_iff_pair (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (P : (n : ℕ) → N ≤ n → SourceHillComplexPair r hr q n)
    (z : ℂ) (hhigh : freeHillValue N-12*(N:ℝ) ≤ z.re) :
    z ∈ sourceHillSpectrum r hr q ↔
      ∃ (n : ℕ) (hn : N ≤ n), z = (P n hn).left ∨ z = (P n hn).right := by
  constructor
  · intro hz
    obtain ⟨n, hn, hstrip, _⟩ := sourceHillSpectrum_complex_high_cover r hr q N hN hs z hz hhigh
    exact ⟨n, hn, (SourceHillComplexPair.spectrum_iff r hr q n (P n hn) z hstrip).mp hz⟩
  · rintro ⟨n, hn, he | he⟩
    · rw [he, sourceHillSpectrum_eq]
      exact (P n hn).left_spectral
    · rw [he, sourceHillSpectrum_eq]
      exact (P n hn).right_spectral

end NLS.Articles.KdVPseudomeasures
