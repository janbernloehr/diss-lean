import NLS.ZakharovShabat.SourcePsiGapRootIsospectral
import NLS.ZakharovShabat.SourcePsiReflectionPeriods
import NLS.ComplexAnalysis.OddSquareDescentCongruence

/-! Full real isospectral invariance of the actual simultaneous psi
families and their filled energy numerators. The canonical real gap-root
uniqueness theorem fixes the entire functions, including zero energy. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V₀ V : Set (CoeffPair p)}
  {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem SourceTheorem12_1Data.displacedRoots_im_eq_zero_of_real
    (H : SourceTheorem12_1Data hp hp1 W₀ W s) (φ : realTypeSourceSubmodule p) (n k : ℤ) :
    (displacedRoots (s n φ.val : Coeff p) k).im = 0 := by
  rw [H.real_agreement n φ]
  have hr := sourcePsiGapRoot_mem_realDeletedCoeffSubmodule hp hp1 n φ k
  simpa only [displacedRoots,Complex.add_im,Complex.mul_im,Complex.ofReal_im,
    Complex.intCast_im,mul_zero,zero_mul,zero_add] using hr

theorem SourceTheorem12_1Data.roots_eq_of_real_isospectral
    (H : SourceTheorem12_1Data hp hp1 W₀ W s) (K : SourceTheorem12_1Data hp hp1 V₀ V t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) :
    s n ψ.val = t n φ.val := by
  rw [H.real_agreement n ψ,K.real_agreement n φ]
  exact sourcePsiGapRoot_eq_of_isospectral hp hp1 φ ψ h n

theorem SourceTheorem12_1Data.selectedNumerator_eq_of_real_isospectral
    (H : SourceTheorem12_1Data hp hp1 W₀ W s) (K : SourceTheorem12_1Data hp hp1 V₀ V t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) (z : ℂ) :
    sourceSelectedPsiNumerator s n (z,ψ.val) = sourceSelectedPsiNumerator t n (z,φ.val) := by
  simp only [sourceSelectedPsiNumerator,sourcePsiDeletedCandidate,
    H.roots_eq_of_real_isospectral K φ ψ h n]

theorem SourceTheorem12_1Data.energyNumerator_eq_of_real_isospectral
    (H : SourceTheorem12_1Data hp hp1 W₀ W s) (K : SourceTheorem12_1Data hp hp1 V₀ V t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) (E : ℂ) :
    sourcePsiEnergyNumerator s n (E,ψ.val) = sourcePsiEnergyNumerator t n (E,φ.val) :=
  oddSquareDescent_congr_slice _ _ ψ.val φ.val
    (H.selectedNumerator_eq_of_real_isospectral K φ ψ h n) E

end NLS.ZakharovShabat
