import NLS.ZakharovShabat.SourceAbelianSquare
import NLS.ZakharovShabat.SourceAbelianPrimitiveIsospectral

/-! # Isospectrality preserves the filled normalized primitive square

Equality on the common canonical root domain passes to the defining
relative limit, including the selected cut and its collapsed endpoints.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAbelianSquare_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) (z : ℂ) :
    sourceAbelianSquare hp hp1 ψ.val ψ.property n z =
      sourceAbelianSquare hp hp1 φ.val φ.property n z := by
  unfold sourceAbelianSquare denseLimitExtension Filter.limUnder
  have hdom := sourceCanonicalRootDomain_eq_of_isospectral hp hp1 φ ψ h
  rw [hdom]
  apply congrArg (fun L : Filter ℂ => Filter.lim L)
  apply Filter.map_congr
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hwψ : w ∈ sourceCanonicalRootDomain hp hp1 ψ.val := hdom.symm ▸ hw
  rw [sourceAbelianPrimitive_eq_of_isospectral hp hp1 φ ψ h w hwψ]

theorem sourceAbelianSquare_eq_of_actions (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceRealActionLevelSet hp hp1 φ)
    (hi : sourceIsospectralSet hp φ = sourceRealActionLevelSet hp hp1 φ) (n : ℤ) (z : ℂ) :
    sourceAbelianSquare hp hp1 ψ.val ψ.property n z =
      sourceAbelianSquare hp hp1 φ.val φ.property n z :=
  sourceAbelianSquare_eq_of_isospectral hp hp1 φ ψ (hi.symm ▸ h) n z

end NLS.ZakharovShabat
