import NLS.Dynamics.ComplexBirkhoffCoordinates
import NLS.ZakharovShabat.SourceBirkhoffTheorem15_2

/-! # The actual Birkhoff map in Section 22's complex coordinates

The established rectangular map is composed with the exact continuous linear
change of variables. Its real restriction consists of conjugate pairs, and
its coordinate products are the original spectral actions.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Birkhoff coordinates z=(x-iy)/sqrt(2), w=(x+iy)/sqrt(2). -/
def sourceComplexBirkhoffMap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (φ : CoeffPair p) : Coeff p × Coeff p :=
  Birkhoff.rectangularToComplex (sourceBirkhoffMap hp hp1 s φ)

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
include D

/-- The complex-coordinate map has full Banach analyticity on the constructed domain. -/
theorem complex_map_analytic : AnalyticOnNhd ℂ (sourceComplexBirkhoffMap hp hp1 s) W := by
  intro φ hφ
  exact ((Birkhoff.rectangularToComplex (p := p)).toContinuousLinearMap.analyticAt _).comp (D.analytic φ hφ)

/-- Its coordinate products are the actual spectral actions, including closed gaps. -/
theorem complex_map_action (φ : CoeffPair p) (hφ : φ ∈ W) (n : ℤ) :
    (sourceComplexBirkhoffMap hp hp1 s φ).1 n*(sourceComplexBirkhoffMap hp hp1 s φ).2 n =
      sourceComplexAction hp hp1 n φ := by
  rw [sourceComplexBirkhoffMap, Birkhoff.rectangularToComplex_action, D.action_radius φ hφ n]
  ring

/-- Real sources have conjugate complex Birkhoff coordinates at the same index. -/
theorem complex_map_real (φ : realTypeSourceSubmodule p) :
    Birkhoff.IsConjugatePair (sourceComplexBirkhoffMap hp hp1 s φ.val) :=
  Birkhoff.rectangularToComplex_real _ (D.coordinates_im_eq_zero_of_realType φ.val φ.property)

/-- Real source dependence is continuous in the full complex sequence norm. -/
theorem continuous_complex_map_real :
    Continuous (fun φ : realTypeSourceSubmodule p => sourceComplexBirkhoffMap hp hp1 s φ.val) := by
  apply continuous_iff_continuousAt.mpr
  intro φ
  exact ((D.complex_map_analytic φ.val (D.real_subset φ.property)).continuousAt).comp
    (realTypeSourceSubmodule p).subtypeL.continuous.continuousAt

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
