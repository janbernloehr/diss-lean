import NLS.ZakharovShabat.SourceDeleteResonance
import NLS.ZakharovShabat.SourceRealTypeAnalyticSlice
import NLS.ZakharovShabat.SourceBirkhoffSingletonStrip

/-! # Complex vanishing on deleted adapted coordinate slices

The real-form identity theorem extends actual real coordinate zeros to
one complex ball after an analytic source change and signed projection.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceBirkhoffMapComplexData.zero_on_complex_deleted_slice
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (b : realTypeSourceLocus p) (r δ : ℝ) (hr : 0 < r) (n : ℤ)
    (g : CoeffPair p → CoeffPair p) (hg : AnalyticOnNhd ℂ g (ball b.val δ))
    (hgW : MapsTo g (ball b.val δ) W)
    (hT : MapsTo (sourceDeleteResonance n) (ball b.val r) (ball b.val δ))
    (hzero : ∀ y ∈ ball b.val r, IsRealType (CoeffPair.toMax p y) →
      (sourceBirkhoffMap hp hp1 s (g (sourceDeleteResonance n y))).1 n = 0 ∧
        (sourceBirkhoffMap hp hp1 s (g (sourceDeleteResonance n y))).2 n = 0) :
    ∀ y ∈ ball b.val r,
      (sourceBirkhoffMap hp hp1 s (g (sourceDeleteResonance n y))).1 n = 0 ∧
        (sourceBirkhoffMap hp hp1 s (g (sourceDeleteResonance n y))).2 n = 0 := by
  let L : (Coeff p × Coeff p) →L[ℂ] (ℂ × ℂ) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).prodMap (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n)
  have hz := eqOn_zero_of_realType_projected_observation hp b r hr
    (sourceBirkhoffMap hp hp1 s) g (sourceDeleteResonance n) L
    (ball b.val δ) W D.analytic hg hgW hT (by
      intro y hy hreal
      exact Prod.ext (hzero y hy hreal).1 (hzero y hy hreal).2)
  intro y hy
  exact ⟨congrArg Prod.fst (hz y hy),congrArg Prod.snd (hz y hy)⟩

end NLS.ZakharovShabat
