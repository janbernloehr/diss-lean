import NLS.ZakharovShabat.VerticalSpectralDisplacements
import NLS.ComplexAnalysis.SmallAbsoluteProducts

/-!
# Relative spectral products at vertical infinity

The absolute displacement sum tends to zero on either end of every fixed
vertical line. Exponential product control therefore gives the correctly
normalized limit one for both single and paired relative products.
-/

noncomputable section
open Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The deviation of an unconditional relative product is controlled by its absolute displacement sum. -/
theorem norm_spectralRelativeProduct_sub_one_le (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    ‖(∏' n, spectralRelativeFactor ξ z n)-1‖ ≤
      Real.exp (∑' n, ‖(ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)‖)-1 := by
  have he : spectralRelativeFactor ξ z = fun n => 1 + -((ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)) :=
    funext (spectralRelativeFactor_eq ξ z hz)
  rw [he]
  simpa only [norm_neg] using norm_tprod_one_add_sub_one_le_exp
    (fun n => -((ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)))
    (by simpa only [norm_neg] using summable_norm_spectralRelativeDisplacement hp ξ hξ z hz)

/-- A nonreal vertical spectral point is eventually available whenever the absolute height diverges. -/
theorem eventually_verticalSpectralPoint_notMem_freeLattice {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) (x : ℝ) :
    ∀ᶠ a in l, verticalSpectralPoint x (y a) ∉ freeLattice := by
  filter_upwards [hy.eventually (eventually_ge_atTop (1 : ℝ))] with a ha
  apply verticalSpectralPoint_notMem_freeLattice
  intro h
  norm_num [h] at ha

/-- Every single relative spectral product tends to one along either end of a fixed vertical line. -/
theorem tendsto_spectralRelativeProduct_vertical {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (x : ℝ) :
    Tendsto (fun a => ∏' n, spectralRelativeFactor ξ (verticalSpectralPoint x (y a)) n) l (𝓝 1) := by
  let u := fun a n => -((ξ n-(Real.pi : ℂ)*n)/(verticalSpectralPoint x (y a)-(Real.pi : ℂ)*n))
  have hs : ∀ᶠ a in l, Summable (fun n => ‖u a n‖) := by
    filter_upwards [eventually_verticalSpectralPoint_notMem_freeLattice hy x] with a ha
    simpa only [u,norm_neg] using summable_norm_spectralRelativeDisplacement hp ξ hξ _ ha
  have ht : Tendsto (fun a => ∑' n, ‖u a n‖) l (𝓝 0) := by
    simpa only [u,norm_neg] using tendsto_tsum_norm_vertical_relativeDisplacement hy hp ξ hξ x
  apply (tendsto_tprod_one_add_of_tsum_norm_tendsto_zero u hs ht).congr'
  filter_upwards [eventually_verticalSpectralPoint_notMem_freeLattice hy x] with a ha
  apply tprod_congr
  intro n
  exact (spectralRelativeFactor_eq ξ _ ha n).symm

/-- Pairing the two displaced root sequences preserves the vertical limit one. -/
theorem tendsto_spectralRelativePairProduct_vertical {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (x : ℝ) :
    Tendsto (fun a => spectralRelativePairProduct ξ η (verticalSpectralPoint x (y a))) l (𝓝 1) := by
  have h := (tendsto_spectralRelativeProduct_vertical hy hp ξ hξ x).mul
    (tendsto_spectralRelativeProduct_vertical hy hp η hη x)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_verticalSpectralPoint_notMem_freeLattice hy x] with a ha
  exact ((multipliable_spectralRelativeFactor hp ξ hξ _ ha).tprod_mul
    (multipliable_spectralRelativeFactor hp η hη _ ha)).symm

end NLS.ZakharovShabat
