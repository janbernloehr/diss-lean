import NLS.ZakharovShabat.FreeResolventExteriorLimit
import NLS.ZakharovShabat.RelativeProductsVerticalLimit

/-!
# Relative products tend to one outside fixed free spectral discs

Strong free-resolvent decay makes the total absolute relative displacement
vanish. This controls the entire unconditional product, including paths with
bounded imaginary part and unbounded real part.
-/

noncomputable section
open Complex Filter Topology
open scoped ENNReal
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem tendsto_tsum_norm_relativeDisplacement_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (ξ : ℤ → ℂ) (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => ∑' n : ℤ, ‖(ξ n-(Real.pi : ℂ)*n)/(z i-(Real.pi : ℂ)*n)‖)
      l (𝓝 0) := by
  let a : Coeff p := ⟨_, hξ⟩
  have hz (i) := notMem_freeLattice_of_separated hr (hsep i)
  have h := (tendsto_scalarResolventToL1_of_separated hp z hz hescape hr hrπ hsep a).norm
  simpa only [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal),
    ENNReal.toReal_one, one_div, inv_one, Real.rpow_one, scalarResolventToL1_apply, norm_zero, lp.coeFn_zero, Pi.zero_apply, tsum_zero, a]
    using! h

/-- The single relative product has limit one in every direction outside fixed discs. -/
theorem tendsto_spectralRelativeProduct_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (ξ : ℤ → ℂ) (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => ∏' n, spectralRelativeFactor ξ (z i) n) l (𝓝 1) := by
  have hz (i) := notMem_freeLattice_of_separated hr (hsep i)
  have he : (fun i => ∏' n, spectralRelativeFactor ξ (z i) n) =
      (fun i => ∏' n, (1 + -((ξ n-(Real.pi : ℂ)*n)/(z i-(Real.pi : ℂ)*n)))) := by
    funext i
    congr 1
    funext n
    exact spectralRelativeFactor_eq ξ (z i) (hz i) n
  rw [he]
  apply tendsto_tprod_one_add_of_tsum_norm_tendsto_zero
  · exact Eventually.of_forall (fun i => by simpa only [norm_neg] using
      summable_norm_spectralRelativeDisplacement hp ξ hξ (z i) (hz i))
  · simpa only [norm_neg] using
      tendsto_tsum_norm_relativeDisplacement_of_separated hp ξ hξ z hescape hr hrπ hsep

/-- Both displaced roots may vary at every index; the paired relative product still tends to one. -/
theorem tendsto_spectralRelativePairProduct_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => spectralRelativePairProduct ξ η (z i)) l (𝓝 1) := by
  have h := (tendsto_spectralRelativeProduct_of_separated hp ξ hξ z hescape hr hrπ hsep).mul
    (tendsto_spectralRelativeProduct_of_separated hp η hη z hescape hr hrπ hsep)
  have he (i) : spectralRelativePairProduct ξ η (z i) =
      (∏' n, spectralRelativeFactor ξ (z i) n) * (∏' n, spectralRelativeFactor η (z i) n) := by
    have hz := notMem_freeLattice_of_separated hr (hsep i)
    exact (multipliable_spectralRelativeFactor hp ξ hξ (z i) hz).tprod_mul
      (multipliable_spectralRelativeFactor hp η hη (z i) hz)
  simpa only [he, mul_one] using! h

end NLS.ZakharovShabat
