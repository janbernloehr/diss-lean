import NLS.ZakharovShabat.RelativeSpectralProducts

/-!
# Restoring a selected factor in a relative spectral product

Absolute convergence of the relative displacements also gives convergence
after omitting any one factor. This permits exact factor restoration even
when a spectral numerator vanishes.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Omitting a local factor preserves convergence, including when that factor is zero. -/
theorem multipliable_update_spectralRelativeFactor (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun k => ξ k-(Real.pi : ℂ)*k) p) (z : ℂ) (hz : z ∉ freeLattice) (n : ℤ) :
    Multipliable (Function.update (spectralRelativeFactor ξ z) n 1) := by
  let u : ℤ → ℂ := fun k => if k = n then 0 else -((ξ k-(Real.pi : ℂ)*k)/(z-(Real.pi : ℂ)*k))
  have hu : Summable (fun k => ‖u k‖) :=
    (summable_norm_spectralRelativeDisplacement hp ξ hξ z hz).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun k => by
        by_cases hk : k = n
        · simp only [u, if_pos hk, norm_zero]
          exact norm_nonneg _
        · simp [u, hk])
  apply (multipliable_one_add_of_summable hu).congr
  intro k
  by_cases hk : k = n
  · simp [u, hk]
  · simp [u, hk, spectralRelativeFactor_eq ξ z hz]

/-- The full relative product is its local factor times the omitted-diagonal product. -/
theorem spectralRelativeProduct_eq_local_mul (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun k => ξ k-(Real.pi : ℂ)*k) p) (z : ℂ) (hz : z ∉ freeLattice) (n : ℤ) :
    (∏' k : ℤ, spectralRelativeFactor ξ z k) =
      spectralRelativeFactor ξ z n*(∏' k : ℤ, if k = n then 1 else spectralRelativeFactor ξ z k) :=
  Multipliable.tprod_eq_mul_tprod_ite' n (multipliable_update_spectralRelativeFactor hp ξ hξ z hz n)

end NLS.ZakharovShabat
