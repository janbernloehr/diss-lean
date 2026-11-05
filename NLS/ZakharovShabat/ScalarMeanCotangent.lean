import NLS.ZakharovShabat.Domain

/-! # Scalar Sobolev cotangents on the fixed-mean tangent space

The unconditional Fourier expansion in the original scalar domain shows
that a continuous cotangent vanishing on every nonconstant unit mode
vanishes on every zero-mean direction.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual scalar-domain norm has the usual unconditional Fourier mode expansion. -/
theorem hasSum_scalarModes (hp : p ≠ ⊤) (h : ScalarDomain p) :
    HasSum (fun n : ℤ => scalarMode n (h.val n)) h := by
  let e := WeightedCoeff.weightIsometry (Weight.sobolev 1) p
  have hs := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum
    (lp.hasSum_single hp (e h))
  change HasSum (fun n : ℤ => e.symm (lp.single p n (e h n))) (e.symm (e h)) at hs
  rw [e.symm_apply_apply] at hs
  exact hs

/-- The mean is the only possible cotangent left after all nonconstant Fourier tests vanish. -/
theorem scalarCotangent_eq_zero_on_zero_mean (hp : p ≠ ⊤)
    (L : ScalarDomain p →L[ℂ] ℂ)
    (hL : ∀ k : ℤ, k ≠ 0 → L (scalarMode k 1) = 0)
    (h : ScalarDomain p) (hh : h.val 0 = 0) : L h = 0 := by
  have hs := L.hasSum (hasSum_scalarModes hp h)
  have hterm (k : ℤ) : L (scalarMode k (h.val k)) = 0 := by
    have he : scalarMode (p := p) k (h.val k) = h.val k • scalarMode k 1 := by
      apply Subtype.ext
      funext j
      by_cases hj : j = k <;> simp [scalarMode_apply,hj]
    rw [he,map_smul,smul_eq_mul]
    by_cases hk : k = 0
    · rw [hk,hh,zero_mul]
    · rw [hL k hk,mul_zero]
  change HasSum (fun k : ℤ => L (scalarMode k (h.val k))) (L h) at hs
  have he : (fun k : ℤ => L (scalarMode k (h.val k))) = (fun _ => 0) := funext hterm
  rw [he] at hs
  exact hs.unique hasSum_zero

end NLS.ZakharovShabat
