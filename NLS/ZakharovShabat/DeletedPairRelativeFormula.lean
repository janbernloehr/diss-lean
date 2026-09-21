import NLS.ZakharovShabat.DeletedSpectralPairProducts
import NLS.ZakharovShabat.RestoredSpectralPairs

/-!
# Relative formula for the product with one pair removed

Off the free lattice the remaining entire product is the squared filled sine
quotient times the two omitted-diagonal relative products. Replacing the
removed roots by their free values proves the identity without assuming
that the actual endpoint factors are nonzero.
-/

noncomputable section
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The omitted-diagonal relative product ignores the omitted displacement. -/
theorem freeDiscRelativeProduct_congr_away (a b : Coeff p) (n : ℤ)
    (hab : ∀ k, k ≠ n → a k = b k) (z : ℂ) :
    freeDiscRelativeProduct a n z = freeDiscRelativeProduct b n z := by
  apply tprod_congr
  intro k
  by_cases hk : k = n
  · simp only [if_pos hk]
  · simp only [if_neg hk,hab k hk]

/-- The remaining entire product has the exact free-relative formula, even at actual endpoints. -/
theorem deletedSpectralPairProduct_eq_relative (hp : p ≠ ⊤) (a b : Coeff p)
    (n : ℤ) (z : ℂ) (hz : z ∉ freeLattice) :
    deletedSpectralPairProduct (displacedRoots a) (displacedRoots b) n z =
      (freeSineQuotient n z)^2*freeDiscRelativeProduct a n z*freeDiscRelativeProduct b n z := by
  let α : Coeff p := a-lp.single p n (a n)
  let β : Coeff p := b-lp.single p n (b n)
  have hα (k : ℤ) (hk : k ≠ n) : α k = a k := by simp [α,lp.single_apply,hk]
  have hβ (k : ℤ) (hk : k ≠ n) : β k = b k := by simp [β,lp.single_apply,hk]
  have hα0 : α n = 0 := by simp [α]
  have hβ0 : β n = 0 := by simp [β]
  have hd := deletedSpectralPairProduct_congr_away (displacedRoots α) (displacedRoots β)
    (displacedRoots a) (displacedRoots b) n
    (fun k hk => by simp only [displacedRoots,hα k hk])
    (fun k hk => by simp only [displacedRoots,hβ k hk])
  have he := entireSpectralPairProduct_eq_deleted hp _ _ (memℓp_displacedRoots α)
    (memℓp_displacedRoots β) n z
  rw [entireSpectralPairProduct_eq_restored hp α β n z hz,hd] at he
  simp only [restoredSineProduct,displacedRoots,hα0,hβ0,add_zero,sub_zero,
    freeDiscRelativeProduct_congr_away α a n hα z,freeDiscRelativeProduct_congr_away β b n hβ z] at he
  have hnz : z-(Real.pi : ℂ)*n ≠ 0 := free_denominator_ne_zero hz n
  apply mul_left_cancel₀ (show -4*(z-(Real.pi : ℂ)*n)^2 ≠ 0 from
    mul_ne_zero (by norm_num) (pow_ne_zero _ hnz))
  linear_combination -he

end NLS.ZakharovShabat
