import NLS.SequenceSpaces.WeightedPairMap

/-! # Coefficient-preserving comparison of weighted sequence spaces

Pointwise weight comparisons induce continuous linear equivalences.
The finite-exponent pair estimates use the original combined p-sum norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.WeightComparison
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The coefficient-preserving continuous map induced by a pointwise weight comparison. -/
def map (w v : Weight) (C : ℝ) (hC : 0 ≤ C) (h : ∀ n, v n ≤ C*w n) :
    WeightedCoeff w p →L[ℂ] WeightedCoeff v p :=
  WeightedCoeff.weightedMultiplierCLM w v (fun _ => 1) C hC (by simpa using h)

/-- Weight comparison leaves every raw coefficient unchanged. -/
@[simp] theorem map_apply (w v : Weight) (C : ℝ) (hC : 0 ≤ C) (h : ∀ n, v n ≤ C*w n)
    (a : WeightedCoeff w p) (n : ℤ) : (map w v C hC h a).val n = a.val n := by
  simp [map]

/-- The comparison map has the same bound as the pointwise weight comparison. -/
theorem norm_map_le (w v : Weight) (C : ℝ) (hC : 0 ≤ C) (h : ∀ n, v n ≤ C*w n)
    (a : WeightedCoeff w p) : ‖map w v C hC h a‖ ≤ C*‖a‖ :=
  WeightedCoeff.norm_weightedMultiplier_le w v (fun _ => 1) C hC (by simpa using h) a

/-- Mutually comparable weights give a coefficient-preserving continuous linear equivalence. -/
def equiv (w v : Weight) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcv : ∀ n, v n ≤ C*w n) (hdw : ∀ n, w n ≤ D*v n) :
    WeightedCoeff w p ≃L[ℂ] WeightedCoeff v p where
  toLinearEquiv :=
    { toLinearMap := (map w v C hC hcv).toLinearMap
      invFun := map v w D hD hdw
      left_inv a := by
        apply Subtype.ext
        funext n
        exact (map_apply v w D hD hdw _ n).trans (map_apply w v C hC hcv a n)
      right_inv a := by
        apply Subtype.ext
        funext n
        exact (map_apply w v C hC hcv _ n).trans (map_apply v w D hD hdw a n) }
  continuous_toFun := (map w v C hC hcv).continuous
  continuous_invFun := (map v w D hD hdw).continuous

/-- The forward weight equivalence preserves each coefficient. -/
@[simp] theorem equiv_apply (w v : Weight) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcv : ∀ n, v n ≤ C*w n) (hdw : ∀ n, w n ≤ D*v n) (a : WeightedCoeff w p) (n : ℤ) :
    (equiv w v C D hC hD hcv hdw a).val n = a.val n := map_apply w v C hC hcv a n

/-- The inverse weight equivalence preserves each coefficient. -/
@[simp] theorem equiv_symm_apply (w v : Weight) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcv : ∀ n, v n ≤ C*w n) (hdw : ∀ n, w n ≤ D*v n) (a : WeightedCoeff v p) (n : ℤ) :
    ((equiv w v C D hC hD hcv hdw).symm a).val n = a.val n := map_apply v w D hD hdw a n

/-- Apply the weight equivalence to both components of the original p-sum pair space. -/
def pairEquiv (w v : Weight) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcv : ∀ n, v n ≤ C*w n) (hdw : ∀ n, w n ≤ D*v n) :
    WeightedCoeffPair w p ≃L[ℂ] WeightedCoeffPair v p :=
  (WeightedCoeffPair.toMax w p).trans
    (((equiv w v C D hC hD hcv hdw).prodCongr (equiv w v C D hC hD hcv hdw)).trans
      (WeightedCoeffPair.toMax v p).symm)

/-- The pair comparison retains the scalar bound, with no product-norm loss. -/
theorem norm_pairEquiv_le (hp : p ≠ ⊤) (w v : Weight) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcv : ∀ n, v n ≤ C*w n) (hdw : ∀ n, w n ≤ D*v n) (a : WeightedCoeffPair w p) :
    ‖pairEquiv w v C D hC hD hcv hdw a‖ ≤ C*‖a‖ := by
  exact WeightedCoeffPair.norm_mapComponents_le hp w v
    (map w v C hC hcv) (map w v C hC hcv) hC
    (norm_map_le w v C hC hcv) (norm_map_le w v C hC hcv) a

/-- The inverse pair comparison retains the reverse scalar bound. -/
theorem norm_pairEquiv_symm_le (hp : p ≠ ⊤) (w v : Weight) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcv : ∀ n, v n ≤ C*w n) (hdw : ∀ n, w n ≤ D*v n) (a : WeightedCoeffPair v p) :
    ‖(pairEquiv w v C D hC hD hcv hdw).symm a‖ ≤ D*‖a‖ := by
  exact WeightedCoeffPair.norm_mapComponents_le hp v w
    (map v w D hD hdw) (map v w D hD hdw) hD
    (norm_map_le v w D hD hdw) (norm_map_le v w D hD hdw) a

end NLS.WeightComparison
