import NLS.ZakharovShabat.SourceSingleRootQuotientAbsolute
import NLS.ZakharovShabat.SourcePsiFilledRegularFactor

/-!
# Literal auxiliary products in (2.24)-(2.25)

The double-omitted product converges absolutely. Its regular factor has
no artificial pole at the unused numerator root. Factorization is proved
without dividing by either retained numerator factors or their zeros.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourcePsiDoubleOmittedFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) (k : ℤ) : ℂ :=
  if k = n ∨ k = m then 1 else (displacedRoots a k-z)/sourceStandardRoot hp hp1 ψ k z

theorem summable_norm_sourcePsiDoubleOmittedFactor_sub_one
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) :
    Summable (fun k => ‖sourcePsiDoubleOmittedFactor hp hp1 n m a ψ z k-1‖) := by
  apply (summable_norm_sourceSingleRootQuotient_error hp hp1 ψ a z).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro k
  by_cases hk : k = n ∨ k = m
  · simp [sourcePsiDoubleOmittedFactor,hk]
  · simp [sourcePsiDoubleOmittedFactor,hk]

theorem multipliable_sourcePsiDoubleOmittedFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) :
    Multipliable (sourcePsiDoubleOmittedFactor hp hp1 n m a ψ z) := by
  convert multipliable_one_add_of_summable
    (summable_norm_sourcePsiDoubleOmittedFactor_sub_one hp hp1 n m a ψ z) using 1
  ext k
  ring

def sourcePsiDoubleOmittedProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  ∏' k, sourcePsiDoubleOmittedFactor hp hp1 n m a ψ z k

theorem hasProd_sourcePsiDoubleOmitted_subtype
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) :
    HasProd (fun k : {k : ℤ // k ≠ n ∧ k ≠ m} =>
      (displacedRoots a k-z)/sourceStandardRoot hp hp1 ψ k z)
      (sourcePsiDoubleOmittedProduct hp hp1 n m a ψ z) := by
  apply (hasProd_subtype_iff_mulIndicator (s := {k : ℤ | k ≠ n ∧ k ≠ m})
    (f := fun k => (displacedRoots a k-z)/sourceStandardRoot hp hp1 ψ k z)).mpr
  unfold sourcePsiDoubleOmittedProduct
  convert (multipliable_sourcePsiDoubleOmittedFactor hp hp1 n m a ψ z).hasProd using 1
  ext k
  by_cases hkn : k = n <;> by_cases hkm : k = m <;>
    simp [Set.mulIndicator,sourcePsiDoubleOmittedFactor,hkn,hkm]

theorem sourcePsiDoubleOmittedProduct_comm
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) :
    sourcePsiDoubleOmittedProduct hp hp1 n m a ψ z =
      sourcePsiDoubleOmittedProduct hp hp1 m n a ψ z := by
  simp only [sourcePsiDoubleOmittedProduct,sourcePsiDoubleOmittedFactor,or_comm]

theorem sourceSingleRootQuotient_eq_doubleOmitted
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)) =
      sourcePsiDoubleOmittedProduct hp hp1 n m a ψ z *
        ((displacedRoots a n-z)/sourceStandardRoot hp hp1 ψ n z) := by
  have he : (fun k => if k = n then 1 else sourceSingleRootQuotientFactor hp hp1 ψ a z m k) =
      sourcePsiDoubleOmittedFactor hp hp1 n m a ψ z := by
    funext k
    by_cases hkn : k = n <;> by_cases hkm : k = m <;>
      simp [sourceSingleRootQuotientFactor,sourcePsiDoubleOmittedFactor,hkn,hkm]
  have hd : HasProd (fun k => if k = n then 1 else sourceSingleRootQuotientFactor hp hp1 ψ a z m k)
      (sourcePsiDoubleOmittedProduct hp hp1 n m a ψ z) := by
    rw [he]
    exact (multipliable_sourcePsiDoubleOmittedFactor hp hp1 n m a ψ z).hasProd
  simpa only [sourceSingleRootQuotientFactor,if_neg hmn.symm] using
    eq_mul_of_hasProd_ite (hasProd_sourceSingleRootQuotientFactor hp hp1 ψ a z m hz) n _ hd

/-- The literal regular factor from (2.24), independent of the omitted roots. -/
def sourcePsiZeta (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  I/sourceStandardRoot hp hp1 ψ n z * sourcePsiDoubleOmittedProduct hp hp1 n m a ψ z

theorem sourcePsiZeta_eq_product
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) :
    sourcePsiZeta hp hp1 n m a ψ z = I/sourceStandardRoot hp hp1 ψ n z *
      ∏' k : {k : ℤ // k ≠ n ∧ k ≠ m}, (displacedRoots a k-z)/sourceStandardRoot hp hp1 ψ k z := by
  rw [(hasProd_sourcePsiDoubleOmitted_subtype hp hp1 n m a ψ z).tprod_eq]
  rfl

/-- Equation (2.25), including zeros of any numerator factor. -/
theorem sourcePsi_zetaSingle_eq_product
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    -sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)) =
      -(∏' k : {k : ℤ // k ≠ m}, (displacedRoots a k-z)/sourceStandardRoot hp hp1 ψ k z) := by
  rw [(hasProd_sourceSingleRootQuotient_subtype hp hp1 ψ a z m hz).tprod_eq]

theorem sourcePsiGapRegularFactor_eq_zeta
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) (hzn : z ≠ displacedRoots a n) :
    sourcePsiGapRegularFactor hp hp1 n m a ψ z = sourcePsiZeta hp hp1 n m a ψ z := by
  have hn : displacedRoots a n-z ≠ 0 := sub_ne_zero.mpr hzn.symm
  unfold sourcePsiGapRegularFactor sourcePsiZeta
  rw [sourceSingleRootQuotient_eq_doubleOmitted hp hp1 n m hmn a ψ z hz]
  field_simp [hn]

theorem sourcePsiZeta_congr
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (a b : Coeff p)
    (hab : ∀ k : ℤ, k ≠ n → k ≠ m → a k = b k) (ψ : CoeffPair p) (z : ℂ) :
    sourcePsiZeta hp hp1 n m a ψ z = sourcePsiZeta hp hp1 n m b ψ z := by
  unfold sourcePsiZeta sourcePsiDoubleOmittedProduct
  congr 1
  apply tprod_congr
  intro k
  by_cases hk : k = n ∨ k = m
  · simp [sourcePsiDoubleOmittedFactor,hk]
  · simp only [sourcePsiDoubleOmittedFactor,if_neg hk,displacedRoots,
      hab k (not_or.mp hk).1 (not_or.mp hk).2]

theorem sourcePsiZeta_fillDeletedRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (a : DeletedCoeff p n)
    (ξ : ℂ) (ψ : CoeffPair p) (z : ℂ) :
    sourcePsiZeta hp hp1 n m (sourcePsiFillDeletedRoot n a ξ) ψ z =
      sourcePsiZeta hp hp1 n m (a:Coeff p) ψ z := by
  unfold sourcePsiZeta sourcePsiDoubleOmittedProduct
  congr 1
  apply tprod_congr
  intro k
  by_cases hk : k = n ∨ k = m
  · simp [sourcePsiDoubleOmittedFactor,hk]
  · simp only [sourcePsiDoubleOmittedFactor,if_neg hk,
      displacedRoots_sourcePsiFillDeletedRoot_other n k (not_or.mp hk).1]

/-- Equation (2.24) on the entire gap complement, with no numerator-root
avoidance assumption. This includes both omitted-root and retained-root collisions. -/
theorem sourcePsiContourIntegrandJoint_eq_zeta
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)) =
      ((displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z) * sourcePsiZeta hp hp1 n m a ψ z := by
  have hn : sourceStandardRoot hp hp1 ψ n z ≠ 0 := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hz n)
  have ho := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n (fun k _ => hz k)
  have hratio : sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)) =
      I*sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))/sourceStandardRoot hp hp1 ψ n z := by
    unfold sourcePsiContourIntegrandJoint sourcePsiCandidate sourceSingleRootQuotientJointProduct
      sourceStandardRootOmittedJointProduct
    rw [sourceCanonicalRoot_eq_omitted hp hp1 n ψ z]
    field_simp [hn,ho,Complex.I_ne_zero]
    simp [Complex.I_sq]
  rw [hratio,sourceSingleRootQuotient_eq_doubleOmitted hp hp1 m n hmn.symm a ψ z (fun k _ => hz k),
    sourcePsiDoubleOmittedProduct_comm hp hp1 m n]
  unfold sourcePsiZeta
  ring

end NLS.ZakharovShabat
