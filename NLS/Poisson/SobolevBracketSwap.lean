import NLS.Poisson.SobolevSourceCompatibility
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! # Antisymmetry on the full common Sobolev domain

Exchanging the two functionals exchanges their ambient domains. The order
normalization below preserves every signed coefficient and makes that
exchange explicit, including the actual common base point.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Poisson
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Pair order normalization preserves the original component-sum topology. -/
def negNegPairEquiv (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeffPair (Weight.sobolev (-(-s))) p ≃L[ℂ] WeightedCoeffPair (Weight.sobolev s) p :=
  (WeightedCoeffPair.toMax _ p).trans
    (((negNegIsometry s).toContinuousLinearEquiv.prodCongr
      (negNegIsometry s).toContinuousLinearEquiv).trans (WeightedCoeffPair.toMax _ p).symm)

@[simp] theorem negNegPairEquiv_fst (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev (-(-s))) p) (n : ℤ) :
    (negNegPairEquiv s p a).fst.val n = a.fst.val n := negNegIsometry_val s _ n

@[simp] theorem negNegPairEquiv_snd (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev (-(-s))) p) (n : ℤ) :
    (negNegPairEquiv s p a).snd.val n = a.snd.val n := negNegIsometry_val s _ n

@[simp] theorem negNegPairEquiv_symm_fst (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) p) (n : ℤ) :
    ((negNegPairEquiv s p).symm a).fst.val n = a.fst.val n := negNegIsometry_symm_val s _ n

@[simp] theorem negNegPairEquiv_symm_snd (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) p) (n : ℤ) :
    ((negNegPairEquiv s p).symm a).snd.val n = a.snd.val n := negNegIsometry_symm_val s _ n

@[simp] theorem negNegPairEquiv_inl_mode (s : ℝ) (n : ℤ) :
    negNegPairEquiv s p (WeightedCoeffPair.inlCLM _
      (WeightedCoeff.ofFinsupp _ p (Finsupp.single n 1))) =
      WeightedCoeffPair.inlCLM _ (WeightedCoeff.ofFinsupp _ p (Finsupp.single n 1)) := by
  apply (WeightedCoeffPair.toMax _ p).injective
  apply Prod.ext
  · apply Subtype.ext
    funext k
    exact negNegPairEquiv_fst s _ k
  · apply Subtype.ext
    funext k
    exact negNegPairEquiv_snd s _ k

@[simp] theorem negNegPairEquiv_inr_mode (s : ℝ) (n : ℤ) :
    negNegPairEquiv s p (WeightedCoeffPair.inrCLM _
      (WeightedCoeff.ofFinsupp _ p (Finsupp.single n 1))) =
      WeightedCoeffPair.inrCLM _ (WeightedCoeff.ofFinsupp _ p (Finsupp.single n 1)) := by
  apply (WeightedCoeffPair.toMax _ p).injective
  apply Prod.ext
  · apply Subtype.ext
    funext k
    exact negNegPairEquiv_fst s _ k
  · apply Subtype.ext
    funext k
    exact negNegPairEquiv_snd s _ k

/-- Exchange the two original representatives of the very same physical state. -/
def swapCommonState (s : ℝ) (x : SobolevCommonState s p q) : SobolevCommonState (-s) q p :=
  commonStateOfCoefficients (-s) ((negNegPairEquiv s p).symm x.val.2) x.val.1 (by
    intro n
    simp only [negNegPairEquiv_symm_fst,negNegPairEquiv_symm_snd]
    exact ⟨(commonState_coefficients s x n).1.symm,(commonState_coefficients s x n).2.symm⟩)

variable [p.HolderConjugate q]

/-- Antisymmetry of the full cotangent pairing with its original source domains. -/
theorem conjugateBivector_swap (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (L : WeightedCoeffPair (Weight.sobolev (-s)) q →L[ℂ] ℂ)
    (M : WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ) :
    conjugateBivector s hp hq L M = -conjugateBivector (-s) hq hp
      (M.comp (negNegPairEquiv s p).toContinuousLinearMap) L := by
  rw [conjugateBivector_eq_tsum,conjugateBivector_eq_tsum]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    negNegPairEquiv_inl_mode,negNegPairEquiv_inr_mode]
  rw [← mul_neg,← tsum_neg]
  congr 1
  apply tsum_congr
  intro n
  ring

/-- The two actual function brackets are negatives after exchanging their domains and state. -/
theorem commonSobolevBracket_swap (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (F : WeightedCoeffPair (Weight.sobolev (-s)) q → ℂ)
    (G : WeightedCoeffPair (Weight.sobolev s) p → ℂ) (x : SobolevCommonState s p q) :
    commonSobolevBracket s hp hq F G x =
      -commonSobolevBracket (-s) hq hp (G ∘ negNegPairEquiv s p) F (swapCommonState s x) := by
  change conjugateBivector s hp hq (fderiv ℂ F x.val.1) (fderiv ℂ G x.val.2) =
    -conjugateBivector (-s) hq hp
      (fderiv ℂ (G ∘ negNegPairEquiv s p) ((negNegPairEquiv s p).symm x.val.2))
      (fderiv ℂ F x.val.1)
  rw [ContinuousLinearEquiv.comp_right_fderiv,ContinuousLinearEquiv.apply_symm_apply]
  exact conjugateBivector_swap s hp hq _ _

/-- The right product rule on the full common domain. -/
theorem commonSobolevBracket_mul_right (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (F : WeightedCoeffPair (Weight.sobolev (-s)) q → ℂ)
    (G H : WeightedCoeffPair (Weight.sobolev s) p → ℂ) (x : SobolevCommonState s p q)
    (hG : DifferentiableAt ℂ G x.val.2) (hH : DifferentiableAt ℂ H x.val.2) :
    commonSobolevBracket s hp hq F (fun y => G y*H y) x =
      G x.val.2*commonSobolevBracket s hp hq F H x + H x.val.2*commonSobolevBracket s hp hq F G x := by
  rw [commonSobolevBracket,fderiv_fun_mul hG hH]
  simp only [map_add,map_smul,smul_eq_mul]
  rfl

end NLS.Poisson
