import NLS.ZakharovShabat.SourceAbelianMomentEvenNumerator
import NLS.ZakharovShabat.SourceFullAbelianSquareJointAnalytic

/-! # Joint analyticity of the filled even-moment numerator

The normalized psi branch and canonical filled square may be varied
jointly with the spectral parameter. The selected cut is filled, including
both endpoints and endpoint collisions; only the other gaps are excluded.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The regular psi numerator is jointly analytic along any analytic
coefficient branch on the selected-root omitted domain. -/
theorem sourceMomentRegularNumerator_joint_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (U : Set (CoeffPair p)) (n k : ℤ)
    (a : CoeffPair p → Coeff p) (ha : AnalyticOnNhd ℂ a U)
    (hO : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 k)
      (sourceStandardRootOmittedJointDomain hp hp1 U k)) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceMomentRegularNumerator hp hp1 n k (a t.2) t.2 t.1)
      (sourceStandardRootOmittedJointDomain hp hp1 U k) := by
  intro t ht
  have hbranch := (ha t.2 ht.1).comp (f := fun t : ℂ × CoeffPair p => t.2) analyticAt_snd
  have hnum := (analyticOnNhd_sourcePsiCandidate hp hp1 n (t.1,a t.2) (mem_univ _)).comp
    (f := fun t : ℂ × CoeffPair p => (t.1,a t.2)) (analyticAt_fst.prod hbranch)
  exact hnum.div (analyticAt_const.mul (hO t ht))
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 t.2 t.1 k ht.2))

/-- Every filled even-moment numerator inherits joint analyticity from
the square and psi branch, without choosing individual analytic endpoints. -/
theorem sourceAbelianMomentEvenNumerator_joint_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W U : Set (CoeffPair p)) (n k : ℤ) (m : ℕ)
    (a : CoeffPair p → Coeff p) (ha : AnalyticOnNhd ℂ a U)
    (hO : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 k)
      (sourceStandardRootOmittedJointDomain hp hp1 U k))
    (hS : AnalyticOnNhd ℂ (sourceFullAbelianSquare hp hp1 W k)
      (sourceStandardRootOmittedJointDomain hp hp1 U k)) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
      sourceAbelianMomentEvenNumerator hp hp1 W n k m (a t.2) t.2 t.1)
      (sourceStandardRootOmittedJointDomain hp hp1 U k) := by
  intro t ht
  exact ((hS t ht).pow m).mul (sourceMomentRegularNumerator_joint_analytic hp hp1 U n k a ha hO t ht)

/-- Specialization to the actual normalized psi branch used by the moment atlas. -/
theorem SourcePsiNormalizedComplexExtension.evenNumerator_joint_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s)
    (W U : Set (CoeffPair p)) (hUV : U ⊆ V) (n k : ℤ) (m : ℕ)
    (hO : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 k)
      (sourceStandardRootOmittedJointDomain hp hp1 U k))
    (hS : AnalyticOnNhd ℂ (sourceFullAbelianSquare hp hp1 W k)
      (sourceStandardRootOmittedJointDomain hp hp1 U k)) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
      sourceAbelianMomentEvenNumerator hp hp1 W n k m (s n t.2 : Coeff p) t.2 t.1)
      (sourceStandardRootOmittedJointDomain hp hp1 U k) := by
  have hbranch : AnalyticOnNhd ℂ (fun ψ => (s n ψ : Coeff p)) U := by
    intro ψ hψ
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL.analyticAt (s n ψ)).comp
      (hs.analytic n ψ (hUV hψ))
  exact sourceAbelianMomentEvenNumerator_joint_analytic hp hp1 W U n k m
    (fun ψ => (s n ψ : Coeff p)) hbranch hO hS

end NLS.ZakharovShabat
