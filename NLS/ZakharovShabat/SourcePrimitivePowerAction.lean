import NLS.ZakharovShabat.SourcePrimitivePowerAtlas
import NLS.ZakharovShabat.SourceRealActionRealCenteredCircle
import NLS.ComplexAnalysis.CircleIntegralIntegrationByParts

/-! # The first primitive-power moment is the spectral action

Integration by parts on the circle identifies the first moment with
the original action contour. Each moment chart is therefore also a
valid action chart, giving equality with the glued complex action on
the entire common moment domain, including collapsed gaps.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Closed-contour integration by parts, with the exact Section 21 sign. -/
theorem sourcePrimitivePowerCircle_one_eq_actionCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (n : ℤ)
    (ψ : CoeffPair p) (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    sourcePrimitivePowerCircle hp hp1 W n 1 ψ c R = sourceActionCircle hp hp1 ψ c R := by
  let F : ℂ → ℂ := fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ)
  have hi := circleIntegral_mul_deriv_eq_neg_of_analyticOnNhd F
    (sourceOpenGapComplement hp hp1 ψ) (sourceFullAbelianPrimitive_spectral_analytic D n)
    c R hR (hc.trans (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ))
  have he : (∮ z in C(c,R), z * sourceCriticalRootRatioJoint hp hp1 (z,ψ)) =
      ∮ z in C(c,R), z * deriv F z := by
    apply circleIntegral.integral_congr hR
    intro z hz
    exact congrArg (fun v : ℂ => z*v) (sourceFullAbelianPrimitive_hasDerivAt D n z (hc hz)).deriv.symm
  simp only [sourcePrimitivePowerCircle,pow_one,sourceActionCircle,he,hi,neg_mul,mul_neg]
  rfl

namespace SourcePrimitivePowerLocalChart
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable {φ : realTypeSourceLocus p}

/-- The first-moment chart supplies an actual action chart on the same ball. -/
def actionChart (L : SourcePrimitivePowerLocalChart hp hp1 W φ) (n : ℤ) :
    SourceRealActionBallChart hp hp1 n where
  center := φ.val
  center_real := φ.property
  radius := L.radius
  radius_pos := L.radius_pos
  spectralCenter := L.center n
  spectralRadius := L.contourRadius n
  spectralRadius_pos := (L.family φ.val (mem_ball_self L.radius_pos)).2 n |>.1
  geometry := fun ψ hψ => ⟨(L.family ψ hψ).2 n |>.2.1,(L.family ψ hψ).2 n |>.2.2.1⟩
  differentiable := by
    apply (L.analytic n 1).differentiableOn.congr
    intro ψ hψ
    obtain ⟨D⟩ := L.charts ψ hψ
    exact (sourcePrimitivePowerCircle_one_eq_actionCircle hp hp1 W n ψ D _ _
      ((L.family ψ hψ).2 n).1.le ((L.family ψ hψ).2 n).2.2.2).symm
  agrees_real := by
    intro ψ hψ hreal
    have hF := L.family ψ hψ
    exact sourceRealAction_eq_realCentered_enclosingCircle hp hp1 ψ hreal n _ _
      (hF.1 n) (hF.2 n).1 (hF.2 n).2.1 (hF.2 n).2.2.1

end SourcePrimitivePowerLocalChart
namespace SourcePrimitivePowerAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- The common moment domain is contained in every indexed action domain. -/
theorem domain_subset_actionDomain (n : ℤ) : A.domain ⊆ sourceComplexActionDomain hp hp1 n := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact ⟨(A.localChart φ).actionChart n,hφ⟩

/-- Lemma 21.1(v) on the full complex source domain. -/
theorem moment_one (n : ℤ) : EqOn (A.moment n 1) (sourceComplexAction hp hp1 n) A.domain := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  obtain ⟨D⟩ := (A.localChart φ).charts ψ hφ
  have hF := (A.localChart φ).family ψ hφ
  exact (A.moment_eq_local n 1 φ hφ).trans
    ((sourcePrimitivePowerCircle_one_eq_actionCircle hp hp1 W n ψ D _ _
      (hF.2 n).1.le (hF.2 n).2.2.2).trans
      (sourceComplexAction_eq_chart hp hp1 n ((A.localChart φ).actionChart n) ψ hφ).symm)

end SourcePrimitivePowerAtlas

/-- The analytic primitive-power moments of Lemma 21.1, their even and
collapsed-gap vanishing, and their first-order action identity all hold
on one common open source neighborhood. -/
theorem exists_sourcePrimitivePower_moments (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W U : Set (CoeffPair p), IsOpen W ∧ IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧
      ∃ M : ℤ → ℕ → CoeffPair p → ℂ,
        (∀ n m, AnalyticOnNhd ℂ (M n m) U) ∧
        (∀ ψ ∈ U, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
          sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
          ∀ n m, M n m ψ = sourcePrimitivePowerCircle hp hp1 W n m ψ (c n) (R n)) ∧
        (∀ ψ ∈ U, ∀ n m, M n (2*m) ψ = 0) ∧
        (∀ ψ ∈ U, ∀ n,
          canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 →
          ∀ m, M n m ψ = 0) ∧
        (∀ n, EqOn (M n 1) (sourceComplexAction hp hp1 n) U) := by
  obtain ⟨W,hW,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas hp hp1
  exact ⟨W,A.domain,hW,A.isOpen_domain,A.realType_subset_domain,A.moment,
    A.analytic_moment,A.circle_representation,A.moment_even,A.moment_of_collapsed,A.moment_one⟩

end NLS.ZakharovShabat
