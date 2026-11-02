import NLS.ComplexAnalysis.RootPeriodComparison
import NLS.ZakharovShabat.SourceTheorem12_1
import NLS.ZakharovShabat.SourceCriticalRootPeriodZero
import NLS.ZakharovShabat.SourceCriticalRootRatioFactorization
import NLS.ZakharovShabat.SourcePsiFilledRegularFactor

/-! # Actual psi-root versus critical-root period comparison

This is equation (38) of arXiv:1606.07052v1, with the deleted psi root
filled by the actual discriminant critical root, rather than the midpoint.
All products and zero periods are the existing spectral constructions.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The paper's lambda-dot at the physical source potential. -/
def sourceCriticalRoot (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (k : ℤ) : ℂ :=
  canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k

/-- The paper's zeta factor with sigma_n^n=lambda-dot_n. -/
def sourcePsiCriticalFilledQuotient (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  sourceSingleRootQuotientJointProduct hp hp1 k
    (z,(sourcePsiFillDeletedRoot n a (sourceCriticalRoot hp hp1 ψ n),ψ))

/-- The corresponding deleted product of the discriminant's critical roots. -/
def sourceCriticalDeletedQuotient (hp : p ≠ ⊤) (hp1 : 1 < p)
    (k : ℤ) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  sourceSingleRootQuotientJointProduct hp hp1 k
    (z,(canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ),ψ))

/-- The comparison equation (38), with all three actual contour terms visible. -/
def SourcePsiCriticalComparisonIdentity (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) : Prop :=
  (displacedRoots (a : Coeff p) k-sourceCriticalRoot hp hp1 ψ k)*
    (∮ z in C(c,R), ((sourceCriticalRoot hp hp1 ψ n-sourceCriticalRoot hp hp1 ψ k)/
      (sourceCriticalRoot hp hp1 ψ n-z))*sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z /
        sourceStandardRoot hp hp1 ψ k z) =
    (∮ z in C(c,R), (z-sourceCriticalRoot hp hp1 ψ k)*
      (sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z-sourceCriticalDeletedQuotient hp hp1 k ψ z)/
        sourceStandardRoot hp hp1 ψ k z) +
    (∮ z in C(c,R), (z-sourceCriticalRoot hp hp1 ψ k)^2*sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z /
      ((sourceCriticalRoot hp hp1 ψ n-z)*sourceStandardRoot hp hp1 ψ k z))

/-- Filling the unused root with the actual critical point does not change the psi integrand. -/
theorem sourcePsiContourIntegrand_critical_fill
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : DeletedCoeff p n)
    (ψ : CoeffPair p) (z : ℂ) :
    sourcePsiContourIntegrandJoint hp hp1 n
      (z,(sourcePsiFillDeletedRoot n a (sourceCriticalRoot hp hp1 ψ n),ψ)) =
      sourcePsiContourIntegrandJoint hp hp1 n (z,((a : Coeff p),ψ)) := by
  unfold sourcePsiContourIntegrandJoint
  rw [sourcePsiCandidate_eq_of_off_index hp hp1 n z
    (sourcePsiFillDeletedRoot n a (sourceCriticalRoot hp hp1 ψ n)) (a : Coeff p)
    (fun k hk => sourcePsiFillDeletedRoot_apply_other n k hk a _)]

/-- The root comparison identity on a valid spectral circle. Continuity of the
actual deleted products is supplied by the existing analytic quotient domain. -/
theorem SourceTheorem12_1Data.psi_critical_root_comparison
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V Q : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    (K : SourceLemma10_11CircleData hp hp1 V)
    (hQ : ∀ k : ℤ, AnalyticOnNhd ℂ (sourceSingleRootQuotientJointProduct hp hp1 k)
      (sourceSingleRootQuotientJointDomain hp hp1 Q k))
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (hψQ : ψ ∈ Q)
    (n k : ℤ) (hkn : k ≠ n) (P : SourceCriticalRootPeriodCircle hp hp1 ψ k)
    (havoid : ∀ z ∈ sphere (P.center : ℂ) P.radius, sourceCriticalRoot hp hp1 ψ n-z ≠ 0) :
    (displacedRoots (s n ψ : Coeff p) k-sourceCriticalRoot hp hp1 ψ k)*
      (∮ z in C((P.center : ℂ),P.radius),
        ((sourceCriticalRoot hp hp1 ψ n-sourceCriticalRoot hp hp1 ψ k)/
          (sourceCriticalRoot hp hp1 ψ n-z))*sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z /
            sourceStandardRoot hp hp1 ψ k z) =
      (∮ z in C((P.center : ℂ),P.radius),
        (z-sourceCriticalRoot hp hp1 ψ k)*
          (sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z-
            sourceCriticalDeletedQuotient hp hp1 k ψ z)/sourceStandardRoot hp hp1 ψ k z) +
      (∮ z in C((P.center : ℂ),P.radius),
        (z-sourceCriticalRoot hp hp1 ψ k)^2*sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z /
          ((sourceCriticalRoot hp hp1 ψ n-z)*sourceStandardRoot hp hp1 ψ k z)) := by
  let sigma := displacedRoots (s n ψ : Coeff p) k
  let rho := sourceCriticalRoot hp hp1 ψ k
  let nu := sourceCriticalRoot hp hp1 ψ n
  let zeta := sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ
  let chi := sourceCriticalDeletedQuotient hp hp1 k ψ
  let w := sourceStandardRoot hp hp1 ψ k
  have hcircle := P.sphere_subset_rootDomain
  have hw0 (z : ℂ) (hz : z ∈ sphere (P.center : ℂ) P.radius) : w z ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 ψ k z (hcircle hz k)
  have hqw (a : Coeff p) : ContinuousOn
      (fun z => sourceSingleRootQuotientJointProduct hp hp1 k (z,(a,ψ)))
      (sphere (P.center : ℂ) P.radius) := by
    intro z hz
    have ha := (hQ k (z,(a,ψ)) ⟨hψQ,P.closedBall_subset_omittedDomain (sphere_subset_closedBall hz)⟩).comp
      (f := fun z : ℂ => (z,(a,ψ))) (analyticAt_id.prod (analyticAt_const.prod analyticAt_const))
    exact ha.continuousAt.continuousWithinAt
  have hw : ContinuousOn w (sphere (P.center : ℂ) P.radius) :=
    (sourceStandardRoot_analyticOnNhd hp hp1 ψ k).continuousOn.mono (fun z hz => hcircle hz k)
  have hraw : (∮ z in C((P.center : ℂ),P.radius),
      sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ : Coeff p),ψ))) = 0 := by
    have hz := H.period ψ hψW n k P
    rw [if_neg hkn] at hz
    unfold sourcePsiContour at hz
    exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (by
      exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
  have hpsi : (∮ z in C((P.center : ℂ),P.radius), ((sigma-z)/w z)*(zeta z/(nu-z))) = 0 := by
    calc
      _ = -I*(∮ z in C((P.center : ℂ),P.radius),
          sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ : Coeff p),ψ))) := by
        rw [← circleIntegral.integral_const_mul]
        apply circleIntegral.integral_congr P.radius_pos.le
        intro z hz
        dsimp only
        rw [← sourcePsiContourIntegrand_critical_fill hp hp1 n (s n ψ) ψ z,
          sourcePsiContourIntegrandJoint_eq_gap_factor hp hp1 n k
            (sourcePsiFillDeletedRoot n (s n ψ) nu) ψ z (hcircle hz) (by
              rw [displacedRoots_sourcePsiFillDeletedRoot_same]
              exact (sub_ne_zero.mp (havoid z hz)).symm)]
        simp only [sourcePsiGapRegularFactor,displacedRoots_sourcePsiFillDeletedRoot_other n k hkn,
          displacedRoots_sourcePsiFillDeletedRoot_same]
        change ((sigma-z)/w z)*(zeta z/(nu-z)) =
          -I*(((sigma-z)/w z)*(I*zeta z/(nu-z)))
        ring_nf
        simp [I_sq,sub_eq_add_neg]
      _ = 0 := by rw [hraw,mul_zero]
  have hcrit : (∮ z in C((P.center : ℂ),P.radius), ((rho-z)/w z)*chi z) = 0 := by
    calc
      _ = I*(∮ z in C((P.center : ℂ),P.radius), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) := by
        rw [← circleIntegral.integral_const_mul]
        apply circleIntegral.integral_congr P.radius_pos.le
        intro z hz
        change ((rho-z)/w z)*chi z = I*(deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z)
        rw [sourceCriticalRootRatio_eq_selectedFactor_mul_extension hp hp1 ψ k z (hcircle hz)]
        change ((rho-z)/w z)*chi z = I*(((rho-z)/w z)*(-I*chi z))
        ring_nf
        simp [I_sq,sub_eq_add_neg]
      _ = 0 := by rw [K.zero ψ hψV k P,mul_zero]
  exact NLS.ComplexAnalysis.root_comparison_period_identity sigma rho nu (P.center : ℂ) P.radius
    P.radius_pos.le w zeta chi hw (hqw _) (hqw _) hw0 havoid hpsi hcrit
end NLS.ZakharovShabat
