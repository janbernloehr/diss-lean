import NLS.ZakharovShabat.SourcePsiJacobianOffDiagonalEstimate
import NLS.ZakharovShabat.SourcePsiNearFreeCollapsedGap

/-!
# Off-diagonal psi Jacobian at a collapsed periodic gap

When the selected standard gap collapses, its square root is linear.
The off-diagonal root-variation integral is then a Cauchy residue of
the regular factor divided by the varied-root factor. Its value is
the same quotient expression as the open-gap mean-value formula,
evaluated at the periodic midpoint.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- At a collapsed selected gap, an off-diagonal Jacobian entry is
the regular quotient and root ratio evaluated at the midpoint. -/
theorem sourcePsi_offDiagonalJacobian_collapsedGap_eq_quotient
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m k : ℤ) (hkn : k ≠ n) (a : DeletedCoeff p n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere c R,
      z ≠ displacedRoots (a : Coeff p) n)
    (havoidk : ∀ z ∈ closedBall c R,
      z ≠ displacedRoots (a : Coeff p) k)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall c R)) :
    deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n k hkn t) ψ c R) 0 =
      2*(Real.pi : ℂ)*
        (((displacedRoots (a : Coeff p) m-
            sourceStandardRootMidpoint hp hp1 ψ m) /
          (displacedRoots (a : Coeff p) k-
            sourceStandardRootMidpoint hp hp1 ψ m)) *
          ((((n-m : ℤ) : ℂ) *
            sourceSingleRootQuotientJointProduct hp hp1 m
              (sourceStandardRootMidpoint hp hp1 ψ m,
                ((a : Coeff p),ψ))) /
            (displacedRoots (a : Coeff p) n-
              sourceStandardRootMidpoint hp hp1 ψ m))) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let σ := displacedRoots (a : Coeff p) m
  let F : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  let f : ℂ → ℂ := fun z => F z /
    (displacedRoots (a : Coeff p) k-z)
  have hf : AnalyticOnNhd ℂ f (closedBall c R) := by
    intro z hz
    have hden : displacedRoots (a : Coeff p) k-z ≠ 0 :=
      sub_ne_zero.mpr (havoidk z hz).symm
    exact (hreg z hz).div
      (analyticAt_const.sub analyticAt_id) hden
  have hJ := deriv_sourcePsiDeletedEquationCoordinate_eq_gap_factor_circleIntegral
    hp hp1 n m k hkn a ψ hreal c R hR.le hcircle havoidn
      (fun z hz => havoidk z (sphere_subset_closedBall hz))
  have hJ' :
      deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n k hkn t) ψ c R) 0 =
      ∮ z in C(c,R), ((σ-z)/(τ-z))*f z := by
    rw [hJ]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    dsimp only
    rw [sourceStandardRoot_of_zeroGap hp hp1 ψ m z hgap]
    change ((σ-z)/(displacedRoots (a : Coeff p) k-z)) *
        (F z/(τ-z)) = ((σ-z)/(τ-z))*f z
    dsimp [f]
    ring
  have hres := circleIntegral_collapsedGap_ratio_of_mem_ball
    c τ σ R hR hmid f hf
  rw [hJ',hres]
  have hfactor := sourcePsi_diagonal_rotatedFactor_eq_quotient
    hp hp1 n m (a : Coeff p) ψ τ
  change (2*(Real.pi : ℂ)*I)*(τ-σ)*
      (F τ/(displacedRoots (a : Coeff p) k-τ)) = _
  calc
    (2*(Real.pi : ℂ)*I)*(τ-σ)*
        (F τ/(displacedRoots (a : Coeff p) k-τ)) =
      2*(Real.pi : ℂ)*
        (((σ-τ)/(displacedRoots (a : Coeff p) k-τ)) *
          ((-I)*(((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m
              (a : Coeff p) ψ τ))) := by dsimp [F]; ring
    _ = _ := by rw [hfactor]

end NLS.ZakharovShabat
