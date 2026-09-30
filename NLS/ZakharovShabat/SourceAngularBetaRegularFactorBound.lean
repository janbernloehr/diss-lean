import NLS.ZakharovShabat.SourceAngularBetaBound
import NLS.ZakharovShabat.SourcePsiQuadraticRootOffset

/-!
# Angular bounds from the actual midpoint-filled regular factor

The gap numerator is exactly the retained psi root factor times chi,
divided by pi times the index difference. Consequently a circle bound
on chi gives the required reciprocal index difference in the beta bound.
Uniform bounds on chi and the retained roots remain to be assembled.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Filling the unused root with its midpoint leaves the numerator
unchanged and makes its index dependence explicit. -/
theorem sourceAngularGapNumerator_eq_midpointFilledRegularFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAngularGapNumerator hp hp1 n m s ψ z =
      (displacedRoots (s n ψ : Coeff p) m-z) *
        sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ z /
          ((Real.pi : ℂ)*((n-m : ℤ) : ℂ)) := by
  let b := sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)
  have hfill : sourcePsiCandidate n (z,b) = sourcePsiCandidate n (z,(s n ψ : Coeff p)) :=
    sourcePsiCandidate_eq_of_off_index hp hp1 n z b _
      (fun k hk => sourcePsiFillDeletedRoot_apply_other n k hk (s n ψ) _)
  have havoid : z ≠ displacedRoots b n := by
    rw [displacedRoots_sourcePsiFillDeletedRoot_same]
    intro he
    exact hz n (he ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have hraw := sourcePsiContourIntegrandJoint_eq_gap_factor hp hp1 n m b ψ z hz havoid
  have hleft : sourcePsiContourIntegrandJoint hp hp1 n (z,(b,ψ)) =
      sourceAngularGapNumerator hp hp1 n m s ψ z/sourceStandardRoot hp hp1 ψ m z := by
    change sourcePsiCandidate n (z,b)/sourceCanonicalRoot hp hp1 ψ z = _
    rw [hfill]
    exact sourceAngularIntegrand_eq_gapNumerator_div_standardRoot hp hp1 n m s ψ z
  rw [hleft,displacedRoots_sourcePsiFillDeletedRoot_other n m hmn] at hraw
  have hQ := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z (hz m)
  field_simp [hQ] at hraw
  have hind : ((n-m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn.symm
  rw [sourcePsiMidpointFilledRegularFactor]
  change _ = (displacedRoots (s n ψ : Coeff p) m-z) *
    ((Real.pi : ℂ)*((n-m : ℤ) : ℂ)*sourcePsiGapRegularFactor hp hp1 n m b ψ z) /
      ((Real.pi : ℂ)*((n-m : ℤ) : ℂ))
  field_simp [hind,Real.pi_ne_zero]
  exact hraw

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- The original assigned discs keep an enclosing chart circle off every
gap, permitting the actual regular-factor decomposition for all indices. -/
theorem circle_subset_canonicalRootDomain
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) :
    sphere (c m) ρ ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  intro w hw k
  by_cases hkm : k = m
  · subst k
    intro h
    have hd := mem_ball.mp (D.gap_enclosed ψ hψ h)
    rw [mem_sphere.mp hw] at hd
    linarith
  · apply ((D.disc_family ψ hψ).contour_family.2 m).2.2.1 _ k hkm
    exact mem_closedBall.mpr ((mem_sphere.mp hw).le.trans (hρR.trans D.outer_lt_assigned).le)

/-- A bound on chi supplies the reciprocal index difference, with an
explicit radius constant. The retained root enters only by its distance
from the fixed selected-disc center. -/
theorem norm_beta_le_of_midpointFilledRegularFactor_bound
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (hmn : m ≠ n)
    (ρ M : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (hM : 0 ≤ M)
    (hχ : ∀ w ∈ sphere (c m) ρ,
      ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ w‖ ≤ M) :
    ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤
      (ρ^2*(‖displacedRoots (s n ψ : Coeff p) m-c m‖+ρ)*M/(ρ-r)^3) *
        (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
          ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
            sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)| := by
  let A := ‖displacedRoots (s n ψ : Coeff p) m-c m‖+ρ
  let d := |((n-m : ℤ) : ℝ)|
  have hρ : 0 < ρ := D.inner_pos.trans hrρ
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hd : 0 < d := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hmn.symm)
  have hg (w : ℂ) (hw : w ∈ sphere (c m) ρ) :
      ‖sourceAngularGapNumerator hp hp1 n m s ψ w‖ ≤ A*M/(Real.pi*d) := by
    rw [sourceAngularGapNumerator_eq_midpointFilledRegularFactor hp hp1 n m hmn s ψ w
      (D.circle_subset_canonicalRootDomain ψ hψ ρ hrρ hρR hw),norm_div,norm_mul,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_intCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul _ (hχ w hw) (norm_nonneg _) hA
    have h := norm_sub_le (displacedRoots (s n ψ : Coeff p) m-c m) (w-c m)
    have hnorm : ‖w-c m‖ = ρ := by simpa only [mem_sphere,dist_eq_norm] using hw
    rw [show displacedRoots (s n ψ : Coeff p) m-c m-(w-c m) =
      displacedRoots (s n ψ : Coeff p) m-w by ring,hnorm] at h
    exact h
  have h := D.norm_beta_le_of_gapNumerator_bound ψ hψ n hmn ρ (A*M/(Real.pi*d)) hrρ hρR
    (by positivity) hg
  have hweight :
      ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-sourceStandardRootMidpoint hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
        ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-sourceStandardRootMidpoint hp hp1 ψ m‖ := by
    nlinarith [norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ m)]
  apply h.trans
  calc
    _ ≤ (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
      ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-sourceStandardRootMidpoint hp hp1 ψ m‖) *
        (Real.pi*ρ^2*(A*M/(Real.pi*d))/(ρ-r)^3) :=
      mul_le_mul_of_nonneg_right hweight (by positivity)
    _ = _ := by
      change _ = (ρ^2*A*M/(ρ-r)^3) * _ / d
      field_simp

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
