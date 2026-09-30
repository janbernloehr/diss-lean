import NLS.ZakharovShabat.SourcePsiMidpointDenominator
import NLS.ZakharovShabat.SourcePsiQuadraticRootOffset

/-!
# Moving omitted-midpoint estimates on shifted selected discs

A bounded omitted-midpoint displacement preserves half the lattice
separation once the index difference dominates the selected disc's
shift and radius. A quotient bound then controls the actual chi factor
uniformly for distant deleted indices on a fixed selected disc.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Both the omitted root and the selected disc may move from their
free lattice points; their two shifts enter the same separation budget. -/
theorem shifted_root_shifted_disc_distance_lower
    (n m : ℤ) (ξ c : ℂ) (R : ℝ)
    (hsep : 2*(‖ξ-(Real.pi:ℂ)*n‖+‖c-(Real.pi:ℂ)*m‖+R) ≤
      Real.pi*|((n-m : ℤ) : ℝ)|) (z : ℂ) (hz : z ∈ closedBall c R) :
    (Real.pi/2)*|((n-m : ℤ) : ℝ)| ≤ ‖ξ-z‖ := by
  have hzR : ‖z-c‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have htri : ‖(Real.pi:ℂ)*n-(Real.pi:ℂ)*m‖ ≤
      ‖ξ-(Real.pi:ℂ)*n‖+‖ξ-z‖+‖z-c‖+‖c-(Real.pi:ℂ)*m‖ := by
    rw [show (Real.pi:ℂ)*n-(Real.pi:ℂ)*m =
      ((Real.pi:ℂ)*n-ξ)+(ξ-z)+(z-c)+(c-(Real.pi:ℂ)*m) by ring]
    have h : ‖((Real.pi:ℂ)*n-ξ)+(ξ-z)+(z-c)+(c-(Real.pi:ℂ)*m)‖ ≤
        ‖(Real.pi:ℂ)*n-ξ‖+‖ξ-z‖+‖z-c‖+‖c-(Real.pi:ℂ)*m‖ := (norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    simpa only [norm_sub_rev] using h
  rw [norm_free_center_sub n m] at htri
  linarith

/-- Half the lattice denominator gives the same chi bound on any
shifted selected disc, including a central nonstandard disc. -/
theorem norm_sourcePsiMidpointFilledRegularFactor_le_of_quotient_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (z : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hsep : (Real.pi/2)*|((n-m : ℤ) : ℝ)| ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖)
    (hQ : ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))‖ ≤ M) :
    ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z‖ ≤ 2*M := by
  have hd : 0 < |((n-m : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hmn.symm)
  have hden : 0 < ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖ := by nlinarith [Real.pi_pos]
  simp only [sourcePsiMidpointFilledRegularFactor,sourcePsiGapRegularFactor,
    displacedRoots_sourcePsiFillDeletedRoot_same,norm_mul,norm_div,norm_I,one_mul,
    Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ Real.pi*|((n-m : ℤ) : ℝ)| * M := mul_le_mul_of_nonneg_left hQ (by positivity)
    _ ≤ 2*M*‖sourceStandardRootMidpoint hp hp1 ψ n-z‖ := by nlinarith [mul_le_mul_of_nonneg_left hsep hM]

end NLS.ZakharovShabat
