import NLS.ZakharovShabat.SourcePsiLimitQuotient
import NLS.ZakharovShabat.SourcePsiGapFactorization
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The fixed-row selected-index factor at infinity

For a fixed row and spectral point, the factor
`π(n-m)/(πn-z)` approaches one as the deleted index escapes in
either direction. Together with convergence of the omitted-coordinate
quotient, this identifies the pointwise limit of the weighted regular
factor in Lemma 12.10.
-/

noncomputable section
open Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The elementary deleted-index factor from (2.28), with the
omitted root fixed at its free center. -/
def sourcePsiDeletedIndexRatio (n m : ℤ) (z : ℂ) : ℂ :=
  ((Real.pi : ℂ) * ((n-m : ℤ) : ℂ)) / ((Real.pi : ℂ) * n-z)

/-- Free lattice centers escape in norm along the two-sided deleted
index filter. -/
theorem tendsto_norm_freeCenter_at_natAbs :
    Tendsto (fun n : ℤ => ‖(Real.pi : ℂ) * n‖)
      (Filter.comap Int.natAbs Filter.atTop) Filter.atTop := by
  have hnat : Tendsto (fun n : ℤ => (n.natAbs : ℝ))
      (Filter.comap Int.natAbs Filter.atTop) Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_comap
  have hmul := hnat.const_mul_atTop Real.pi_pos
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,Complex.norm_intCast,
    Nat.cast_natAbs,Int.cast_abs] using hmul

/-- The fixed spectral point is far from the omitted free center
when the deleted index escapes. -/
theorem tendsto_norm_freeCenter_sub_at_natAbs (z : ℂ) :
    Tendsto (fun n : ℤ => ‖(Real.pi : ℂ)*n-z‖)
      (Filter.comap Int.natAbs Filter.atTop) Filter.atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [tendsto_norm_freeCenter_at_natAbs.eventually_ge_atTop
    (B+‖z‖)] with n hn
  have htri := norm_le_norm_sub_add ((Real.pi : ℂ)*n) z
  linarith

/-- Equation (2.28): the selected-index factor tends to one at
each fixed spectral point as `|n|` grows. -/
theorem tendsto_sourcePsiDeletedIndexRatio
    (m : ℤ) (z : ℂ) :
    Tendsto (fun n : ℤ => sourcePsiDeletedIndexRatio n m z)
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 1) := by
  have hden := tendsto_norm_freeCenter_sub_at_natAbs z
  have hsmall : Tendsto
      (fun n : ℤ => (z-(Real.pi : ℂ)*m) / ((Real.pi : ℂ)*n-z))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_div] using hden.const_div_atTop ‖z-(Real.pi : ℂ)*m‖
  have hne : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      (Real.pi : ℂ)*n-z ≠ 0 := by
    filter_upwards [hden.eventually_ge_atTop 1] with n hn
    exact norm_ne_zero_iff.mp (by linarith)
  have heq : (fun n : ℤ => sourcePsiDeletedIndexRatio n m z) =ᶠ[
      Filter.comap Int.natAbs Filter.atTop]
      (fun n => 1+(z-(Real.pi : ℂ)*m)/((Real.pi : ℂ)*n-z)) := by
    filter_upwards [hne] with n hn
    unfold sourcePsiDeletedIndexRatio
    have hnum : (Real.pi : ℂ)*((n-m : ℤ) : ℂ) =
        (Real.pi : ℂ)*n-(Real.pi : ℂ)*m := by push_cast; ring
    rw [hnum]
    field_simp [hn]
    ring
  have hlimit := (tendsto_const_nhds (x := (1 : ℂ))).add hsmall
  simpa using hlimit.congr' heq.symm

/-- At fixed row and spectral point, the weighted regular factor
formed from a full root sequence with coordinate `n` deleted tends
to the undeleted single-root quotient, with the normalization from
the dissertation's `Q*` matrix. -/
theorem tendsto_sourcePsiGapRegularFactor_deletedIndex
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (z : ℂ) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (a : Coeff p) :
    Tendsto (fun n : ℤ =>
      (Real.pi : ℂ) * (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m
          (Coeff.deleteCoordinate n a) ψ z))
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (I * sourceSingleRootQuotientJointProduct hp hp1 m
        (z,(a,ψ)))) := by
  have hquot := tendsto_sourceSingleRootQuotient_deleteCoordinate
    hp hp1 m ψ hψ z hz a
  have hratio := tendsto_sourcePsiDeletedIndexRatio m z
  have hprod := ((tendsto_const_nhds (x := I)).mul hquot).mul hratio
  have heq (n : ℤ) :
      (Real.pi : ℂ) * (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m
          (Coeff.deleteCoordinate n a) ψ z) =
      (I * sourceSingleRootQuotientJointProduct hp hp1 m
        (z,(Coeff.deleteCoordinate n a,ψ))) *
        sourcePsiDeletedIndexRatio n m z := by
    have hn : displacedRoots (Coeff.deleteCoordinate n a) n =
        (Real.pi : ℂ)*n := by
      simp [displacedRoots,Coeff.deleteCoordinate_apply_same]
    dsimp only [sourcePsiGapRegularFactor,sourcePsiDeletedIndexRatio]
    rw [hn]
    ring
  simpa only [mul_one] using
    hprod.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)

/-- The candidate `Q*` scalar matrix integrand, scaled by `π` so
that its normalized factor has a simple pointwise limit. -/
def sourcePsiLimitMatrixIntegrand
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  ((displacedRoots a m-z)/(displacedRoots a k-z)) *
    ((I * sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))) /
      sourceStandardRoot hp hp1 ψ m z)

/-- At a fixed spectral point, the retained-entry integrand of the
extended selected Jacobian approaches the candidate `Q*` integrand.
The deleted index eventually differs from the fixed row and column. -/
theorem tendsto_sourcePsi_fullJacobianIntegrand_deletedIndex
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (z : ℂ) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (a : Coeff p) :
    Tendsto (fun n : ℤ =>
      (Real.pi : ℂ) *
        (((displacedRoots (Coeff.deleteCoordinate n a) m-z) /
            (displacedRoots (Coeff.deleteCoordinate n a) k-z)) *
          ((((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m
              (Coeff.deleteCoordinate n a) ψ z) /
                sourceStandardRoot hp hp1 ψ m z)))
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (sourcePsiLimitMatrixIntegrand hp hp1 m k a ψ z)) := by
  let ratio : ℂ := (displacedRoots a m-z)/(displacedRoots a k-z)
  have hreg := tendsto_sourcePsiGapRegularFactor_deletedIndex
    hp hp1 m ψ hψ z hz a
  have hlim := (hreg.const_mul ratio).div_const
    (sourceStandardRoot hp hp1 ψ m z)
  have hne : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      n ≠ m ∧ n ≠ k := by
    apply eventually_comap.mpr
    apply eventually_atTop.mpr
    refine ⟨max m.natAbs k.natAbs + 1,?_⟩
    intro j hj n hn
    constructor
    · intro hnm
      subst n
      omega
    · intro hnk
      subst n
      omega
  have heq : (fun n : ℤ =>
      (Real.pi : ℂ) *
        (((displacedRoots (Coeff.deleteCoordinate n a) m-z) /
            (displacedRoots (Coeff.deleteCoordinate n a) k-z)) *
          ((((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m
              (Coeff.deleteCoordinate n a) ψ z) /
                sourceStandardRoot hp hp1 ψ m z))) =ᶠ[
        Filter.comap Int.natAbs Filter.atTop]
      (fun n => ratio *
        ((Real.pi : ℂ) * (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m
            (Coeff.deleteCoordinate n a) ψ z)) /
              sourceStandardRoot hp hp1 ψ m z) := by
    filter_upwards [hne] with n hn
    have hm : displacedRoots (Coeff.deleteCoordinate n a) m =
        displacedRoots a m := by
      simp [displacedRoots,Coeff.deleteCoordinate_apply_other n m (Ne.symm hn.1)]
    have hk : displacedRoots (Coeff.deleteCoordinate n a) k =
        displacedRoots a k := by
      simp [displacedRoots,Coeff.deleteCoordinate_apply_other n k (Ne.symm hn.2)]
    rw [hm,hk]
    dsimp only [ratio]
    ring
  simpa only [sourcePsiLimitMatrixIntegrand,ratio,mul_div_assoc] using
    hlim.congr' heq.symm

end NLS.ZakharovShabat
