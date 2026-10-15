import NLS.ZakharovShabat.SourceLemma12_11

/-!
# Equations (2.30), (2.31), and (2.33) on original circles

The actual equation, original-circle geometry, and actual single quotient
give the source identities at every complex point of the unchanged domain.
The construction witness retained in Lemma 12.10 supplies a common positive
midpoint lower bound for this exact family.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Original circle geometry makes the literal midpoint-filled chi analytic. -/
theorem SourceLemma12_11Data.original_chi_analytic
    (H : SourceLemma12_11Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    AnalyticOnNhd ℂ (sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ)
      (closedBall (P.center:ℂ) P.radius) := by
  intro z hz
  have hdom := P.closedBall_subset_omittedDomain hz
  have hQ := H.previous.psi.previous.quotients.spectral ψ (H.previous.subset hψ)
    (sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)) m z hdom
  have hn : sourceStandardRootMidpoint hp hp1 ψ n-z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    exact hdom n hmn.symm (heq ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  unfold sourcePsiMidpointFilledRegularFactor sourcePsiGapRegularFactor
  rw [displacedRoots_sourcePsiFillDeletedRoot_same]
  exact analyticAt_const.mul ((analyticAt_const.mul hQ).div (analyticAt_const.sub analyticAt_id) hn)

/-- Equation (2.30) on every original circle, directly from the actual original equation. -/
theorem SourceLemma12_11Data.original_chi_zero_period
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    (∮ z in C((P.center:ℂ),P.radius),
      ((displacedRoots (s n ψ:Coeff p) m-z)/sourceStandardRoot hp hp1 ψ m z)*
        sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ z) = 0 := by
  apply sourcePsiMidpointFilledRegularFactor_zero_period hp hp1 n m hmn (s n ψ) ψ
    (P.center:ℂ) P.radius P.radius_pos.le P.sphere_subset_rootDomain
  · intro z hz heq
    exact P.sphere_subset_rootDomain hz n (heq ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  · exact H.previous.original_retained_contour_zero hW₀ ψ hψ n m hmn P

/-- Equation (2.33) for the exact original family and any original circle. -/
theorem SourceLemma12_11Data.original_chi_dslope_identity
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    (2*Real.pi*I:ℂ)*(displacedRoots (s n ψ:Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m)*
      sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ (sourceStandardRootMidpoint hp hp1 ψ m) =
        ∮ z in C((P.center:ℂ),P.radius),
          ((displacedRoots (s n ψ:Coeff p) m-z)*(z-sourceStandardRootMidpoint hp hp1 ψ m)/
            sourceStandardRoot hp hp1 ψ m z)*
              dslope (sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ)
                (sourceStandardRootMidpoint hp hp1 ψ m) z := by
  apply sourceStandardRoot_zero_period_dslope_identity hp hp1 ψ m (P.center:ℂ)
    (displacedRoots (s n ψ:Coeff p) m) P.radius P.radius_pos P.gap _
    (H.original_chi_analytic ψ hψ n m hmn P)
  exact H.original_chi_zero_period hW₀ ψ hψ n m hmn P

/-- Equation (2.31), including the minus sign in the literal single quotient (2.25). -/
theorem sourcePsiMidpointFilledRegularFactor_eq_literal_product
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z =
      ((Real.pi:ℂ)*((n-m:ℤ):ℂ))/(I*(sourceStandardRootMidpoint hp hp1 ψ n-z))*
        (-(∏' k : {k : ℤ // k ≠ m},
          (displacedRoots (sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n)) k-z)/
            sourceStandardRoot hp hp1 ψ k z)) := by
  rw [← sourcePsi_zetaSingle_eq_product hp hp1 m _ ψ z hz]
  unfold sourcePsiMidpointFilledRegularFactor sourcePsiGapRegularFactor
  rw [displacedRoots_sourcePsiFillDeletedRoot_same]
  have hn : sourceStandardRootMidpoint hp hp1 ψ n-z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    exact hz n hmn.symm (heq ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  field_simp
  simp [Complex.I_sq]

/-- The original construction's midpoint lower bound is retained on exactly W. -/
theorem SourceLemma12_11Data.original_midpoint_lower_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧ V ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ χ ∈ V, ∀ n m : ℤ, m ≠ n →
        C ≤ ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n χ) χ
          (sourceStandardRootMidpoint hp hp1 χ m)‖ := by
  obtain ⟨A,hdom,hbranch⟩ := H.previous.atlas
  simpa only [hdom,hbranch] using
    A.toSourcePsiMidpointBoundComplexRootAtlas.locally_uniform_midpoint_lower_bounds ψ (hdom ▸ hψ)


end NLS.ZakharovShabat
