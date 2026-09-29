import NLS.ZakharovShabat.SourcePsiCommonJacobianRootVariation
import NLS.SequenceSpaces.MatrixLimitNormBound

/-!
# Continuity and a common inverse bound on the full gap product

The eventual root Lipschitz estimate for the actual Jacobians passes
through their basis-entry limits to the intrinsic operator `Q*`.
This gives operator-norm continuity on the compact full gap product.
Its pointwise bijectivity then supplies a common inverse norm bound
over all gap-root vectors at the fixed real-type potential.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual limit operator is locally Lipschitz in operator norm
as its full gap-contained root vector varies. -/
theorem exists_local_lipschitz_sourcePsiGapLimitOperator
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ b d : sourcePeriodicGapRootSet hp hp1 φ,
        b.val ∈ ball a.val r → d.val ∈ ball a.val r →
        ‖sourcePsiGapLimitOperator hp hp1 φ hφ b -
            sourcePsiGapLimitOperator hp hp1 φ hφ d‖ ≤ L*‖b.val-d.val‖ := by
  obtain ⟨c,R,hfamily,r,L,hr,hL,hbound,hentry⟩ :=
    exists_common_sourcePsi_fullJacobian_rootLipschitz hp hp1 a.val φ hφ
  refine ⟨r,L,hr,hL,?_⟩
  intro b d hb hd
  let l := Filter.comap Int.natAbs Filter.atTop
  let : NeBot l :=
    (inferInstance : NeBot (Filter.atTop : Filter ℕ)).comap_of_surj Int.natAbs_surjective
  let T (n : ℤ) := sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n b.val) φ -
    sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n d.val) φ
  apply Coeff.opNorm_le_of_basis_limit hp l T
    (sourcePsiGapLimitOperator hp hp1 φ hφ b - sourcePsiGapLimitOperator hp hp1 φ hφ d)
    (L*‖b.val-d.val‖) (mul_nonneg hL (norm_nonneg _))
    (hbound.mono fun n hn => hn b.val hb d.val hd)
  intro m k
  have h := (hentry b.val hb b.property m k).sub (hentry d.val hd d.property m k)
  simpa only [T,sub_apply,lp.coeFn_sub,Pi.sub_apply,
    sourcePsiGapLimitOperator_entry hp hp1 φ hφ b c R hfamily m k,
    sourcePsiGapLimitOperator_entry hp hp1 φ hφ d c R hfamily m k] using h

/-- Operator-norm continuity of the intrinsic limit on the entire
compact gap product, without an assumed limit-family continuity. -/
theorem continuous_sourcePsiGapLimitOperator
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    Continuous (sourcePsiGapLimitOperator hp hp1 φ hφ) := by
  rw [continuous_iff_continuousAt]
  intro a
  obtain ⟨r,L,hr,hL,hLip⟩ := exists_local_lipschitz_sourcePsiGapLimitOperator hp hp1 φ hφ a
  let K : ℝ≥0 := ⟨L,hL⟩
  have hlocal : LipschitzOnWith K (sourcePsiGapLimitOperator hp hp1 φ hφ) (ball a r) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro b hb d hd
    have hb' : b.val ∈ ball a.val r := by simpa only [mem_ball,Subtype.dist_eq] using hb
    have hd' : d.val ∈ ball a.val r := by simpa only [mem_ball,Subtype.dist_eq] using hd
    rw [dist_eq_norm]
    change ‖sourcePsiGapLimitOperator hp hp1 φ hφ b -
      sourcePsiGapLimitOperator hp hp1 φ hφ d‖ ≤ L*dist b d
    simpa only [Subtype.dist_eq,dist_eq_norm] using hLip b d hb' hd'
  exact (hlocal.continuousOn a (mem_ball_self hr)).continuousAt
    (isOpen_ball.mem_nhds (mem_ball_self hr))

/-- The bounded linear isomorphism supplied by the actual limit
operator's bijectivity. -/
def sourcePsiGapLimitEquiv
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : sourcePeriodicGapRootSet hp hp1 φ) : Coeff p ≃L[ℂ] Coeff p :=
  ContinuousLinearEquiv.ofBijective (sourcePsiGapLimitOperator hp hp1 φ hφ a)
    (LinearMap.ker_eq_bot.mpr (sourcePsiGapLimitOperator_bijective hp hp1 φ hφ a).1)
    (LinearMap.range_eq_top.mpr (sourcePsiGapLimitOperator_bijective hp hp1 φ hφ a).2)

/-- The genuine bounded inverse, on the full coefficient space. -/
def sourcePsiGapLimitInverse
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : sourcePeriodicGapRootSet hp hp1 φ) : Coeff p →L[ℂ] Coeff p :=
  (sourcePsiGapLimitEquiv hp hp1 φ hφ a).symm.toContinuousLinearMap

theorem sourcePsiGapLimitOperator_comp_inverse
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : sourcePeriodicGapRootSet hp hp1 φ) :
    (sourcePsiGapLimitOperator hp hp1 φ hφ a).comp (sourcePsiGapLimitInverse hp hp1 φ hφ a) =
      ContinuousLinearMap.id ℂ (Coeff p) := by
  apply ContinuousLinearMap.ext
  intro x
  exact (sourcePsiGapLimitEquiv hp hp1 φ hφ a).apply_symm_apply x

theorem sourcePsiGapLimitInverse_comp_operator
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : sourcePeriodicGapRootSet hp hp1 φ) :
    (sourcePsiGapLimitInverse hp hp1 φ hφ a).comp (sourcePsiGapLimitOperator hp hp1 φ hφ a) =
      ContinuousLinearMap.id ℂ (Coeff p) := by
  apply ContinuousLinearMap.ext
  intro x
  exact (sourcePsiGapLimitEquiv hp hp1 φ hφ a).symm_apply_apply x

/-- At every fixed real-type potential, one constant bounds the
actual `Q*` inverses over all full gap-contained root vectors. -/
theorem exists_uniform_sourcePsiGapLimitInverse_norm
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : sourcePeriodicGapRootSet hp hp1 φ,
      ‖sourcePsiGapLimitInverse hp hp1 φ hφ a‖ ≤ M := by
  exact NLS.exists_uniform_inverse_norm_on_compact
    (sourcePeriodicGapRootSet hp hp1 φ) (isCompact_sourcePeriodicGapRootSet hp hp1 φ)
    (sourcePsiGapLimitOperator hp hp1 φ hφ) (sourcePsiGapLimitInverse hp hp1 φ hφ)
    (continuous_sourcePsiGapLimitOperator hp hp1 φ hφ)
    (sourcePsiGapLimitOperator_comp_inverse hp hp1 φ hφ)
    (sourcePsiGapLimitInverse_comp_operator hp hp1 φ hφ)

end NLS.ZakharovShabat
