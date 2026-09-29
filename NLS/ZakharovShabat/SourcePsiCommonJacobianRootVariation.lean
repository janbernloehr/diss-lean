import NLS.ZakharovShabat.SourcePsiGapLimitOperator
import NLS.ComplexAnalysis.BanachHolomorphicC1

/-!
# Uniform root variation on common psi Jacobian charts

One bounded holomorphic chart family for escaping deleted indices
gives a common Lipschitz constant for the full Jacobians as the root
vector varies. Nearby gap-root vectors also have the actual scalar
entry limits on this same family of contours.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem tendsto_sourcePsiFullRootJacobian_entry_of_eventualCharts
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (hcharts : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ∃ U : Set (DeletedCoeff p n × CoeffPair p),
        IsOpen U ∧ (Coeff.deleteCoordinateTo n a,φ) ∈ U ∧
        (∀ t ∈ U, ∀ m : ℤ,
          (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
            sourcePsiEquationCoordinate hp hp1 n m
              (t.1 : Coeff p) t.2 (c m) (R m)) ∧
        DifferentiableOn ℂ (fun t : DeletedCoeff p n × CoeffPair p =>
          sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (m k : ℤ) :
    Tendsto (fun n : ℤ => (sourcePsiFullRootJacobian hp hp1 n c R
      (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m)
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m))) := by
  have hk : ∀ z ∈ sphere (c m) (R m), displacedRoots a k-z ≠ 0 := by
    intro z hz heq
    exact (hfamily.2 m).2.2.2 hz k ((sub_eq_zero.mp heq).symm ▸ ha k)
  have hscalar := tendsto_sourcePsiDeletedScalarMatrixEntry_at_natAbs
    hp hp1 m k a φ hφ (c m) (R m) (hfamily.2 m).1.le
      (hfamily.2 m).2.2.1 (hfamily.2 m).2.2.2 hk
  have hne : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      m ≠ n ∧ k ≠ n := by
    apply eventually_comap.mpr
    apply eventually_atTop.mpr
    refine ⟨max m.natAbs k.natAbs+1,?_⟩
    intro j hj n hn
    constructor <;> intro heq <;> subst n <;> omega
  apply hscalar.congr'
  filter_upwards [hcharts,hne] with n hn hnk
  obtain ⟨U,hUopen,hbase,hcoord,hdiff⟩ := hn
  exact (sourcePsiFullRootJacobian_retained_entry_eq_scalarMatrixEntry
    hp hp1 n m k a φ c R U hUopen hcoord hdiff hbase hnk.1 hnk.2).symm

/-- A neighborhood of any fixed full root vector has one eventual
Lipschitz bound for every escaping full Jacobian, and every nearby
gap-root vector has the actual entry limit on those same contours. -/
theorem exists_common_sourcePsi_fullJacobian_rootLipschitz
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      sourcePsiRealCenteredContourFamily hp hp1 φ c R ∧
      ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∀ b ∈ ball a r, ∀ d ∈ ball a r,
          ‖sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n b) φ -
              sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n d) φ‖ ≤
            L*‖b-d‖) ∧
      (∀ b ∈ ball a r, b ∈ sourcePeriodicGapRootSet hp hp1 φ →
        ∀ m k : ℤ,
          Tendsto (fun n : ℤ => (sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n b) φ (lp.single p k 1)) m)
            (Filter.comap Int.natAbs Filter.atTop)
            (𝓝 (sourcePsiLimitMatrixEntry hp hp1 m k b φ (c m) (R m)))) := by
  obtain ⟨c,R,hcenter,hgeom,K,hfree,δ,hδ,C,hC,hcharts⟩ :=
    exists_common_sourcePsi_selectedJacobianCharts_at_natAbs_realCentered hp hp1 a φ hφ
  let r := δ/4
  let L := 4*C/r^2
  have hr : 0 < r := by dsimp [r]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hfour : 4*r = δ := by dsimp [r]; ring
  have hsmall : r ≤ δ := by dsimp [r]; linarith
  have hproj (n : ℤ) (x y : Coeff p) :
      ‖Coeff.deleteCoordinateTo n x-Coeff.deleteCoordinateTo n y‖ ≤ ‖x-y‖ := by
    rw [← map_sub]
    simpa only [one_mul] using (Coeff.deleteCoordinateTo (p := p) n).le_of_opNorm_le
      (Coeff.norm_deleteCoordinateTo_le_one n) (x-y)
  have hprojectedBall (n : ℤ) (b : Coeff p) (hb : b ∈ ball a r) :
      Coeff.deleteCoordinateTo n b ∈ ball (Coeff.deleteCoordinateTo n a) r := by
    rw [mem_ball,dist_eq_norm] at hb ⊢
    exact (hproj n b a).trans_lt hb
  refine ⟨c,R,⟨hcenter,hgeom⟩,r,L,hr,hL,?_,?_⟩
  · filter_upwards [hcharts] with n hn
    obtain ⟨U,hUopen,hbase,hlocal,hbound,hcoord,hdiff⟩ := hn
    let a₀ := Coeff.deleteCoordinateTo n a
    let f : DeletedCoeff p n → DeletedCoeff p n :=
      fun b => sourcePsiSelectedEquationSequence hp hp1 n c R b φ
    have hballPair (b : DeletedCoeff p n) (hb : b ∈ ball a₀ δ) : (b,φ) ∈ U := by
      apply hlocal
      simpa only [dist_prod_same_right,mem_ball] using hb
    have hf : DifferentiableOn ℂ f (ball a₀ δ) := by
      intro b hb
      have hbU := hballPair b hb
      have hpairDiff : DifferentiableAt ℂ
          (fun b : DeletedCoeff p n => (b,φ)) b :=
        (differentiableAt_id : DifferentiableAt ℂ
          (fun b : DeletedCoeff p n => b) b).prodMk (differentiableAt_const φ)
      exact (((hdiff (b,φ) hbU).differentiableAt (hUopen.mem_nhds hbU)).comp b
        hpairDiff).differentiableWithinAt
    have hb : ∀ b ∈ ball a₀ δ, ‖f b‖ ≤ C :=
      fun b hb => hbound (b,φ) (hballPair b hb)
    intro b hb' d hd'
    have hQ := NLS.ComplexAnalysis.norm_fderiv_sub_le_of_holomorphic_ball_bound
      f a₀ r C hr (by rw [hfour]; exact hf) (by rw [hfour]; exact hb)
      (hprojectedBall n d hd') (hprojectedBall n b hb')
    let Qb := sourcePsiSelectedRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n b) φ
    let Qd := sourcePsiSelectedRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n d) φ
    have hfull : sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n b) φ -
        sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n d) φ =
          Coeff.deletedOperatorExtension n 0 (Qb-Qd) := by
      apply ContinuousLinearMap.ext
      intro x
      ext j
      simp only [sub_apply,sourcePsiFullRootJacobian,Coeff.deletedJacobianExtension,
        Coeff.deletedOperatorExtension_apply,Qb,Qd,Submodule.coe_sub,
        lp.coeFn_add,lp.coeFn_sub,Pi.add_apply,Pi.sub_apply,zero_mul,lp.single_zero]
      simp
    rw [hfull]
    calc
      ‖Coeff.deletedOperatorExtension n 0 (Qb-Qd)‖ ≤ ‖Qb-Qd‖ := by
        simpa only [norm_zero,add_zero] using Coeff.norm_deletedOperatorExtension_le n 0 (Qb-Qd)
      _ ≤ L*‖Coeff.deleteCoordinateTo n b-Coeff.deleteCoordinateTo n d‖ := hQ
      _ ≤ L*‖b-d‖ := mul_le_mul_of_nonneg_left (hproj n b d) hL
  · intro b hb hbgap m k
    apply tendsto_sourcePsiFullRootJacobian_entry_of_eventualCharts
      hp hp1 b φ hφ hbgap c R ⟨hcenter,hgeom⟩
    filter_upwards [hcharts] with n hn
    obtain ⟨U,hUopen,hbase,hlocal,hbound,hcoord,hdiff⟩ := hn
    refine ⟨U,hUopen,?_,hcoord,hdiff⟩
    apply hlocal
    have hb' := (ball_subset_ball hsmall) (hprojectedBall n b hb)
    simpa only [dist_prod_same_right,mem_ball] using hb'

end NLS.ZakharovShabat
