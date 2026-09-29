import NLS.ZakharovShabat.SourcePsiCommonJacobianCharts
import NLS.ZakharovShabat.SourcePsiAnalyticImplicitStep
import NLS.ZakharovShabat.SourcePsiGapLimitOperator
import NLS.ComplexAnalysis.BanachHolomorphicC1

/-!
# Joint root and source variation of the actual psi Jacobians

A bounded holomorphic chart controls its joint derivative. Restriction
to the root variable and the full block extension are contractions on
operator differences, giving the same Lipschitz bound for the actual
full Jacobian when both roots and complex potentials vary.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An actual analytic equation chart with its coordinate formula,
moving contour geometry, equation norm bound, and joint Lipschitz
bound for the full root Jacobian. -/
def sourcePsiJointJacobianControl
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (φ : CoeffPair p) (r L : ℝ) : Prop :=
  DifferentiableOn ℂ (fun t : DeletedCoeff p n × CoeffPair p =>
    sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) (ball (a,φ) r) ∧
  (∀ t ∈ ball (a,φ) r, ∀ m : ℤ,
    (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m (t.1 : Coeff p) t.2 (c m) (R m)) ∧
  (∀ t ∈ ball (a,φ) r, ∀ u ∈ ball (a,φ) r,
    ‖sourcePsiFullRootJacobian hp hp1 n c R t.1 t.2 -
        sourcePsiFullRootJacobian hp hp1 n c R u.1 u.2‖ ≤ L*‖t-u‖) ∧
  (∀ t ∈ ball (a,φ) r, sourcePsiRealCenteredContourFamily hp hp1 t.2 c R) ∧
  ∀ t ∈ ball (a,φ) r, ‖sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2‖ ≤ L

theorem sourcePsiJointJacobianControl.mono
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (φ : CoeffPair p) (r r' L L' : ℝ)
    (h : sourcePsiJointJacobianControl hp hp1 n c R a φ r L)
    (hr : r' ≤ r) (hL : L ≤ L') :
    sourcePsiJointJacobianControl hp hp1 n c R a φ r' L' := by
  have hball : ball (a,φ) r' ⊆ ball (a,φ) r := ball_subset_ball hr
  refine ⟨h.1.mono hball,(fun t ht m => h.2.1 t (hball ht) m),?_,
    (fun t ht => h.2.2.2.1 t (hball ht)),
    (fun t ht => (h.2.2.2.2 t (hball ht)).trans hL)⟩
  intro t ht u hu
  exact (h.2.2.1 t (hball ht) u (hball hu)).trans
    (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

theorem norm_sourcePsiFullRootJacobian_sub_le_of_joint_ball_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n × CoeffPair p) (r C : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) (ball a (4*r)))
    (hb : ∀ t ∈ ball a (4*r),
      ‖sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2‖ ≤ C)
    {t u : DeletedCoeff p n × CoeffPair p}
    (ht : t ∈ ball a r) (hu : u ∈ ball a r) :
    ‖sourcePsiFullRootJacobian hp hp1 n c R t.1 t.2 -
        sourcePsiFullRootJacobian hp hp1 n c R u.1 u.2‖ ≤
      (4*C/r^2)*‖t-u‖ := by
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2
  have hsub : ball a r ⊆ ball a (4*r) := ball_subset_ball (by linarith)
  have hd (v : DeletedCoeff p n × CoeffPair p) (hv : v ∈ ball a r) :
      DifferentiableAt ℂ F v :=
    (hf v (hsub hv)).differentiableAt (isOpen_ball.mem_nhds (hsub hv))
  have hpart (v : DeletedCoeff p n × CoeffPair p) (hv : v ∈ ball a r) :=
    sourcePsiSelectedEquation_partial_fderiv_eq_rootJacobian hp hp1 n c R v.1 v.2 (hd v hv)
  let Qt := sourcePsiSelectedRootJacobian hp hp1 n c R t.1 t.2
  let Qu := sourcePsiSelectedRootJacobian hp hp1 n c R u.1 u.2
  have hfull : sourcePsiFullRootJacobian hp hp1 n c R t.1 t.2 -
      sourcePsiFullRootJacobian hp hp1 n c R u.1 u.2 =
        Coeff.deletedOperatorExtension n 0 (Qt-Qu) := by
    apply ContinuousLinearMap.ext
    intro x
    ext j
    simp only [sub_apply,sourcePsiFullRootJacobian,Coeff.deletedJacobianExtension,
      Coeff.deletedOperatorExtension_apply,Qt,Qu,Submodule.coe_sub,
      lp.coeFn_add,lp.coeFn_sub,Pi.add_apply,Pi.sub_apply,zero_mul,lp.single_zero]
    simp
  have hQ : ‖Qt-Qu‖ ≤ ‖fderiv ℂ F t-fderiv ℂ F u‖ := by
    change ‖sourcePsiSelectedRootJacobian hp hp1 n c R t.1 t.2 -
      sourcePsiSelectedRootJacobian hp hp1 n c R u.1 u.2‖ ≤ _
    rw [← hpart t ht,← hpart u hu,← ContinuousLinearMap.sub_comp]
    have hmul : ‖fderiv ℂ F t-fderiv ℂ F u‖ *
        ‖ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)‖ ≤
          ‖fderiv ℂ F t-fderiv ℂ F u‖ := by
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_inl_le_one ℂ (DeletedCoeff p n) (CoeffPair p))
        (norm_nonneg (fderiv ℂ F t-fderiv ℂ F u)))
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans hmul
  rw [hfull]
  calc
    ‖Coeff.deletedOperatorExtension n 0 (Qt-Qu)‖ ≤ ‖Qt-Qu‖ := by
      simpa only [norm_zero,add_zero] using Coeff.norm_deletedOperatorExtension_le n 0 (Qt-Qu)
    _ ≤ ‖fderiv ℂ F t-fderiv ℂ F u‖ := hQ
    _ ≤ (4*C/r^2)*‖t-u‖ :=
      NLS.ComplexAnalysis.norm_fderiv_sub_le_of_holomorphic_ball_bound F a r C hr hf hb hu ht

/-- One contour family and one joint radius control the full
Jacobians at all sufficiently distant indices, including complex
source perturbations and arbitrary nearby deleted root inputs. -/
theorem exists_common_sourcePsi_fullJacobian_jointLipschitz
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      sourcePsiRealCenteredContourFamily hp hp1 φ c R ∧
      ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        DifferentiableOn ℂ (fun t : DeletedCoeff p n × CoeffPair p =>
          sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
          (ball (Coeff.deleteCoordinateTo n a,φ) r) ∧
        (∀ t ∈ ball (Coeff.deleteCoordinateTo n a,φ) r, ∀ m : ℤ,
          (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
            sourcePsiEquationCoordinate hp hp1 n m (t.1 : Coeff p) t.2 (c m) (R m)) ∧
        (∀ t ∈ ball (Coeff.deleteCoordinateTo n a,φ) r,
          ∀ u ∈ ball (Coeff.deleteCoordinateTo n a,φ) r,
            ‖sourcePsiFullRootJacobian hp hp1 n c R t.1 t.2 -
                sourcePsiFullRootJacobian hp hp1 n c R u.1 u.2‖ ≤ L*‖t-u‖) ∧
        (∀ t ∈ ball (Coeff.deleteCoordinateTo n a,φ) r,
          sourcePsiRealCenteredContourFamily hp hp1 t.2 c R) ∧
        ∀ t ∈ ball (Coeff.deleteCoordinateTo n a,φ) r,
          ‖sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2‖ ≤ L := by
  obtain ⟨c,R,hcenter,hgeom,K,hfree,δ,hδ,C,hC,hcharts⟩ :=
    exists_common_sourcePsi_selectedJacobianCharts_at_natAbs_realCentered_with_geometry hp hp1 a φ hφ
  let r := δ/4
  let L := max C (4*C/r^2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hL : 0 ≤ L := le_max_of_le_left hC
  have hfour : 4*r = δ := by dsimp [r]; ring
  have hsmall : r ≤ δ := by dsimp [r]; linarith
  refine ⟨c,R,⟨hcenter,hgeom⟩,r,L,hr,hL,?_⟩
  filter_upwards [hcharts] with n hn
  obtain ⟨U,hUopen,hbase,hlocal,hbound,hcoord,hdiff,hgeometry⟩ := hn
  have hball : ball (Coeff.deleteCoordinateTo n a,φ) r ⊆ U :=
    (ball_subset_ball hsmall).trans hlocal
  refine ⟨hdiff.mono hball,(fun t ht m => hcoord t (hball ht) m),?_,
    (fun t ht => ⟨hcenter,fun m => hgeometry t (hball ht) m⟩),
    (fun t ht => (hbound t (hball ht)).trans (le_max_left _ _))⟩
  intro t ht u hu
  apply (norm_sourcePsiFullRootJacobian_sub_le_of_joint_ball_bound hp hp1 n c R
    (Coeff.deleteCoordinateTo n a,φ) r C hr ?_ ?_ ht hu).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · rw [hfour]
    exact hdiff.mono hlocal
  · rw [hfour]
    exact fun t ht => hbound t (hlocal ht)

end NLS.ZakharovShabat
