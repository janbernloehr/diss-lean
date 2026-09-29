import NLS.ZakharovShabat.SourcePsiComplexJacobianInverseBound
import NLS.ZakharovShabat.SourcePsiGapProductConvex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# A common complex neighborhood of the full psi gap product

The union of the jointly controlled chart balls contains the whole
real gap product at a fixed potential. Every point has an actual
holomorphic contour chart and bounded two-sided full and deleted
Jacobian inverses for every index. Compactness supplies one positive
tube radius, independent of both the root center and the index.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal Pointwise
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An actual holomorphic selected equation near the given complex data,
with two-sided full and deleted Jacobian inverses sharing a bound.
Its real-centered contour family remains valid throughout the chart
and at the real-type base potential. -/
def sourcePsiComplexJacobianChartInverseBound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : Coeff p) (ψ : CoeffPair p) (M : ℝ) : Prop :=
  sourcePsiRealCenteredContourFamily hp hp1 φ c R ∧
  (∃ V : Set (DeletedCoeff p n × CoeffPair p), IsOpen V ∧
    (Coeff.deleteCoordinateTo n a,ψ) ∈ V ∧
    DifferentiableOn ℂ (fun t : DeletedCoeff p n × CoeffPair p =>
      sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) V ∧
    (∀ t ∈ V, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m (t.1 : Coeff p) t.2 (c m) (R m)) ∧
    ∀ t ∈ V, sourcePsiRealCenteredContourFamily hp hp1 t.2 c R) ∧
  (∃ S : Coeff p →L[ℂ] Coeff p,
    (sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a) ψ).comp S =
      ContinuousLinearMap.id ℂ (Coeff p) ∧
    S.comp (sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a) ψ) =
      ContinuousLinearMap.id ℂ (Coeff p) ∧ ‖S‖ ≤ M) ∧
  (∃ S : DeletedCoeff p n →L[ℂ] DeletedCoeff p n,
    (sourcePsiSelectedRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a) ψ).comp S =
      ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
    S.comp (sourcePsiSelectedRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a) ψ) =
      ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧ ‖S‖ ≤ M)

/-- There is one open neighborhood of the whole full gap product at
the real source where every index has an actual holomorphic chart and
both full and deleted inverses with one common norm bound. -/
theorem exists_sourcePsi_complexJacobian_neighborhood
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      sourcePeriodicGapRootSet hp hp1 φ ×ˢ {φ} ⊆ U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ U, ∀ n : ℤ,
        ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
          sourcePsiComplexJacobianChartInverseBound hp hp1 φ n c R t.1 t.2 M := by
  classical
  obtain ⟨M,hM,hlocal⟩ := exists_uniform_local_sourcePsi_complexJacobian_inverses hp hp1 φ hφ
  choose c R hfamily δ L hδ hL hcharts using hlocal
  let U : Set (Coeff p × CoeffPair p) :=
    ⋃ a : sourcePeriodicGapRootSet hp hp1 φ, ball (a.val,φ) (δ a)
  have hUopen : IsOpen U := isOpen_iUnion (fun a => isOpen_ball)
  have hbase : sourcePeriodicGapRootSet hp hp1 φ ×ˢ {φ} ⊆ U := by
    rintro ⟨a,ψ⟩ ⟨ha,hψ⟩
    have hψφ : ψ = φ := mem_singleton_iff.mp hψ
    subst ψ
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,mem_ball_self (hδ ⟨a,ha⟩)⟩
  refine ⟨U,hUopen,hbase,M,hM,?_⟩
  intro t ht n
  obtain ⟨a,ha⟩ := mem_iUnion.mp ht
  let q : DeletedCoeff p n × CoeffPair p := (Coeff.deleteCoordinateTo n t.1,t.2)
  have hproj : ‖Coeff.deleteCoordinateTo n t.1-Coeff.deleteCoordinateTo n a.val‖ ≤ ‖t.1-a.val‖ := by
    rw [← map_sub]
    simpa only [one_mul] using (Coeff.deleteCoordinateTo (p := p) n).le_of_opNorm_le
      (Coeff.norm_deleteCoordinateTo_le_one n) (t.1-a.val)
  have hq : q ∈ ball (Coeff.deleteCoordinateTo n a.val,φ) (δ a) := by
    rw [mem_ball,Prod.dist_eq]
    rw [mem_ball,Prod.dist_eq] at ha
    apply (max_le_max ?_ le_rfl).trans_lt ha
    simpa only [dist_eq_norm] using hproj
  have hcontrol := (hcharts a n).1
  obtain ⟨S,hQS,hSQ,hS⟩ := (hcharts a n).2 q hq
  obtain ⟨Sd,hQSd,hSdQ,hSd⟩ := Coeff.exists_deleted_inverse_of_extension_inverse n
    (sourcePsiSelectedRootJacobian hp hp1 n (c a n) (R a n) q.1 q.2) S hQS hSQ
  exact ⟨c a n,R a n,hfamily a n,
    ⟨ball (Coeff.deleteCoordinateTo n a.val,φ) (δ a),isOpen_ball,hq,
      hcontrol.1,hcontrol.2.1,hcontrol.2.2.2.1⟩,
    ⟨S,hQS,hSQ,hS⟩,Sd,hQSd,hSdQ,hSd.trans hS⟩

/-- One positive radius works at every gap-root center and every
deleted index, for arbitrary nearby complex roots and potentials. -/
theorem exists_uniform_sourcePsi_complexJacobian_tube
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 ≤ M ∧
      ∀ a : sourcePeriodicGapRootSet hp hp1 φ,
        ∀ t ∈ ball (a.val,φ) ε, ∀ n : ℤ,
          ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
            sourcePsiComplexJacobianChartInverseBound hp hp1 φ n c R t.1 t.2 M := by
  obtain ⟨U,hUopen,hbase,M,hM,hcharts⟩ := exists_sourcePsi_complexJacobian_neighborhood hp hp1 φ hφ
  let K : Set (Coeff p × CoeffPair p) := sourcePeriodicGapRootSet hp hp1 φ ×ˢ {φ}
  have hK : IsCompact K := (isCompact_sourcePeriodicGapRootSet hp hp1 φ).prod
    (isCompact_singleton : IsCompact {φ})
  obtain ⟨ε,hε,htube⟩ := hK.exists_cthickening_subset_open hUopen hbase
  refine ⟨ε,M,hε,hM,?_⟩
  intro a t ht n
  apply hcharts t (htube ?_) n
  exact mem_cthickening_of_dist_le t (a.val,φ) ε K
    ⟨a.property,mem_singleton φ⟩ (le_of_lt (mem_ball.mp ht))

/-- The common complex neighborhood can be chosen convex: add one
small open ball to the convex full gap product at the fixed source. -/
theorem exists_convex_sourcePsi_complexJacobian_neighborhood
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ Convex ℝ U ∧
      sourcePeriodicGapRootSet hp hp1 φ ×ˢ {φ} ⊆ U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ U, ∀ n : ℤ,
        ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
          sourcePsiComplexJacobianChartInverseBound hp hp1 φ n c R t.1 t.2 M := by
  obtain ⟨ε,M,hε,hM,hcharts⟩ := exists_uniform_sourcePsi_complexJacobian_tube hp hp1 φ hφ
  let K : Set (Coeff p × CoeffPair p) := sourcePeriodicGapRootSet hp hp1 φ ×ˢ {φ}
  let U := K+ball (0 : Coeff p × CoeffPair p) ε
  have hconvK : Convex ℝ K := (convex_sourcePeriodicGapRootSet hp hp1 φ).prod (convex_singleton φ)
  refine ⟨U,isOpen_ball.add_left,hconvK.add (convex_ball 0 ε),?_,M,hM,?_⟩
  · intro t ht
    exact mem_add.mpr ⟨t,ht,0,mem_ball_self hε,add_zero t⟩
  · intro t ht n
    obtain ⟨k,hk,z,hz,rfl⟩ := mem_add.mp ht
    have hkφ : k.2 = φ := mem_singleton_iff.mp hk.2
    have hnear : k+z ∈ ball (k.1,φ) ε := by
      have hkeq : (k.1,φ) = k := by ext <;> simp [hkφ]
      rw [hkeq,mem_ball,dist_eq_norm,add_sub_cancel_left]
      simpa only [mem_ball,dist_zero_right] using hz
    exact hcharts ⟨k.1,hk.1⟩ (k+z) hnear n

end NLS.ZakharovShabat
