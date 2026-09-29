import NLS.ZakharovShabat.SourcePsiJacobianContourIndependence
import NLS.ZakharovShabat.SourceRealTypeDecomposition
import NLS.ComplexAnalysis.RealFormIdentity
import NLS.ComplexAnalysis.ConvexHolomorphicIdentity

/-!
# Compatibility of complex psi equation charts

The joint real form restricts only the source variable; root inputs
remain arbitrary complex deleted sequences. Real contour independence
therefore identifies the Banach-valued equations on this form. The
identity principle gives one joint complex germ, and convexity extends
the agreement to the whole overlap. Their actual root Jacobians agree
there as well.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourcePsiSelectedEquationSequence_eventuallyEq_of_realCentered_charts
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : DeletedCoeff p n) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c₀ c₁ : ℤ → ℂ) (R₀ R₁ : ℤ → ℝ)
    (U₀ U₁ : Set (DeletedCoeff p n × CoeffPair p))
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (ha₀ : (a,φ) ∈ U₀) (ha₁ : (a,φ) ∈ U₁)
    (hfamily₀ : ∀ t ∈ U₀, sourcePsiRealCenteredContourFamily hp hp1 t.2 c₀ R₀)
    (hfamily₁ : ∀ t ∈ U₁, sourcePsiRealCenteredContourFamily hp hp1 t.2 c₁ R₁)
    (hf₀ : DifferentiableOn ℂ (fun t : DeletedCoeff p n × CoeffPair p =>
      sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ t.1 t.2) U₀)
    (hf₁ : DifferentiableOn ℂ (fun t : DeletedCoeff p n × CoeffPair p =>
      sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ t.1 t.2) U₁) :
    (fun t : DeletedCoeff p n × CoeffPair p => sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ t.1 t.2)
      =ᶠ[𝓝 (a,φ)] (fun t => sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ t.1 t.2) := by
  let RealForm : Set (DeletedCoeff p n × CoeffPair p) :=
    {t | IsRealType (CoeffPair.toMax p t.2)}
  let A : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n × CoeffPair p :=
    fun t => (t.1,sourceRealPart t.2)
  let B : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n × CoeffPair p :=
    fun t => (0,sourceImagPart t.2)
  let H : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n := fun t =>
    sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ t.1 t.2 -
      sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ t.1 t.2
  have hdiff : DifferentiableOn ℂ H (U₀ ∩ U₁) :=
    (hf₀.mono inter_subset_left).sub (hf₁.mono inter_subset_right)
  have hzero : ∀ t ∈ U₀ ∩ U₁, t ∈ RealForm → H t = 0 := by
    intro t ht hreal
    exact sub_eq_zero.mpr (sourcePsiSelectedEquationSequence_eq_of_realCentered_families
      hp hp1 t.2 hreal c₀ c₁ R₀ R₁ (hfamily₀ t ht.1) (hfamily₁ t ht.2) n t.1)
  have hlocal := NLS.ComplexAnalysis.DifferentiableOn.eventually_eq_zero_of_real_form
    RealForm (a,φ) hφ
    (by
      intro x y hx hy
      change IsRealType (CoeffPair.toMax p (x.2+y.2))
      rw [map_add]
      exact hx.add hy)
    (by
      intro t x hx
      change IsRealType (CoeffPair.toMax p ((t:ℂ) • x.2))
      rw [map_smul]
      exact hx.ofReal_smul t)
    A B (fun t => sourceRealPart_realType t.2) (fun t => sourceImagPart_realType t.2)
    (by
      intro t
      apply Prod.ext
      · simp [A,B]
      · exact (sourceRealPart_add_I_smul_sourceImagPart t.2).symm)
    (by
      intro t
      change max ‖t.1‖ ‖sourceRealPart t.2‖ ≤ max ‖t.1‖ ‖t.2‖
      exact max_le_max le_rfl (norm_sourceRealPart_le hp t.2))
    (by
      intro t
      change max ‖(0 : DeletedCoeff p n)‖ ‖sourceImagPart t.2‖ ≤ max ‖t.1‖ ‖t.2‖
      rw [norm_zero,max_eq_right (norm_nonneg _)]
      exact (norm_sourceImagPart_le hp t.2).trans (le_max_right _ _))
    (U₀ ∩ U₁) (hU₀.inter hU₁) ⟨ha₀,ha₁⟩ H hdiff hzero
  filter_upwards [hlocal] with t ht
  exact sub_eq_zero.mp ht

/-- Holomorphic real-centered psi charts agree throughout any convex
overlap containing one point with a real-type source. -/
theorem sourcePsiSelectedEquationSequence_eqOn_convex_charts
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : DeletedCoeff p n) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c₀ c₁ : ℤ → ℂ) (R₀ R₁ : ℤ → ℝ)
    (U₀ U₁ : Set (DeletedCoeff p n × CoeffPair p))
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (hconv₀ : Convex ℝ U₀) (hconv₁ : Convex ℝ U₁)
    (ha₀ : (a,φ) ∈ U₀) (ha₁ : (a,φ) ∈ U₁)
    (hfamily₀ : ∀ t ∈ U₀, sourcePsiRealCenteredContourFamily hp hp1 t.2 c₀ R₀)
    (hfamily₁ : ∀ t ∈ U₁, sourcePsiRealCenteredContourFamily hp hp1 t.2 c₁ R₁)
    (hf₀ : DifferentiableOn ℂ (fun t : DeletedCoeff p n × CoeffPair p =>
      sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ t.1 t.2) U₀)
    (hf₁ : DifferentiableOn ℂ (fun t : DeletedCoeff p n × CoeffPair p =>
      sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ t.1 t.2) U₁) :
    EqOn (fun t : DeletedCoeff p n × CoeffPair p => sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ t.1 t.2)
      (fun t => sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ t.1 t.2) (U₀ ∩ U₁) := by
  apply NLS.ComplexAnalysis.DifferentiableOn.eqOn_of_convex_of_eventuallyEq
    _ _ (U₀ ∩ U₁) (hU₀.inter hU₁) (hconv₀.inter hconv₁)
    (hf₀.mono inter_subset_left) (hf₁.mono inter_subset_right) (a,φ) ⟨ha₀,ha₁⟩
  exact sourcePsiSelectedEquationSequence_eventuallyEq_of_realCentered_charts hp hp1 n a φ hφ
    c₀ c₁ R₀ R₁ U₀ U₁ hU₀ hU₁ ha₀ ha₁ hfamily₀ hfamily₁ hf₀ hf₁

/-- Equality of selected equations on an open chart identifies their
actual root derivatives, with no derivative regularity assumption. -/
theorem sourcePsiSelectedRootJacobian_eq_of_eqOn_open
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c₀ c₁ : ℤ → ℂ) (R₀ R₁ : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p)) (hU : IsOpen U)
    (heq : EqOn (fun t : DeletedCoeff p n × CoeffPair p => sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ t.1 t.2)
      (fun t => sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ t.1 t.2) U)
    (t : DeletedCoeff p n × CoeffPair p) (ht : t ∈ U) :
    sourcePsiSelectedRootJacobian hp hp1 n c₀ R₀ t.1 t.2 =
      sourcePsiSelectedRootJacobian hp hp1 n c₁ R₁ t.1 t.2 := by
  have hpair : Continuous (fun b : DeletedCoeff p n => (b,t.2)) :=
    continuous_id.prodMk continuous_const
  have hnear : ∀ᶠ b in 𝓝 t.1, (b,t.2) ∈ U :=
    (hpair.tendsto t.1).eventually (hU.mem_nhds ht)
  have hfg : (fun b : DeletedCoeff p n => sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ b t.2)
      =ᶠ[𝓝 t.1] (fun b => sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ b t.2) := by
    filter_upwards [hnear] with b hb
    exact heq (x := (b,t.2)) hb
  unfold sourcePsiSelectedRootJacobian
  exact hfg.fderiv_eq (𝕜 := ℂ)

/-- Joint ball charts centered at the same real source agree on
their entire overlap. Replacing the source component by its common
real center gives a real-form point in every nonempty overlap. -/
theorem sourcePsiSelectedEquationSequence_eqOn_ball_charts
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a₀ a₁ : DeletedCoeff p n) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (r₀ r₁ : ℝ)
    (c₀ c₁ : ℤ → ℂ) (R₀ R₁ : ℤ → ℝ)
    (hfamily₀ : ∀ t ∈ ball (a₀,φ) r₀, sourcePsiRealCenteredContourFamily hp hp1 t.2 c₀ R₀)
    (hfamily₁ : ∀ t ∈ ball (a₁,φ) r₁, sourcePsiRealCenteredContourFamily hp hp1 t.2 c₁ R₁)
    (hf₀ : DifferentiableOn ℂ (fun t : DeletedCoeff p n × CoeffPair p =>
      sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ t.1 t.2) (ball (a₀,φ) r₀))
    (hf₁ : DifferentiableOn ℂ (fun t : DeletedCoeff p n × CoeffPair p =>
      sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ t.1 t.2) (ball (a₁,φ) r₁)) :
    EqOn (fun t : DeletedCoeff p n × CoeffPair p => sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ t.1 t.2)
      (fun t => sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ t.1 t.2)
        (ball (a₀,φ) r₀ ∩ ball (a₁,φ) r₁) := by
  intro t ht
  have hbase₀ : (t.1,φ) ∈ ball (a₀,φ) r₀ := by
    rw [mem_ball,dist_prod_same_right]
    have h : max (dist t.1 a₀) (dist t.2 φ) < r₀ := by
      simpa only [mem_ball,Prod.dist_eq] using ht.1
    exact (le_max_left _ _).trans_lt h
  have hbase₁ : (t.1,φ) ∈ ball (a₁,φ) r₁ := by
    rw [mem_ball,dist_prod_same_right]
    have h : max (dist t.1 a₁) (dist t.2 φ) < r₁ := by
      simpa only [mem_ball,Prod.dist_eq] using ht.2
    exact (le_max_left _ _).trans_lt h
  exact sourcePsiSelectedEquationSequence_eqOn_convex_charts hp hp1 n t.1 φ hφ
    c₀ c₁ R₀ R₁ (ball (a₀,φ) r₀) (ball (a₁,φ) r₁) isOpen_ball isOpen_ball
    (convex_ball _ _) (convex_ball _ _) hbase₀ hbase₁ hfamily₀ hfamily₁ hf₀ hf₁ ht

end NLS.ZakharovShabat
