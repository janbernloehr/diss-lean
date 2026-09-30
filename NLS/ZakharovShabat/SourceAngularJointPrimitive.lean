import NLS.ComplexAnalysis.ParametricCosinePrimitive
import NLS.ZakharovShabat.SourceAngularBetaBoundaryDomain
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic

/-!
# Joint primitive families for the actual angular integrands

Regular sheet charts admit jointly analytic primitives with a fixed anchor.
The regular gap numerator is jointly analytic on the moving complement of
the other gaps. Its cosine pullback admits a jointly analytic primitive
normalized at pi, with no supplied primitive or normalization constant.
The actual beta domain can be shrunk to support every such numerator while
retaining analytic boundary coordinates and the full psi extension.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The literal regular angular gap numerator is jointly analytic wherever
the actual omitted standard-root product is jointly analytic. -/
theorem angular_gapNumerator_analyticOnNhd_joint
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s) (n m : ℤ)
    (V : Set (CoeffPair p)) (hVW : V ⊆ W)
    (hP : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 m)
      (sourceStandardRootOmittedJointDomain hp hp1 V m)) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
      sourceAngularGapNumerator hp hp1 n m s t.2 t.1)
      (sourceStandardRootOmittedJointDomain hp hp1 V m) := by
  intro t ht
  exact (hs.analytic_numerator_joint n t ⟨mem_univ _,hVW ht.1⟩).div
    (analyticAt_const.mul (hP t ht))
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 t.2 t.1 m ht.2))

/-- Around every regular spectral/source point the actual sheet integrand
has an explicit jointly analytic primitive. Its anchor value is exactly
zero at every nearby source, rather than an arbitrary chosen constant. -/
theorem exists_local_angular_joint_regular_primitive
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s) (hW : IsOpen W)
    (n : ℤ) (w : ℂ) (hw : w ≠ 0) (z : ℂ) (φ : CoeffPair p)
    (hφ : φ ∈ W) (hz : (z,φ) ∈ sourceAngularRootSheetDomain hp w) :
    ∃ r : ℝ, 0 < r ∧ ball φ r ⊆ W ∧ ∃ H : ℂ × CoeffPair p → ℂ,
      AnalyticOnNhd ℂ H (ball z r ×ˢ ball φ r) ∧
        (∀ ψ ∈ ball φ r, H (z,ψ) = 0) ∧
        ∀ ψ ∈ ball φ r, ∀ u ∈ ball z r,
          (u,ψ) ∈ sourceAngularRootSheetDomain hp w ∧
            HasDerivAt (fun v => H (v,ψ))
              (sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (u,ψ)) u := by
  let D : Set (ℂ × CoeffPair p) := sourceAngularRootSheetDomain hp w ∩ (univ ×ˢ W)
  have hD : IsOpen D := (isOpen_sourceAngularRootSheetDomain hp hp1 w).inter (isOpen_univ.prod hW)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hD (z,φ) ⟨hz,mem_univ _,hφ⟩
  have hprod : ball z r ×ˢ ball φ r ⊆ D := by
    rw [ball_prod_same]
    exact hball
  have hVW : ball φ r ⊆ W := by
    intro ψ hψ
    have hpair : (z,ψ) ∈ ball z r ×ˢ ball φ r := ⟨mem_ball_self hr,hψ⟩
    have ht : (z,ψ) ∈ D := hprod hpair
    exact ht.2.2
  let f : ℂ × CoeffPair p → ℂ := sourceAngularIntegrand n s (sourceAngularRootSheet hp w)
  have hf : AnalyticOnNhd ℂ f (ball z r ×ˢ ball φ r) :=
    (hs.angular_rootSheet_integrand_analyticOnNhd n w hw).mono hprod
  let H : ℂ × CoeffPair p → ℂ := parametricConvexPrimitive f z
  refine ⟨r,hr,hVW,H,
    analyticOnNhd_parametricConvexPrimitive f _ _ z isOpen_ball (convex_ball z r)
      isOpen_ball (mem_ball_self hr) hf,
    (fun ψ _ => parametricConvexPrimitive_anchor f z ψ),?_⟩
  intro ψ hψ u hu
  have hpair : (u,ψ) ∈ ball z r ×ˢ ball φ r := ⟨hu,hψ⟩
  exact ⟨(hprod hpair).1,hasDerivAt_parametricConvexPrimitive f _ _ z isOpen_ball
    (convex_ball z r) (mem_ball_self hr) hf ψ hψ u hu⟩

/-- At a real source with a regular Dirichlet terminal, the actual sheet
integrand has a joint primitive normalized at that fixed base terminal.
Evaluation at the moving Dirichlet root is complex analytic in the source.
The periodic-endpoint normalization needed for beta is separate. -/
theorem exists_local_angular_dirichlet_joint_primitive
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s) (hW : IsOpen W)
    (n m : ℤ) (φ : CoeffPair p) (hφ : φ ∈ W)
    (hreal : IsRealType (CoeffPair.toMax p φ))
    (hw : sourceAntiDiscriminantCandidate hp hp1 φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m) ≠ 0) :
    let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
    let w := sourceAntiDiscriminantCandidate hp hp1 φ (μ φ)
    ∃ r : ℝ, 0 < r ∧ ball φ r ⊆ W ∧ ∃ H : ℂ × CoeffPair p → ℂ,
      AnalyticOnNhd ℂ H (ball (μ φ) r ×ˢ ball φ r) ∧
        AnalyticAt ℂ (fun ψ => H (μ ψ,ψ)) φ ∧
        (∀ ψ ∈ ball φ r, H (μ φ,ψ) = 0) ∧
        ∀ ψ ∈ ball φ r, ∀ u ∈ ball (μ φ) r,
          (u,ψ) ∈ sourceAngularRootSheetDomain hp w ∧
            HasDerivAt (fun v => H (v,ψ))
              (sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (u,ψ)) u := by
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let w := sourceAntiDiscriminantCandidate hp hp1 φ (μ φ)
  obtain ⟨r,hr,hsub,H,hH,hzero,hderiv⟩ := hs.exists_local_angular_joint_regular_primitive
    hW n w hw (μ φ) φ hφ (sourceAngularRootSheet_dirichlet_base hp hp1 φ m hw).1
  refine ⟨r,hr,hsub,H,hH,?_,hzero,hderiv⟩
  exact (hH (μ φ,φ) ⟨mem_ball_self hr,mem_ball_self hr⟩).comp
    (f := fun ψ : CoeffPair p => (μ ψ,ψ))
    ((analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ hreal m).prod analyticAt_id)

/-- An analytic cosine chart for the actual gap numerator has a jointly
analytic primitive normalized at the fixed angle pi. -/
theorem angular_cosine_primitive_spec
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s) (n m : ℤ)
    (V : Set (CoeffPair p)) (hV : IsOpen V) (hVW : V ⊆ W)
    (hP : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 m)
      (sourceStandardRootOmittedJointDomain hp hp1 V m))
    (τ δ : CoeffPair p → ℂ) (hτ : AnalyticOnNhd ℂ τ V) (hδ : AnalyticOnNhd ℂ δ V)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hπ : (Real.pi:ℂ) ∈ Ω)
    (hchart : ∀ ψ ∈ V, ∀ θ ∈ Ω, cosineGapPoint (τ ψ) (δ ψ) θ ∈
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    let g : ℂ × CoeffPair p → ℂ := fun t => sourceAngularGapNumerator hp hp1 n m s t.2 t.1
    AnalyticOnNhd ℂ (parametricCosinePrimitive g τ δ) (Ω ×ˢ V) ∧
      (∀ ψ : CoeffPair p, parametricCosinePrimitive g τ δ ((Real.pi:ℂ),ψ) = 0) ∧
      ∀ ψ ∈ V, ∀ θ ∈ Ω, HasDerivAt (fun e => parametricCosinePrimitive g τ δ (e,ψ))
        (sourceAngularGapNumerator hp hp1 n m s ψ (cosineGapPoint (τ ψ) (δ ψ) θ)) θ :=
  parametricCosinePrimitive_spec _ τ δ (sourceStandardRootOmittedJointDomain hp hp1 V m)
    Ω V hΩ hconv hV hπ (hs.angular_gapNumerator_analyticOnNhd_joint n m V hVW hP)
    hτ hδ (fun x hx => ⟨hx.2,hchart x.2 hx.2 x.1 hx.1⟩)

end SourcePsiIsolatingComplexExtension

/-- All actual gap numerators are jointly analytic on their moving domains
on a common beta neighborhood, together with all analytic boundary roots. -/
theorem exists_sourceAngularBeta_common_domain_with_jointGapNumerators
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          (∀ b : BoundaryCondition, ∀ m : ℤ, AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
            canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) W) ∧
          (∀ n m : ℤ, IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W m) ∧
            AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceAngularGapNumerator hp hp1 n m s t.2 t.1)
              (sourceStandardRootOmittedJointDomain hp hp1 W m)) ∧
          ∀ ψ ∈ W, ∀ n m : ℤ, m ≠ n →
            sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ ∧
              ∀ b ∈ sourceAngularBetaValues hp hp1 n m s ψ, b = sourceAngularBeta hp hp1 n m s ψ := by
  obtain ⟨W₀,V,hW₀,hW₀conn,hW₀real,hV,hVreal,hVW₀,s,hs,hroots,hbeta⟩ :=
    exists_sourceAngularBeta_common_domain_with_analyticBoundaryRoots hp hp1
  obtain ⟨A,hA,_,hAreal,hprod⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  let W := V ∩ A
  have hW : IsOpen W := hV.inter hA
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,(fun φ hφ => ⟨hVreal hφ,hAreal hφ⟩),
    (fun φ hφ => hVW₀ hφ.1),s,hs,
    (fun b m ψ hψ => hroots b m ψ hψ.1),?_,(fun ψ hψ => hbeta ψ hψ.1)⟩
  intro n m
  have hsub : sourceStandardRootOmittedJointDomain hp hp1 W m ⊆
      sourceStandardRootOmittedJointDomain hp hp1 A m := fun t ht => ⟨ht.1.2,ht.2⟩
  have heq : sourceStandardRootOmittedJointDomain hp hp1 W m =
      sourceStandardRootOmittedJointDomain hp hp1 A m ∩ (univ ×ˢ V) := by
    ext t
    exact ⟨fun ht => ⟨⟨ht.1.2,ht.2⟩,mem_univ _,ht.1.1⟩,
      fun ht => ⟨⟨ht.2.2,ht.1.1⟩,ht.1.2⟩⟩
  refine ⟨?_,hs.toSourcePsiIsolatingComplexExtension.angular_gapNumerator_analyticOnNhd_joint
    n m W (fun φ hφ => hVW₀ hφ.1) ((hprod m).2.1.mono hsub)⟩
  rw [heq]
  exact (hprod m).1.inter (isOpen_univ.prod hV)

end NLS.ZakharovShabat
