import NLS.ComplexAnalysis.ParametricAnnularPrimitive
import NLS.ZakharovShabat.SourceAngularAnnulusPrimitive
import NLS.ZakharovShabat.SourceAngularBetaEndpointAnalytic
import NLS.ZakharovShabat.SourceCanonicalRootJointAnalytic

/-!
# Actual joint angular primitives around open and collapsed gaps

The assigned contour periods are exact on a source neighborhood. Smaller
fixed circles enclose the moving selected gap and its Dirichlet terminal.
The canonical angular integrand is jointly analytic on the intervening
annulus, where its zero off-diagonal period gives an explicit joint
primitive normalized at a fixed regular anchor. Individual periodic
endpoints need only be continuous at the real base source.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularJointAnnularPrimitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (c : ℂ) (r R : ℝ) (z₀ : ℂ) : ℂ × CoeffPair p → ℂ :=
  parametricAnnularPrimitiveAtAnchor
    (sourceAngularIntegrand n s (sourceCanonicalRootJointProduct hp hp1)) c r R z₀

/-- Fixed annuli and original assigned discs support every off-diagonal
numerator at once. No nonzero-gap condition occurs in this data. -/
structure SourceAngularJointAnnulusChartData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (W V : Set (CoeffPair p)) (c : ℤ → ℂ) (T : ℤ → ℝ)
    (r R : ℝ) (z₀ : ℂ) : Prop where
  source_open : IsOpen V
  source_subset : V ⊆ W
  inner_pos : 0 < r
  inner_lt_outer : r < R
  outer_lt_assigned : R < T m
  anchor_mem : z₀ ∈ ball (c m) R \ closedBall (c m) r
  disc_family : ∀ ψ ∈ V, SourceAngularDirichletDiscFamilyData hp hp1 s ψ c T
  gap_enclosed : ∀ ψ ∈ V, sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) r
  terminal_enclosed : ∀ ψ ∈ V,
    canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (c m) r
  integrand_analytic : ∀ n : ℤ,
    AnalyticOnNhd ℂ (sourceAngularIntegrand n s (sourceCanonicalRootJointProduct hp hp1))
      ((closedBall (c m) R \ ball (c m) r) ×ˢ V)
  selected_root_analytic : AnalyticOnNhd ℂ
    (fun x : ℂ × CoeffPair p => sourceStandardRoot hp hp1 x.2 m x.1)
    ((closedBall (c m) R \ ball (c m) r) ×ˢ V)
  omitted_analytic : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 m)
    (ball (c m) (T m) ×ˢ V)
  period_zero : ∀ n : ℤ, m ≠ n → ∀ ψ ∈ V,
    (∮ z in C(c m,r), sourceAngularIntegrand n s
      (sourceCanonicalRootJointProduct hp hp1) (z,ψ)) = 0
  primitive_analytic : ∀ n : ℤ,
    AnalyticOnNhd ℂ (sourceAngularJointAnnularPrimitive hp hp1 n s (c m) r R z₀)
      ((ball (c m) R \ closedBall (c m) r) ×ˢ V)
  primitive_anchor : ∀ n : ℤ, ∀ ψ : CoeffPair p,
    sourceAngularJointAnnularPrimitive hp hp1 n s (c m) r R z₀ (z₀,ψ) = 0
  spectral_derivative : ∀ n : ℤ, m ≠ n → ∀ ψ ∈ V,
    ∀ z ∈ ball (c m) R \ closedBall (c m) r,
      HasDerivAt (fun w => sourceAngularJointAnnularPrimitive hp hp1 n s (c m) r R z₀ (w,ψ))
        (sourceAngularIntegrand n s (sourceCanonicalRootJointProduct hp hp1) (z,ψ)) z

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Fixed enclosing geometry and actual assigned periods construct a
joint annular primitive chart on the specified source neighborhood. -/
theorem joint_angular_annulus_chart_of_geometry
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWW₀ : W ⊆ W₀)
    (hA : ∀ ψ ∈ W, ∀ k : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k)^2) ψ)
    (V : Set (CoeffPair p)) (hV : IsOpen V) (hVW : V ⊆ W)
    (m : ℤ) (c : ℤ → ℂ) (T : ℤ → ℝ) (r R : ℝ) (z₀ : ℂ)
    (hr : 0 < r) (hrR : r < R) (hRT : R < T m)
    (hz₀ : z₀ ∈ ball (c m) R \ closedBall (c m) r)
    (hdiscs : ∀ ψ ∈ V, SourceAngularDirichletDiscFamilyData hp hp1 s ψ c T)
    (hgap : ∀ ψ ∈ V, sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) r)
    (hterminal : ∀ ψ ∈ V,
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (c m) r) :
    SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀ := by
  obtain ⟨_,hQ⟩ := sourceCanonicalRootJointProduct_analyticOnNhd_of_symmetric hp hp1 W hW hA
  obtain ⟨_,hP⟩ := sourceStandardRootOmittedJointProduct_analyticOnNhd_of_symmetric hp hp1 W hW hA m
  have hjoint (ψ : CoeffPair p) (hψ : ψ ∈ V)
      (z : ℂ) (hz : z ∈ closedBall (c m) R \ ball (c m) r) :
      (z,ψ) ∈ sourceCanonicalRootJointDomain hp hp1 W := by
    refine ⟨hVW hψ,?_⟩
    intro k
    by_cases hkm : k = m
    · subst k
      exact fun h => hz.2 (hgap ψ hψ h)
    · exact ((hdiscs ψ hψ).contour_family.2 m).2.2.1
        (closedBall_subset_closedBall hRT.le hz.1) k hkm
  have hf (n : ℤ) : AnalyticOnNhd ℂ
      (sourceAngularIntegrand n s (sourceCanonicalRootJointProduct hp hp1))
      ((closedBall (c m) R \ ball (c m) r) ×ˢ V) := by
    intro x hx
    have hxD := hjoint x.2 hx.2 x.1 hx.1
    exact (hs.analytic_numerator_joint n x ⟨mem_univ _,hWW₀ hxD.1⟩).div
      (hQ x hxD) (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 x.2 x.1 hxD.2)
  have hselected : AnalyticOnNhd ℂ
      (fun x : ℂ × CoeffPair p => sourceStandardRoot hp hp1 x.2 m x.1)
      ((closedBall (c m) R \ ball (c m) r) ×ˢ V) := by
    intro x hx
    exact sourceStandardRoot_joint_analyticAt_of_symmetric hp hp1 x.2 m x.1
      (hA x.2 (hVW hx.2) m).1 (hA x.2 (hVW hx.2) m).2 ((hjoint x.2 hx.2 x.1 hx.1).2 m)
  have homitted : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 m)
      (ball (c m) (T m) ×ˢ V) := by
    intro x hx
    exact hP x ⟨hVW hx.2,((hdiscs x.2 hx.2).contour_family.2 m).2.2.1
      (ball_subset_closedBall hx.1)⟩
  have hperiod (n : ℤ) (hmn : m ≠ n) (ψ : CoeffPair p) (hψ : ψ ∈ V) :
      (∮ z in C(c m,r), sourceAngularIntegrand n s
        (sourceCanonicalRootJointProduct hp hp1) (z,ψ)) = 0 := by
    have hzero : sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ (c m) r = 0 := by
      rw [sourcePsiContour_eq_of_nested_enclosingCircles hp hp1 n m (s n ψ : Coeff p) ψ
        (c m) (c m) r (T m) hr ((hdiscs ψ hψ).contour_family.2 m).1 (hgap ψ hψ)
        ((hdiscs ψ hψ).contour_family.2 m).2.1
        (closedBall_subset_closedBall (hrR.trans hRT).le)
        ((hdiscs ψ hψ).contour_family.2 m).2.2.1]
      simpa only [if_neg hmn] using (hdiscs ψ hψ).periods n m
    change (2*Real.pi : ℂ)⁻¹ * (∮ z in C(c m,r), sourceAngularIntegrand n s
      (sourceCanonicalRootJointProduct hp hp1) (z,ψ)) = 0 at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero (by simp [Real.pi_ne_zero]))
  refine ⟨hV,hVW,hr,hrR,hRT,hz₀,hdiscs,hgap,hterminal,
    hf,hselected,homitted,hperiod,?_,?_,?_⟩
  · intro n
    exact analyticOnNhd_parametricAnnularPrimitiveAtAnchor _ _ r R hr hrR V hV (hf n) z₀ hz₀
  · intro n ψ
    exact parametricAnnularPrimitiveAtAnchor_anchor _ _ r R z₀ ψ
  · intro n hmn ψ hψ z hz
    exact hasDerivAt_parametricAnnularPrimitiveAtAnchor _ _ r R hr hrR V hV (hf n) z₀ ψ hψ
      (hperiod n hmn ψ hψ) z hz

/-- The actual canonical root and assigned contour family construct one
joint primitive chart near any real source, including a collapsed gap.
No primitive, period, endpoint branch, or terminal containment is supplied. -/
theorem exists_local_joint_angular_annulus_primitives
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWW₀ : W ⊆ W₀)
    (hA : ∀ ψ ∈ W, ∀ k : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k)^2) ψ)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hreal : IsRealType (CoeffPair.toMax p φ)) (m : ℤ) :
    ∃ V : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
      ∃ r R : ℝ, ∃ z₀ : ℂ, φ ∈ V ∧
        SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀ := by
  obtain ⟨δ,hδ,hballW,c,T,hdiscs⟩ := hs.exists_local_angular_dirichlet_disc_family
    ⟨φ,hreal⟩ W hW hφ
  have hbase := hdiscs φ (mem_ball_self hδ)
  have hgeom := hbase.contour_family.2 m
  obtain ⟨r,R,hr,hrR,hRT,hseg⟩ := exists_nested_radii_of_segment_subset_ball
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m)
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m)
    (c m) (T m) hgeom.2.1
  have hL : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ∈ ball (c m) r :=
    (continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ hreal m).eventually
      (isOpen_ball.mem_nhds (hseg (left_mem_segment ℝ _ _)))
  have hRt : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ∈ ball (c m) r :=
    (continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ hreal m).eventually
      (isOpen_ball.mem_nhds (hseg (right_mem_segment ℝ _ _)))
  have hμ : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (c m) r :=
    (continuousAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ hreal m).eventually
      (isOpen_ball.mem_nhds (hseg
        (canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1 .dirichlet φ hreal m)))
  obtain ⟨O,hOsub,hO,hφO⟩ := _root_.mem_nhds_iff.mp (hL.and (hRt.and hμ))
  let V := ball φ δ ∩ O
  have hV : IsOpen V := isOpen_ball.inter hO
  have hVW : V ⊆ W := fun ψ hψ => hballW hψ.1
  have hgap (ψ : CoeffPair p) (hψ : ψ ∈ V) :
      sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) r :=
    (convex_ball (c m) r).segment_subset (hOsub hψ.2).1 (hOsub hψ.2).2.1
  let z₀ : ℂ := c m + ((r+R)/2 : ℝ)
  have hz₀ : z₀ ∈ ball (c m) R \ closedBall (c m) r := by
    have hdist : dist z₀ (c m) = (r+R)/2 := by
      simp only [z₀,dist_eq_norm,add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs]
      rw [abs_of_pos (by linarith)]
    exact ⟨mem_ball.mpr (by rw [hdist]; linarith),
      fun h => by have hle := mem_closedBall.mp h; rw [hdist] at hle; linarith⟩
  exact ⟨V,c,T,r,R,z₀,⟨mem_ball_self hδ,hφO⟩,
    hs.joint_angular_annulus_chart_of_geometry W hW hWW₀ hA V hV hVW m c T r R z₀
      hr hrR hRT hz₀ (fun ψ hψ => hdiscs ψ hψ.1) hgap
      (fun ψ hψ => (hOsub hψ.2).2.2)⟩

end SourcePsiIsolatingComplexExtension

/-- The actual beta neighborhood can retain joint annular primitives at
every real gap, including collapsed gaps, alongside its open-gap beta
analyticity and the full simply connected psi extension. -/
theorem exists_sourceAngularBeta_common_domain_with_jointAnnularPrimitives
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          (∀ b : BoundaryCondition, ∀ m : ℤ,
            AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) W) ∧
          (∀ ψ ∈ W, ∀ n m : ℤ, m ≠ n →
            sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ ∧
              ∀ b ∈ sourceAngularBetaValues hp hp1 n m s ψ, b = sourceAngularBeta hp hp1 n m s ψ) ∧
          (∀ φ : realTypeSourceLocus p, ∀ n m : ℤ, m ≠ n →
            canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0 →
            AnalyticAt ℂ (sourceAngularBeta hp hp1 n m s) φ.val) ∧
          ∀ φ : realTypeSourceLocus p, ∀ m : ℤ,
            ∃ V : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
              ∃ r R : ℝ, ∃ z₀ : ℂ, φ.val ∈ V ∧
                SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀ := by
  obtain ⟨W₀,O,hW₀,hW₀conn,hW₀real,hO,hOreal,hOW₀,s,hs,hroots,hbeta,hopen⟩ :=
    exists_sourceAngularBeta_common_domain_with_openGapAnalyticity hp hp1
  obtain ⟨A,hA,_,hAreal,hsym⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  let W := O ∩ A
  have hW : IsOpen W := hO.inter hA
  have hWreal : realTypeSourceLocus p ⊆ W := fun φ hφ => ⟨hOreal hφ,hAreal hφ⟩
  have hWW₀ : W ⊆ W₀ := fun φ hφ => hOW₀ hφ.1
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,
    (fun b m ψ hψ => hroots b m ψ hψ.1),(fun ψ hψ => hbeta ψ hψ.1),hopen,?_⟩
  intro φ m
  exact hs.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives
    W hW hWW₀ (fun ψ hψ => hsym ψ hψ.2) φ.val (hWreal φ.property) φ.property m

end NLS.ZakharovShabat
