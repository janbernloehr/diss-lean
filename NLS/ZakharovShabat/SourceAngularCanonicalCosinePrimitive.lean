import NLS.ComplexAnalysis.ParametricCosineChart
import NLS.ZakharovShabat.SourceOpenGapEndpointAnalytic
import NLS.ZakharovShabat.SourceAngularJointPrimitive

/-!
# Actual canonical cosine primitive families near open real gaps

Construct the source and angle charts from canonical spectral data. The
assigned discs contain the moving gaps and Dirichlet roots and retain all
off-diagonal periods. Their cosine images stay in these same discs. The
normalized primitive is jointly analytic for every numerator index, with
the actual canonical midpoint and half-gap, rather than supplied parameters.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual canonical cosine coordinate of a selected source gap. -/
def sourceCanonicalCosinePoint (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) :
    ℂ × CoeffPair p → ℂ := fun x => cosineGapPoint
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential x.2) (periodOnePotential_mem x.2) m)
      (canonicalPeriodicGap hp hp1 (periodOnePotential x.2) (periodOnePotential_mem x.2) m/2) x.1

/-- The endpoint-angle normalized cosine primitive with the actual canonical
midpoint, half-gap, and literal angular gap numerator. -/
def sourceAngularCanonicalCosinePrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) : ℂ × CoeffPair p → ℂ :=
  parametricCosinePrimitive (fun x => sourceAngularGapNumerator hp hp1 n m s x.2 x.1)
    (fun ψ => canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (fun ψ => canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2)

/-- Actual source and full angle-interval charts retaining the assigned
disc family and its endpoint spectral data. -/
structure SourceAngularCanonicalCosineChartData (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (W V : Set (CoeffPair p))
    (Ω : Set ℂ) (c : ℤ → ℂ) (R : ℤ → ℝ) : Prop where
  source_open : IsOpen V
  source_subset : V ⊆ W
  angle_open : IsOpen Ω
  angle_convex : Convex ℝ Ω
  angle_segment : segment ℝ (0:ℂ) (Real.pi:ℂ) ⊆ Ω
  midpoint_analytic : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) V
  gap_analytic : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodicGap
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) V
  gap_ne_zero : ∀ ψ ∈ V, canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0
  disc_family : ∀ ψ ∈ V, SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R
  endpoint_data : ∀ ψ ∈ V, SourceAngularEndpointSpectralData hp hp1 ψ m
  cosine_enclosed : ∀ ψ ∈ V, ∀ θ ∈ Ω, sourceCanonicalCosinePoint hp hp1 m (θ,ψ) ∈ ball (c m) (R m)
  numerator_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (fun x : ℂ × CoeffPair p =>
    sourceAngularGapNumerator hp hp1 n m s x.2 (sourceCanonicalCosinePoint hp hp1 m x)) (Ω ×ˢ V)
  primitive_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ
    (sourceAngularCanonicalCosinePrimitive hp hp1 n m s) (Ω ×ˢ V)
  primitive_derivative : ∀ n : ℤ, ∀ ψ ∈ V, ∀ θ ∈ Ω,
    HasDerivAt (fun e => sourceAngularCanonicalCosinePrimitive hp hp1 n m s (e,ψ))
      (sourceAngularGapNumerator hp hp1 n m s ψ (sourceCanonicalCosinePoint hp hp1 m (θ,ψ))) θ

@[simp] theorem sourceAngularCanonicalCosinePrimitive_pi (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) :
    sourceAngularCanonicalCosinePrimitive hp hp1 n m s ((Real.pi:ℂ),ψ) = 0 :=
  parametricConvexPrimitive_anchor _ _ ψ

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The actual psi family constructs all chart geometry and joint primitive
families near a real source with an open selected gap. -/
theorem exists_local_canonical_cosine_angular_primitives
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWW₀ : W ⊆ W₀)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hreal : IsRealType (CoeffPair.toMax p φ)) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0)
    (hD : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W m))
    (hP : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 m)
      (sourceStandardRootOmittedJointDomain hp hp1 W m)) :
    ∃ V : Set (CoeffPair p), ∃ Ω : Set ℂ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      φ ∈ V ∧ SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R := by
  obtain ⟨ρ,hρ,hballW,c,R,hdiscs⟩ := hs.exists_local_angular_dirichlet_disc_family
    ⟨φ,hreal⟩ W hW hφ
  obtain ⟨O,hO,hφO,hOball,hτ,hγ,hγne⟩ := exists_local_sourceCanonicalOpenGap_analytic
    hp hp1 (ball φ ρ) isOpen_ball φ (mem_ball_self hρ) hreal m hgap
  let τ : CoeffPair p → ℂ := fun ψ => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let δ : CoeffPair p → ℂ := fun ψ => canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2
  let D : Set (ℂ × CoeffPair p) := (ball (c m) (R m) ×ˢ W) ∩
    sourceStandardRootOmittedJointDomain hp hp1 W m
  have hDopen : IsOpen D := (isOpen_ball.prod hW).inter hD
  have hl : τ φ-δ φ = canonicalPeriodicLeft hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) m := by
    dsimp [τ,δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hr : τ φ+δ φ = canonicalPeriodicRight hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) m := by
    dsimp [τ,δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hbase := hdiscs φ (mem_ball_self hρ)
  have hgeom := hbase.contour_family.2 m
  have hbaseGap : ∀ z ∈ segment ℝ (τ φ-δ φ) (τ φ+δ φ), (z,φ) ∈ D := by
    intro z hz
    rw [hl,hr] at hz
    have hzball : z ∈ ball (c m) (R m) := hgeom.2.1 hz
    exact ⟨⟨hzball,hφ⟩,hφ,hgeom.2.2.1 (ball_subset_closedBall hzball)⟩
  obtain ⟨V,Ω,hV,hφV,hVO,hΩ,hconv,hangle,hchart⟩ := exists_local_parametricCosine_chart
    τ δ O hO hτ (fun ψ hψ => (hγ ψ hψ).div_const) D hDopen φ hφO hbaseGap
  have hVW : V ⊆ W := hVO.trans (hOball.trans hballW)
  have hVball : V ⊆ ball φ ρ := hVO.trans hOball
  have hendpoint (ψ : CoeffPair p) (hψ : ψ ∈ V) : SourceAngularEndpointSpectralData hp hp1 ψ m := by
    have hψW := hVW hψ
    have hgeomψ := (hdiscs ψ (hVball hψ)).contour_family.2 m
    have hopen : IsOpen (sourceStandardRootOmittedDomain hp hp1 ψ m) := by
      have heq : sourceStandardRootOmittedDomain hp hp1 ψ m =
          (fun z : ℂ => (z,ψ)) ⁻¹' sourceStandardRootOmittedJointDomain hp hp1 W m := by
        ext z
        exact ⟨fun hz => ⟨hψW,hz⟩,And.right⟩
      rw [heq]
      exact hD.preimage (continuous_id.prodMk continuous_const)
    exact ⟨hopen,(fun z hz => hgeomψ.2.2.1 (ball_subset_closedBall (hgeomψ.2.1 hz))),
      sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 m W hP ψ hψW⟩
  have hg (n : ℤ) : AnalyticOnNhd ℂ (fun x : ℂ × CoeffPair p =>
      sourceAngularGapNumerator hp hp1 n m s x.2 x.1)
      (sourceStandardRootOmittedJointDomain hp hp1 W m) :=
    hs.angular_gapNumerator_analyticOnNhd_joint n m W hWW₀ hP
  have hmap : ∀ x ∈ Ω ×ˢ V, (cosineGapPoint (τ x.2) (δ x.2) x.1,x.2) ∈
      sourceStandardRootOmittedJointDomain hp hp1 W m := fun x hx => (hchart x.2 hx.2 x.1 hx.1).2
  have hτV : AnalyticOnNhd ℂ τ V := hτ.mono hVO
  have hδV : AnalyticOnNhd ℂ δ V := fun ψ hψ => (hγ ψ (hVO hψ)).div_const
  have hπΩ : (Real.pi:ℂ) ∈ Ω := hangle (right_mem_segment ℝ _ _)
  refine ⟨V,Ω,c,R,hφV,⟨hV,hVW,hΩ,hconv,hangle,hτV,hγ.mono hVO,
    (fun ψ hψ => hγne ψ (hVO hψ)),(fun ψ hψ => hdiscs ψ (hVball hψ)),hendpoint,
    (fun ψ hψ θ hθ => (hchart ψ hψ θ hθ).1.1),?_,?_,?_⟩⟩
  · intro n
    exact analyticOnNhd_parametricCosineNumerator _ τ δ _ Ω V (hg n) hτV hδV hmap
  · intro n
    exact (parametricCosinePrimitive_spec _ τ δ _ Ω V hΩ hconv hV hπΩ (hg n) hτV hδV hmap).1
  · intro n ψ hψ θ hθ
    exact (parametricCosinePrimitive_spec _ τ δ _ Ω V hΩ hconv hV hπΩ (hg n) hτV hδV hmap).2.2 ψ hψ θ hθ

end SourcePsiIsolatingComplexExtension

namespace SourceAngularCanonicalCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {W V : Set (CoeffPair p)}
  {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

/-- At each source, every endpoint-normalized actual canonical primitive
agrees with the jointly analytic canonical cosine family on a chart
containing the whole real angle interval, with the exact root coefficient. -/
theorem spectral_matching
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (F : ℂ → ℂ) (A : ℂ)
    (hF : ∀ z ∈ ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z)
    (hA : Tendsto F (𝓝[ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A)) :
    ∃ U : Set ℂ, IsOpen U ∧ Convex ℝ U ∧ segment ℝ (0:ℂ) (Real.pi:ℂ) ⊆ U ∧ U ⊆ Ω ∧
      ∀ θ ∈ U, θ.im ≠ 0 → F (sourceCanonicalCosinePoint hp hp1 m (θ,ψ))-A =
        cosineRootCoefficient (sourceStandardRoot hp hp1 ψ m)
          (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
          (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2) θ *
          sourceAngularCanonicalCosinePrimitive hp hp1 n m s (θ,ψ) := by
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let δ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2
  have hl : τ-δ = canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    dsimp [τ,δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hr : τ+δ = canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    dsimp [τ,δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hδ : δ ≠ 0 := div_ne_zero (D.gap_ne_zero ψ hψ) (by norm_num)
  have hgeom := (D.disc_family ψ hψ).contour_family.2 m
  have hnum : AnalyticOnNhd ℂ (sourceAngularGapNumerator hp hp1 n m s ψ) (ball (c m) (R m)) :=
    (sourceAngularGapNumerator_analyticOnNhd hp hp1 n m s ψ (D.endpoint_data ψ hψ).analytic_omitted).mono
      (fun z hz => hgeom.2.2.1 (ball_subset_closedBall hz))
  obtain ⟨S,H,hS,hSconv,hseg,hT,hH,hmatch⟩ := exists_cosine_gap_primitive_chart
    (sourceAngularGapNumerator hp hp1 n m s ψ) (sourceStandardRoot hp hp1 ψ m) F
    (ball (c m) (R m)) τ δ A isOpen_ball hδ (by rw [hl,hr]; exact hgeom.2.1) hnum
    (by
      rw [hl,hr]
      intro z hz
      exact (sourceStandardRoot_analyticAt hp hp1 ψ m z hz.2).continuousAt.continuousWithinAt)
    (by
      rw [hl,hr]
      intro z hz
      exact sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ m z hz.2)
    (by
      rw [hl,hr]
      intro z hz
      rw [← sourceAngularIntegrand_eq_gapNumerator_div_standardRoot hp hp1 n m s ψ z]
      exact hF z hz)
    (by rw [hl,hr]; exact hA)
  have hangle : AnalyticOnNhd ℂ (fun θ => sourceAngularGapNumerator hp hp1 n m s ψ
      (sourceCanonicalCosinePoint hp hp1 m (θ,ψ))) Ω := by
    intro θ hθ
    exact (D.numerator_analytic n (θ,ψ) ⟨hθ,hψ⟩).comp
      (f := fun θ : ℂ => (θ,ψ)) (analyticAt_id.prod analyticAt_const)
  have hπΩ : (Real.pi:ℂ) ∈ Ω := D.angle_segment (right_mem_segment ℝ _ _)
  have hπS : (Real.pi:ℂ) ∈ S := hseg (right_mem_segment ℝ _ _)
  refine ⟨Ω ∩ S,D.angle_open.inter hS,D.angle_convex.inter hSconv,
    (fun θ hθ => ⟨D.angle_segment hθ,hseg hθ⟩),inter_subset_left,?_⟩
  intro θ hθ hi
  have heq : sourceAngularCanonicalCosinePrimitive hp hp1 n m s (θ,ψ) = H θ-H (Real.pi:ℂ) :=
    parametricConvexPrimitive_eq_sub_of_primitive _ (Ω ∩ S) _ ψ (D.angle_convex.inter hSconv)
      ⟨hπΩ,hπS⟩ (hangle.continuousOn.mono inter_subset_left) H (fun e he => hH e he.2) θ hθ
  rw [heq]
  exact hmatch θ hθ.2 hi

/-- The preserved actual periods construct the sheet primitives whose
exterior values match the joint canonical cosine family. No primitive is
an input to this existence theorem. -/
theorem exists_sheet_primitives_with_cosine_matching
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (hmn : m ≠ n) (w : ℂ) (hw : w ≠ 0) :
    ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ E : ℂ → ℂ, ∃ U : Set ℂ,
      SourceAngularSheetPrimitiveData hp hp1 n m s ψ (c m) (R m) w F A E ∧
        IsOpen U ∧ Convex ℝ U ∧ segment ℝ (0:ℂ) (Real.pi:ℂ) ⊆ U ∧ U ⊆ Ω ∧
        ∀ θ ∈ U, θ.im ≠ 0 → F (sourceCanonicalCosinePoint hp hp1 m (θ,ψ))-A =
          cosineRootCoefficient (sourceStandardRoot hp hp1 ψ m)
            (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
            (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2) θ *
            sourceAngularCanonicalCosinePrimitive hp hp1 n m s (θ,ψ) := by
  have hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    intro heq
    apply D.gap_ne_zero ψ hψ
    simp only [canonicalPeriodicGap,heq,sub_self]
  obtain ⟨F,A,E,hE⟩ := (D.disc_family ψ hψ).exists_sheet_primitive_data n m hmn hgap
    (D.endpoint_data ψ hψ) w hw
  obtain ⟨U,hU,hconv,hangle,hUΩ,hmatch⟩ := D.spectral_matching ψ hψ n F A
    hE.hasDerivAt_exterior hE.tendsto_left_exterior
  exact ⟨F,A,E,U,hE,hU,hconv,hangle,hUΩ,hmatch⟩

end SourceAngularCanonicalCosineChartData

end NLS.ZakharovShabat
