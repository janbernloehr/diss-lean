import NLS.ComplexAnalysis.ParametricSineTerminal
import NLS.ZakharovShabat.SourceAngularCanonicalCosineEndpoint

/-!
# Source analyticity of beta through periodic Dirichlet terminals

On an open gap the actual normalized anti-discriminant is an analytic sine
coordinate. At either endpoint sine has an analytic inverse. The spectral
square identity and continuity recover the cosine terminal equation. This
fixes the sheet coefficient to -i and makes the beta formula analytic
through its zero endpoint convention. Collapsed source gaps remain separate.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceAngularCanonicalCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {W V : Set (CoeffPair p)}
  {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

/-- The actual Dirichlet sine fixes the differential coefficient to
exactly -i wherever the terminal anti-discriminant is nonzero. -/
theorem beta_eq_neg_I_cosine_of_dirichletSine
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (hmn : m ≠ n)
    (θ : ℂ) (hθ : θ ∈ Ω)
    (hpoint : sourceCanonicalCosinePoint hp hp1 m (θ,ψ) =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
    (hsin : Complex.sin θ = sourceAngularDirichletSine hp hp1 m ψ)
    (hw : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0) :
    sourceAngularBeta hp hp1 n m s ψ =
      -I*sourceAngularCanonicalCosinePrimitive hp hp1 n m s (θ,ψ) := by
  rw [D.beta_eq_cosine_primitive ψ hψ n hmn θ hθ hpoint hw]
  congr 1
  let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let P := sourceStandardRootOmittedProduct hp hp1 m ψ μ
  let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
  have hw' : w ≠ 0 := hw
  have hγ : γ ≠ 0 := D.gap_ne_zero ψ hψ
  have hP : P ≠ 0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ m
    (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
      (ball_subset_closedBall ((D.disc_family ψ hψ).dirichlet_mem_ball m)))
  change (-(γ/2)*Complex.sin θ)*(2*I*P)/w = -I
  change Complex.sin θ = w/(γ*P) at hsin
  rw [hsin]
  field_simp [hγ,hP,hw']

/-- Beta is analytic at either periodic Dirichlet terminal of an open
real gap. The same formula holds through nearby regular and endpoint
terminals; source continuity of beta is not an input. -/
theorem analyticAt_beta_of_real_endpoint
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (hmn : m ≠ n) (hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 φ m) :
    AnalyticAt ℂ (sourceAngularBeta hp hp1 n m s) φ := by
  let τ : CoeffPair p → ℂ := fun ψ => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let δ : CoeffPair p → ℂ := fun ψ => canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let σ : CoeffPair p → ℂ := sourceAngularDirichletSine hp hp1 m
  have hμ : AnalyticAt ℂ μ φ := analyticAt_canonicalPeriodOneBoundaryRoots_of_realType
    hp hp1 .dirichlet φ hreal m
  have hσ : AnalyticAt ℂ σ φ := D.analyticAt_dirichletSine φ hφ hμ
  have hσzero : σ φ = 0 := D.dirichlet_sine_eq_zero_of_endpoint φ hφ hend
  have hδne : δ φ ≠ 0 := div_ne_zero (D.gap_ne_zero φ hφ) (by norm_num)
  obtain ⟨e,hee,he,hse,hce,hpoint⟩ : ∃ e : ℂ, (e = 0 ∨ e = (Real.pi:ℂ)) ∧
      e ∈ segment ℝ (0:ℂ) (Real.pi:ℂ) ∧ Complex.sin e = 0 ∧ Complex.cos e ≠ 0 ∧
        cosineGapPoint (τ φ) (δ φ) e = μ φ := by
    rcases hend with hleft | hright
    · refine ⟨(Real.pi:ℂ),Or.inr rfl,right_mem_segment ℝ _ _,by simp,by simp,?_⟩
      change _ = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m
      rw [hleft]
      simp only [cosineGapPoint,Complex.cos_pi,mul_neg,mul_one]
      dsimp only [τ,δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]
      ring
    · refine ⟨0,Or.inl rfl,left_mem_segment ℝ _ _,by simp,by simp,?_⟩
      change _ = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m
      rw [hright]
      simp only [cosineGapPoint,Complex.cos_zero,mul_one]
      dsimp only [τ,δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]
      ring
  have hcosbase : Complex.cos e = (μ φ-τ φ)/δ φ := by
    apply (eq_div_iff hδne).mpr
    dsimp only [cosineGapPoint] at hpoint
    linear_combination hpoint
  have hVevent : ∀ᶠ ψ in 𝓝 φ, ψ ∈ V := D.source_open.mem_nhds hφ
  have hsq : ∀ᶠ ψ in 𝓝 φ, σ ψ^2+((μ ψ-τ ψ)/δ ψ)^2 = 1 :=
    hVevent.mono fun ψ hψ => D.dirichlet_sine_sq_add_cosine_sq ψ hψ
  obtain ⟨ε,hε,hεφ,hzeros,hbase⟩ := exists_analytic_parametricCosine_terminal_from_sine
    τ δ μ σ φ e (D.midpoint_analytic φ hφ) ((D.gap_analytic φ hφ).div_const) hμ hσ hδne hce
    (hσzero.trans hse.symm) hcosbase hsq
  have hεΩ : ε φ ∈ Ω := by rw [hεφ]; exact D.angle_segment he
  have hH : AnalyticAt ℂ (fun ψ : CoeffPair p =>
      -I*sourceAngularCanonicalCosinePrimitive hp hp1 n m s (ε ψ,ψ)) φ :=
    analyticAt_const.mul ((D.primitive_analytic n (ε φ,φ) ⟨hεΩ,hφ⟩).comp
      (f := fun ψ : CoeffPair p => (ε ψ,ψ)) (hε.prod analyticAt_id))
  have hangle : ∀ᶠ ψ in 𝓝 φ, ε ψ ∈ Ω := hε.continuousAt.eventually (D.angle_open.mem_nhds hεΩ)
  have hHe : ∀ ψ ∈ V, sourceAngularCanonicalCosinePrimitive hp hp1 n m s (e,ψ) = 0 := by
    intro ψ hψ
    rcases hee with rfl | rfl
    · exact D.primitive_zero ψ hψ n hmn
    · exact sourceAngularCanonicalCosinePrimitive_pi hp hp1 n m s ψ
  have heq : (fun ψ : CoeffPair p => -I*sourceAngularCanonicalCosinePrimitive hp hp1 n m s (ε ψ,ψ))
      =ᶠ[𝓝 φ] sourceAngularBeta hp hp1 n m s := by
    filter_upwards [hzeros,hVevent,hangle] with ψ hzero hψ hangle
    by_cases hw : sourceAntiDiscriminantCandidate hp hp1 ψ (μ ψ) = 0
    · have hσψ : σ ψ = 0 := by
        change sourceAntiDiscriminantCandidate hp hp1 ψ (μ ψ)/_ = 0
        rw [hw,zero_div]
      have hεψ : ε ψ = e := hbase ψ (hσψ.trans hse.symm)
      have hendψ : SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ m := by
        by_cases hl : μ ψ = canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
        · exact Or.inl hl
        by_cases hr : μ ψ = canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
        · exact Or.inr hr
        exact False.elim ((sourceDirichletAntiDiscriminant_ne_zero_of_mem_omittedDomain hp hp1 ψ m
          (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
            (ball_subset_closedBall ((D.disc_family ψ hψ).dirichlet_mem_ball m))) hl hr) hw)
      rw [hεψ,hHe ψ hψ,mul_zero,sourceAngularBeta_eq_zero_of_endpoint hp hp1 n m s ψ hendψ]
    · exact (D.beta_eq_neg_I_cosine_of_dirichletSine ψ hψ n hmn (ε ψ) hangle hzero.1 hzero.2 hw).symm
  exact hH.congr heq

/-- All terminal types on an open real source gap have analytic beta.
The anti-discriminant distinguishes the regular and endpoint proofs. -/
theorem analyticAt_beta_of_real_openGap
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (hmn : m ≠ n) : AnalyticAt ℂ (sourceAngularBeta hp hp1 n m s) φ := by
  by_cases hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 φ m
  · exact D.analyticAt_beta_of_real_endpoint φ hφ hreal n hmn hend
  · have hl : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m ≠
        canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m :=
      fun h => hend (Or.inl h)
    have hr : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m ≠
        canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m :=
      fun h => hend (Or.inr h)
    exact D.analyticAt_beta_of_real_regular φ hφ hreal n hmn
      (sourceDirichletAntiDiscriminant_ne_zero_of_mem_omittedDomain hp hp1 φ m
        (((D.disc_family φ hφ).contour_family.2 m).2.2.1
          (ball_subset_closedBall ((D.disc_family φ hφ).dirichlet_mem_ball m))) hl hr)

end SourceAngularCanonicalCosineChartData

/-- One actual common domain supports beta source analyticity at every
open real gap, including both periodic Dirichlet endpoints. All beta
values, analytic boundary sequences, and the original simply connected
psi extension coexist on the constructed domains. -/
theorem exists_sourceAngularBeta_common_domain_with_openGapAnalyticity
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
          ∀ φ : realTypeSourceLocus p, ∀ n m : ℤ, m ≠ n →
            canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0 →
            AnalyticAt ℂ (sourceAngularBeta hp hp1 n m s) φ.val := by
  obtain ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hroots,hbeta,hcharts⟩ :=
    exists_sourceAngularBeta_common_domain_with_canonicalCosinePrimitives hp hp1
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hroots,hbeta,?_⟩
  intro φ n m hmn hgap
  obtain ⟨V,Ω,c,R,hφV,D⟩ := hcharts φ m hgap
  exact D.analyticAt_beta_of_real_openGap φ.val hφV φ.property n hmn

end NLS.ZakharovShabat
