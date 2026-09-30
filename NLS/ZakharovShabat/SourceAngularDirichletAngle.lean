import NLS.ComplexAnalysis.ParametricTrigonometricTerminal
import NLS.ZakharovShabat.SourceAngularCanonicalCosineEndpoint

/-!
# Analytic actual Dirichlet terminal angles with a fixed sheet sign

Real interlacing supplies a base cosine angle in the entire closed
interval from zero to pi. The actual normalized Dirichlet sine fixes
one constant sign. The spectral square identity then constructs an
analytic moving angle with both exact terminal coordinates, including
either periodic endpoint of an open gap.
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

/-- Every actual real Dirichlet terminal has a base angle in the
closed gap interval and one sign matching its actual normalized sine. -/
theorem exists_real_dirichlet_angle_with_sign
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ e κ : ℂ, e ∈ segment ℝ (0 : ℂ) (Real.pi : ℂ) ∧ (κ = 1 ∨ κ = -1) ∧
      sourceCanonicalCosinePoint hp hp1 m (e,φ) = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m ∧
      Complex.sin e = κ * sourceAngularDirichletSine hp hp1 m φ := by
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m
  let δ := canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m / 2
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m
  have hδ : δ ≠ 0 := div_ne_zero (D.gap_ne_zero φ hφ) (by norm_num)
  have hl : τ - δ = canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m := by
    dsimp only [τ,δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hr : τ + δ = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m := by
    dsimp only [τ,δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hseg : μ ∈ segment ℝ (τ - δ) (τ + δ) := by
    rw [hl,hr]
    exact canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1 .dirichlet φ hreal m
  obtain ⟨e,he,hpoint⟩ : ∃ e : ℂ, e ∈ segment ℝ (0 : ℂ) (Real.pi : ℂ) ∧
      cosineGapPoint τ δ e = μ := by
    by_cases hleft : μ = τ - δ
    · refine ⟨(Real.pi : ℂ),right_mem_segment ℝ _ _,?_⟩
      simpa only [cosineGapPoint,Complex.cos_pi,mul_neg,mul_one,← sub_eq_add_neg] using hleft.symm
    by_cases hright : μ = τ + δ
    · refine ⟨0,left_mem_segment ℝ _ _,?_⟩
      simpa only [cosineGapPoint,Complex.cos_zero,mul_one] using hright.symm
    obtain ⟨e,he,_,hpoint⟩ := exists_cosineGapPoint_regular_angle τ δ μ hseg hleft hright
    exact ⟨e,he,hpoint⟩
  have hcos : Complex.cos e = (μ - τ) / δ := by
    apply (eq_div_iff hδ).mpr
    dsimp only [cosineGapPoint] at hpoint
    linear_combination hpoint
  have hsq := D.dirichlet_sine_sq_add_cosine_sq φ hφ
  have htrig := Complex.sin_sq_add_cos_sq e
  rw [hcos] at htrig
  have hsinSq : Complex.sin e ^ 2 = sourceAngularDirichletSine hp hp1 m φ ^ 2 := by
    change sourceAngularDirichletSine hp hp1 m φ ^ 2 + ((μ - τ) / δ) ^ 2 = 1 at hsq
    linear_combination htrig - hsq
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sin e) (sourceAngularDirichletSine hp hp1 m φ) hsinSq with hs | hs
  · exact ⟨e,1,he,Or.inl rfl,hpoint,by simpa only [one_mul] using hs⟩
  · exact ⟨e,-1,he,Or.inr rfl,hpoint,by simpa only [neg_one_mul] using hs⟩

/-- Both normalized terminal coordinates determine an analytic
moving angle on a source neighborhood, for either constant sheet sign.
This includes endpoint terminals with zero anti-discriminant. -/
theorem exists_local_analytic_dirichlet_angle_with_sign
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V)
    (hμ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ)
    (e κ : ℂ) (he : e ∈ Ω) (hκ : κ = 1 ∨ κ = -1)
    (hpoint : sourceCanonicalCosinePoint hp hp1 m (e,φ) = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m)
    (hsin : Complex.sin e = κ * sourceAngularDirichletSine hp hp1 m φ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧ ∃ ε : CoeffPair p → ℂ,
      AnalyticOnNhd ℂ ε U ∧ ε φ = e ∧ ∀ ψ ∈ U, ε ψ ∈ Ω ∧
        sourceCanonicalCosinePoint hp hp1 m (ε ψ,ψ) = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∧
        Complex.sin (ε ψ) = κ * sourceAngularDirichletSine hp hp1 m ψ := by
  let τ : CoeffPair p → ℂ := fun ψ => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let δ : CoeffPair p → ℂ := fun ψ => canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let σ : CoeffPair p → ℂ := fun ψ => κ * sourceAngularDirichletSine hp hp1 m ψ
  have hκsq : κ ^ 2 = 1 := by rcases hκ with rfl | rfl <;> norm_num
  have hsq : ∀ᶠ ψ in 𝓝 φ, σ ψ ^ 2 + ((μ ψ - τ ψ) / δ ψ) ^ 2 = 1 := by
    filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
    dsimp only [σ]
    rw [mul_pow,hκsq,one_mul]
    exact D.dirichlet_sine_sq_add_cosine_sq ψ hψ
  obtain ⟨ε,hε,hεφ,hzeros⟩ := exists_analytic_parametricCosine_terminal_with_sine
    τ δ μ σ φ e (D.midpoint_analytic φ hφ) ((D.gap_analytic φ hφ).div_const) hμ
    (analyticAt_const.mul (D.analyticAt_dirichletSine φ hφ hμ))
    (div_ne_zero (D.gap_ne_zero φ hφ) (by norm_num)) hsin.symm hpoint hsq
  have hangle : ∀ᶠ ψ in 𝓝 φ, ε ψ ∈ Ω :=
    hε.continuousAt.eventually (D.angle_open.mem_nhds (by rwa [hεφ]))
  have hnear : ∀ᶠ ψ in 𝓝 φ, ψ ∈ V ∧ AnalyticAt ℂ ε ψ ∧ ε ψ ∈ Ω ∧
      sourceCanonicalCosinePoint hp hp1 m (ε ψ,ψ) = μ ψ ∧ Complex.sin (ε ψ) = σ ψ := by
    filter_upwards [D.source_open.mem_nhds hφ,hε.eventually_analyticAt,hangle,hzeros] with ψ hψ ha he hz
    exact ⟨hψ,ha,he,hz⟩
  obtain ⟨U,hUsub,hU,hφU⟩ := _root_.mem_nhds_iff.mp hnear
  exact ⟨U,hU,hφU,fun ψ hψ => (hUsub hψ).1,ε,
    (fun ψ hψ => (hUsub hψ).2.1),hεφ,fun ψ hψ => (hUsub hψ).2.2⟩

/-- Every open real gap, including either periodic Dirichlet endpoint,
has one analytic actual terminal-angle family and one fixed sheet sign. -/
theorem exists_local_analytic_real_dirichlet_angle
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ ε : CoeffPair p → ℂ, ∃ κ : ℂ, (κ = 1 ∨ κ = -1) ∧ AnalyticOnNhd ℂ ε U ∧
        ε φ ∈ segment ℝ (0 : ℂ) (Real.pi : ℂ) ∧ ∀ ψ ∈ U, ε ψ ∈ Ω ∧
          sourceCanonicalCosinePoint hp hp1 m (ε ψ,ψ) = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∧
          Complex.sin (ε ψ) = κ * sourceAngularDirichletSine hp hp1 m ψ := by
  obtain ⟨e,κ,he,hκ,hpoint,hsin⟩ := D.exists_real_dirichlet_angle_with_sign φ hφ hreal
  obtain ⟨U,hU,hφU,hUV,ε,hε,hεφ,hzeros⟩ := D.exists_local_analytic_dirichlet_angle_with_sign φ hφ
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ hreal m)
    e κ (D.angle_segment he) hκ hpoint hsin
  exact ⟨U,hU,hφU,hUV,ε,κ,hκ,hε,hεφ.symm ▸ he,hzeros⟩

end SourceAngularCanonicalCosineChartData
end NLS.ZakharovShabat
