import NLS.ZakharovShabat.SourceAngularBranchEtaRepresentative

/-! # Analytic eta source values at complex periodic terminals

Both endpoint base angles belong to the constructed branch chart.
The circle identity fixes their zero sine coordinate, so their moving
actual Dirichlet terminal has an analytic eta source representative.
No real-source or nonzero anti-discriminant hypothesis is used.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceAngularBranchEtaTerminalData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (δ : CoeffPair p → ℂ)
    (V U : Set (CoeffPair p)) (Ω : Set ℂ) (ε : CoeffPair p → ℂ) : Prop where
  source_open : IsOpen U
  source_subset : U ⊆ V
  angle_analytic : AnalyticOnNhd ℂ ε U
  angle_mem : ∀ ψ ∈ U, ε ψ ∈ Ω
  terminal_point : ∀ ψ ∈ U, sourceAngularBranchCosinePoint hp hp1 m δ (ε ψ,ψ) =
    canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  terminal_sine : ∀ ψ ∈ U, Complex.sin (ε ψ) = sourceAngularBranchDirichletSine hp hp1 m δ ψ
  terminal_root : ∀ ψ ∈ U, sourceAngularBranchCosineRoot hp hp1 m δ (ε ψ,ψ) =
    sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
  eta_analytic : AnalyticOnNhd ℂ (fun ψ => sourceAngularBranchEtaRepresentative hp hp1 m s δ (ε ψ,ψ)) U

namespace SourceAngularBranchCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {δ : CoeffPair p → ℂ}
  {W V : Set (CoeffPair p)} {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

theorem exists_local_analytic_eta_of_zero_sine
    (D : SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V)
    (hμ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ)
    (e : ℂ) (he : e ∈ Ω) (hsin : Complex.sin e = 0)
    (hpoint : sourceAngularBranchCosinePoint hp hp1 m δ (e,φ) =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m) :
    ∃ U : Set (CoeffPair p), ∃ ε : CoeffPair p → ℂ, φ ∈ U ∧ ε φ = e ∧
      SourceAngularBranchEtaTerminalData hp hp1 m s δ V U Ω ε := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m
  have hcos : Complex.cos e = (μ - τ) / δ φ := by
    apply (eq_div_iff (D.halfGap_ne_zero φ hφ)).mpr
    change τ + δ φ * Complex.cos e = μ at hpoint
    linear_combination hpoint
  have hcircle := sourceAngularBranchDirichletSine_sq_add_cosine_sq hp hp1 m δ φ
    (D.halfGap_ne_zero φ hφ) (D.halfGap_sq φ hφ)
    (((D.disc_family φ hφ).contour_family.2 m).2.2.1
      (ball_subset_closedBall ((D.disc_family φ hφ).dirichlet_mem_ball m)))
  have htrig := Complex.sin_sq_add_cos_sq e
  rw [hcos] at htrig
  have hsquare : sourceAngularBranchDirichletSine hp hp1 m δ φ ^ 2 = Complex.sin e ^ 2 := by
    linear_combination hcircle - htrig
  have hsine : Complex.sin e = sourceAngularBranchDirichletSine hp hp1 m δ φ := by
    have hzero : sourceAngularBranchDirichletSine hp hp1 m δ φ = 0 :=
      sq_eq_zero_iff.mp (by simpa only [hsin,zero_pow (by norm_num : 2 ≠ 0)] using hsquare)
    rw [hsin,hzero]
  obtain ⟨U,hU,hφU,hUV,ε,hε,hεφ,hcoords,hη⟩ :=
    D.exists_local_analytic_eta_at_terminal_angle φ hφ hμ e he hpoint hsine
  exact ⟨U,ε,hφU,hεφ,⟨hU,hUV,hε,(fun ψ hψ => (hcoords ψ hψ).1),
    (fun ψ hψ => (hcoords ψ hψ).2.1),(fun ψ hψ => (hcoords ψ hψ).2.2.1),
    (fun ψ hψ => (hcoords ψ hψ).2.2.2),hη⟩⟩

/-- Every complex endpoint terminal on an open half-gap chart has an
analytic actual eta source representative on a constructed neighborhood. -/
theorem exists_local_analytic_endpoint_eta
    (D : SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V)
    (hμ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ)
    (hend : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m ∈
      ({canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m - δ φ,
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m + δ φ} : Set ℂ)) :
    ∃ U : Set (CoeffPair p), ∃ ε : CoeffPair p → ℂ, φ ∈ U ∧
      (ε φ = 0 ∨ ε φ = (Real.pi : ℂ)) ∧ SourceAngularBranchEtaTerminalData hp hp1 m s δ V U Ω ε := by
  simp only [mem_insert_iff,mem_singleton_iff] at hend
  rcases hend with hl | hr
  · obtain ⟨U,ε,hφU,hεφ,hE⟩ := D.exists_local_analytic_eta_of_zero_sine φ hφ hμ
      (Real.pi : ℂ) (D.angle_segment (right_mem_segment ℝ _ _)) Complex.sin_pi
      (by simpa only [sourceAngularBranchCosinePoint,cosineGapPoint,Complex.cos_pi,mul_neg,
        mul_one,← sub_eq_add_neg] using hl.symm)
    exact ⟨U,ε,hφU,Or.inr hεφ,hE⟩
  · obtain ⟨U,ε,hφU,hεφ,hE⟩ := D.exists_local_analytic_eta_of_zero_sine φ hφ hμ
      0 (D.angle_segment (left_mem_segment ℝ _ _)) Complex.sin_zero
      (by simpa only [sourceAngularBranchCosinePoint,cosineGapPoint,Complex.cos_zero,mul_one] using hr.symm)
    exact ⟨U,ε,hφU,Or.inl hεφ,hE⟩

end SourceAngularBranchCosineChartData
end NLS.ZakharovShabat
