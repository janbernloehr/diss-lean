import NLS.ZakharovShabat.SourceAngularTerminalActionFlow

/-! # General actual isospectral terminal sheet flow

Stationarity of the fixed-source omitted product and the actual spectral
factorization give the full terminal sheet equations in any isospectral
direction with the stated actual root and moving anti-discriminant velocities.
No terminal square root or open-gap hypothesis is required.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- Derive the omitted-product and square equations from the actual
root and full moving anti-discriminant velocities in an isospectral direction. -/
theorem terminal_isospectral_flow
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) (v : ℂ)
    (hroot₀ : (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ.val) h =
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val*v)
    (hanti₀ : (fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val) h =
      let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
      canonicalDiscriminant hp (periodOnePotential φ.val) μ*
        deriv (canonicalDiscriminant hp (periodOnePotential φ.val)) μ*v) :
    let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
    let δ := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m
    let P : ℂ × CoeffPair p → ℂ := fun t => 2*I*sourceStandardRootOmittedJointProduct hp hp1 m t
    let K : CoeffPair p → ℂ := fun ψ => P (μ ψ,ψ)
    let K' := deriv (fun z => P (z,φ.val)) (μ φ.val)
    let M := sourceStandardRootMidpoint hp hp1 φ.val m
    let G := (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m)^2
    let Q := (μ φ.val-M)^2-G/4
    K φ.val ≠ 0 ∧ (fderiv ℂ μ φ.val) h = δ φ.val*v ∧
      (fderiv ℂ δ φ.val) h = (K φ.val*K'*Q+K φ.val^2*(μ φ.val-M))*v ∧
      (fderiv ℂ K φ.val) h = K'*δ φ.val*v ∧ δ φ.val^2 = K φ.val^2*Q := by
  dsimp only
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let δ := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m
  let P : ℂ × CoeffPair p → ℂ := fun t => 2*I*sourceStandardRootOmittedJointProduct hp hp1 m t
  let K : CoeffPair p → ℂ := fun ψ => P (μ ψ,ψ)
  let K' := deriv (fun z => P (z,φ.val)) (μ φ.val)
  let M := sourceStandardRootMidpoint hp hp1 φ.val m
  let G := (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m)^2
  let Q := (μ φ.val-M)^2-G/4
  have hμ : DifferentiableAt ℂ μ φ.val :=
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m).differentiableAt
  have hterminalT : μ φ.val ∈ ball (c m) (T m) :=
    (D.disc_family φ.val hφ).dirichlet_mem_ball m
  have hother : μ φ.val ∈ sourceStandardRootOmittedDomain hp hp1 φ.val m :=
    ((D.disc_family φ.val hφ).contour_family.2 m).2.2.1 (ball_subset_closedBall hterminalT)
  have hKne : K φ.val ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 φ.val (μ φ.val) m hother)
  have hPjoint : DifferentiableAt ℂ P (μ φ.val,φ.val) :=
    (analyticAt_const.mul (D.omitted_analytic (μ φ.val,φ.val) ⟨hterminalT,hφ⟩)).differentiableAt
  have hroot := hroot₀
  change (fderiv ℂ μ φ.val) h = δ φ.val*v at hroot
  have hanti := hanti₀
  dsimp only at hanti
  have hf := D.discriminant_mul_deriv_eq_omittedProduct φ.val hφ (μ φ.val) hterminalT
  change canonicalDiscriminant hp (periodOnePotential φ.val) (μ φ.val)*
      deriv (canonicalDiscriminant hp (periodOnePotential φ.val)) (μ φ.val) =
    K φ.val*K'*Q+K φ.val^2*(μ φ.val-M) at hf
  rw [hf] at hanti
  change (fderiv ℂ δ φ.val) h = (K φ.val*K'*Q+K φ.val^2*(μ φ.val-M))*v at hanti
  have hPsource : (fderiv ℂ (fun ψ => P (μ φ.val,ψ)) φ.val) h = 0 := by
    have ho := ((D.omitted_analytic (μ φ.val,φ.val) ⟨hterminalT,hφ⟩).comp
      (f := fun ψ : CoeffPair p => (μ φ.val,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
    change DifferentiableAt ℂ (fun ψ : CoeffPair p => sourceStandardRootOmittedProduct hp hp1 m ψ (μ φ.val)) φ.val at ho
    change (fderiv ℂ (fun ψ : CoeffPair p => 2*I*sourceStandardRootOmittedProduct hp hp1 m ψ (μ φ.val)) φ.val) h = 0
    rw [(ho.hasFDerivAt.const_mul (2*I)).fderiv]
    simp only [smul_apply,smul_eq_mul,
      fderiv_sourceStandardRootOmittedProduct_isospectral_eq_zero hp hp1 φ.val φ.property h hiso m (μ φ.val) hother,mul_zero]
  have hKflow : (fderiv ℂ K φ.val) h = K'*δ φ.val*v := by
    rw [fderiv_moving_spectral_parameter P μ φ.val hPjoint hμ]
    simp only [add_apply,smul_apply,smul_eq_mul,hPsource,zero_add,hroot]
    ring
  have hsq : δ φ.val^2 = K φ.val^2*Q := by
    dsimp only [δ,sourceBoundaryTerminalAntiDiscriminant,K,P,sourceStandardRootOmittedJointProduct,Q,M,G,μ,sourceStandardRootMidpoint]
    rw [← sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 φ.val m,
      canonicalDiscriminant_sq_sub_four_eq_midpoint_mul hp hp1 _ (periodOnePotential_mem φ.val) m,
      ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 φ.val m _ hother]
    simp only [mul_pow,I_sq]
    ring
  exact ⟨hKne,hroot,hanti,hKflow,hsq⟩


end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
