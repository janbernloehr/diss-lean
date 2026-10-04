import NLS.ZakharovShabat.SourceFloquetJointLog

/-! # The multiplier differential at complex sources

The quadratic identity for the canonical root gives the exact joint
multiplier differential on every open analytic root domain.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceFloquetJointMultiplier_hasFDerivAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W))
    (t : ℂ × CoeffPair p) (ht : t ∈ sourceCanonicalRootJointDomain hp hp1 W) :
    HasFDerivAt (sourceFloquetJointMultiplier hp hp1)
      ((sourceFloquetJointMultiplier hp hp1 t / sourceCanonicalRoot hp hp1 t.2 t.1) •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t := by
  let Δ : ℂ × CoeffPair p → ℂ := fun u => canonicalDiscriminant hp (periodOnePotential u.2) u.1
  let Q := sourceCanonicalRootJointProduct hp hp1
  let M := sourceFloquetJointMultiplier hp hp1
  have hΔ : DifferentiableAt ℂ Δ t :=
    (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 t (mem_univ t)).differentiableAt
  have hQ : DifferentiableAt ℂ Q t := (hroot t ht).differentiableAt
  have hM : HasFDerivAt M ((2:ℂ)⁻¹ • (fderiv ℂ Δ t + fderiv ℂ Q t)) t := by
    convert! (hΔ.hasFDerivAt.add hQ.hasFDerivAt).const_smul (2:ℂ)⁻¹ using 1
    funext u
    change (Δ u+Q u)/2 = (2:ℂ)⁻¹*(Δ u+Q u)
    rw [div_eq_inv_mul]
  have hqne : Q t ≠ 0 := sourceCanonicalRoot_ne_zero_off_gaps hp hp1 t.2 t.1 ht.2
  have hqder (v : ℂ × CoeffPair p) : (fderiv ℂ Q t) v = Δ t/Q t*(fderiv ℂ Δ t) v :=
    fderiv_squareRoot_of_sq_eq_discriminant_sq_sub_four Q Δ _ hD
      (fun u hu => sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 u.2 u.1 hu.2)
      t ht hQ hΔ hqne v
  have he : (M t/Q t) • fderiv ℂ Δ t = (2:ℂ)⁻¹ • (fderiv ℂ Δ t + fderiv ℂ Q t) := by
    apply ContinuousLinearMap.ext
    intro v
    change M t/Q t*(fderiv ℂ Δ t) v = (2:ℂ)⁻¹*((fderiv ℂ Δ t) v+(fderiv ℂ Q t) v)
    rw [hqder v]
    change ((Δ t+Q t)/2)/Q t*(fderiv ℂ Δ t) v = _
    field_simp
    ring
  rw [← he] at hM
  exact hM

/-- The spectral multiplier equation at arbitrary complex sources in W. -/
theorem sourceFloquetMultiplier_hasDerivAt_of_jointRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W))
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    HasDerivAt (sourceFloquetMultiplier hp hp1 ψ)
      (sourceFloquetMultiplier hp hp1 ψ z *
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z)) z := by
  have hjoint := sourceFloquetJointMultiplier_hasFDerivAt hp hp1 W hD hroot (z,ψ) ⟨hψ,hz⟩
  have hs : DifferentiableAt ℂ (sourceFloquetMultiplier hp hp1 ψ) z := by
    simpa only using! ((sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot (z,ψ) ⟨hψ,hz⟩).comp
      (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const)).differentiableAt
  convert! hs.hasDerivAt using 1
  change _ = deriv (fun w => sourceFloquetJointMultiplier hp hp1 (w,ψ)) z
  rw [deriv_spectral_section_eq_fderiv (sourceFloquetJointMultiplier hp hp1) z ψ hjoint.differentiableAt,
    hjoint.fderiv,deriv_spectral_section_eq_fderiv
      (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) z ψ
      (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [smul_apply,smul_eq_mul,sourceFloquetJointMultiplier]
  ring

end NLS.ZakharovShabat
