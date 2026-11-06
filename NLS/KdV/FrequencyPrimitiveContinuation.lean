import NLS.KdV.SquaredCoshDerivative
import NLS.KdV.ClassicalBranchPrimitive
import NLS.KdV.FrequencyMoments

/-! # Continuation of the actual Hill primitive quotient at branch points

For a primitive normalized by `2 cosh F = σ Δ`, its compatible root sheet is
`r = 2 σ sinh F`. The ratio `F/r` continues analytically as a function of the
constructed square `K=F²`, even at a multiple or collapsed branch point.
This uses the actual continuous-potential discriminant, rather than an
assumed analytic spectral function. Global gap and sheet normalization
remain separate from this local construction.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- An entire identity in the squared coordinate gives the exact local
factorization of the spectral radicand, without an analytic root choice. -/
theorem squaredCosh_radicand_factorization (K : ℂ) :
    (2*squaredCosh K)^2-4 = 16*K*(deriv squaredCosh K)^2 := by
  let z := Complex.sqrt K
  have hz : z^2 = K := by
    have h := Complex.cpow_nat_inv_pow K (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [z, Complex.sqrt, one_div] using h
  rw [← hz, squaredCosh_sq]
  have hD := deriv_squaredCosh_sq_mul z
  have hh := Complex.cosh_sq_sub_sinh_sq z
  linear_combination 4*hh - 4*(sinh z+deriv squaredCosh (z^2)*(2*z))*hD

/-- The local normalization of the primitive determines a square-root sheet
of the actual Hill radicand. -/
theorem classicalHill_primitive_sheet_sq
    (a : ℂ × NLS.LinearVolterra.Curve ℂ) (σ z : ℂ) (hσ : σ^2 = 1)
    (htrace : 2*cosh z = σ*classicalHillDiscriminant a.2 a.1) :
    (2*σ*sinh z)^2 = classicalHillRadicand a := by
  have hh := Complex.cosh_sq_sub_sinh_sq z
  dsimp only [classicalHillRadicand]
  linear_combination -4*hh +
    (2*cosh z+σ*classicalHillDiscriminant a.2 a.1)*htrace +
    (4*(sinh z)^2+(classicalHillDiscriminant a.2 a.1)^2)*(hσ)

/-- Division by the root is replaced by a nonvanishing analytic function
of the squared primitive. The nonzero-root hypothesis only identifies the
original quotient; the continued function also exists where that root vanishes. -/
theorem primitive_root_ratio_eq
    (σ z K r : ℂ) (hσ : σ^2 = 1) (hK : z^2 = K)
    (hr : r = 2*σ*sinh z) (hr0 : r ≠ 0)
    (hd : deriv squaredCosh K ≠ 0) :
    σ/(4*deriv squaredCosh K) = z/r := by
  apply (div_eq_div_iff (mul_ne_zero (by norm_num) hd) hr0).mpr
  have he : deriv squaredCosh K*(2*z) = sinh z := by
    simpa only [hK] using deriv_squaredCosh_sq_mul z
  calc
    σ*r = 2*(σ^2)*sinh z := by rw [hr]; ring
    _ = 2*sinh z := by rw [hσ]; ring
    _ = z*(4*deriv squaredCosh K) := by rw [← he]; ring

/-- At every periodic or antiperiodic point of the actual continuous Hill
discriminant, jointly analytic `K` and `H` continue `F²` and `F/r`. The
continued quotient has the exact endpoint value `σ/2`. No simplicity
hypothesis on the spectral zero is imposed. -/
theorem exists_classicalHill_primitive_ratio_continuation
    (p : ℂ × NLS.LinearVolterra.Curve ℂ) (σ : ℂ) (hσ : σ^2 = 1)
    (hbase : classicalHillDiscriminant p.2 p.1 = 2*σ) :
    ∃ V : Set (ℂ × NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧
        ∃ K H : ℂ × NLS.LinearVolterra.Curve ℂ → ℂ,
          AnalyticOnNhd ℂ K V ∧ AnalyticOnNhd ℂ H V ∧ K p = 0 ∧ H p = σ/2 ∧
          (∀ a ∈ V, H a ≠ 0 ∧ K a = (H a)^2*classicalHillRadicand a) ∧
          (∀ a ∈ V, K a ∈ U ∧
            squaredCosh (K a) = σ*classicalHillDiscriminant a.2 a.1/2) ∧
          ∀ a ∈ V, ∀ z r : ℂ, z^2 ∈ U →
            2*cosh z = σ*classicalHillDiscriminant a.2 a.1 →
            r = 2*σ*sinh z → r ≠ 0 → K a = z^2 ∧ H a = z/r := by
  obtain ⟨V, hV, hpV, U, hU, h0U, K, hK, hKp, htrace, hmatch⟩ :=
    exists_classicalHill_local_squared_primitive p σ hσ hbase
  let D := fun a => deriv squaredCosh (K a)
  have hD : AnalyticOnNhd ℂ D V := by
    intro a ha
    exact ((analyticOnNhd_squaredCosh (K a) (mem_univ _)).deriv).comp
      (f := K) (hK a ha)
  have hDp : D p = 1/2 := by
    dsimp only [D]
    rw [hKp, hasDerivAt_squaredCosh_zero.deriv]
  have hgood : ∀ᶠ a in 𝓝 p, a ∈ V ∧ D a ≠ 0 := by
    have hne : ∀ᶠ a in 𝓝 p, D a ≠ 0 :=
      (hD p hpV).continuousAt.eventually_ne (by rw [hDp]; norm_num)
    filter_upwards [hV.mem_nhds hpV, hne] with a ha hna
    exact ⟨ha, hna⟩
  obtain ⟨W, hsub, hW, hpW⟩ := _root_.mem_nhds_iff.mp hgood
  let H := fun a => σ/(4*D a)
  have hH : AnalyticOnNhd ℂ H W := by
    apply analyticOnNhd_const.div
      (analyticOnNhd_const.mul (hD.mono (fun a ha => (hsub ha).1)))
    intro a ha
    exact mul_ne_zero (by norm_num) (hsub ha).2
  refine ⟨W, hW, hpW, U, hU, h0U, K, H,
    hK.mono (fun a ha => (hsub ha).1), hH, hKp, ?_, ?_, ?_, ?_⟩
  · dsimp only [H]
    rw [hDp]
    ring
  · intro a ha
    have hσ0 : σ ≠ 0 := by
      intro hzero
      rw [hzero] at hσ
      norm_num at hσ
    refine ⟨div_ne_zero hσ0 (mul_ne_zero (by norm_num) (hsub ha).2), ?_⟩
    have hfac := squaredCosh_radicand_factorization (K a)
    rw [(htrace a (hsub ha).1).2] at hfac
    have hrad : classicalHillRadicand a = 16*K a*(D a)^2 := by
      dsimp only [classicalHillRadicand, D]
      linear_combination hfac - (classicalHillDiscriminant a.2 a.1)^2*hσ
    change K a = (σ/(4*D a))^2*classicalHillRadicand a
    rw [hrad, div_pow, hσ]
    field_simp [(hsub ha).2]
    ring
  · intro a ha
    exact htrace a (hsub ha).1
  intro a ha z r hz hcosh hr hr0
  have hKa : K a = z^2 := hmatch a (hsub ha).1 z hz hcosh
  exact ⟨hKa, primitive_root_ratio_eq σ z (K a) r hσ hKa.symm hr hr0 (hsub ha).2⟩

/-- The source endpoint limit `F/r → 1/Δ = σ/2` follows from continuity
of the constructed analytic continuation. In particular it does not use
l'Hôpital with a nonzero derivative of the discriminant. The relative
domain can omit all root zeros and may approach from either sheet. -/
theorem tendsto_classicalHill_primitive_ratio_at_branch
    (p : ℂ × NLS.LinearVolterra.Curve ℂ) (σ : ℂ) (hσ : σ^2 = 1)
    (hbase : classicalHillDiscriminant p.2 p.1 = 2*σ)
    (F r : ℂ × NLS.LinearVolterra.Curve ℂ → ℂ) (D : Set (ℂ × NLS.LinearVolterra.Curve ℂ))
    (hF : Tendsto F (𝓝[D] p) (𝓝 0))
    (hsheet : ∀ᶠ a in 𝓝[D] p,
      2*cosh (F a) = σ*classicalHillDiscriminant a.2 a.1 ∧
        r a = 2*σ*sinh (F a) ∧ r a ≠ 0) :
    Tendsto (fun a => F a/r a) (𝓝[D] p) (𝓝 (σ/2)) := by
  obtain ⟨V, hV, hpV, U, hU, h0U, K, H, _, hH, _, hHp, _, _, hmatch⟩ :=
    exists_classicalHill_primitive_ratio_continuation p σ hσ hbase
  have hsmall : ∀ᶠ a in 𝓝[D] p, (F a)^2 ∈ U := by
    have hsq : Tendsto (fun a => (F a)^2) (𝓝[D] p) (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0)] using hF.pow 2
    exact hsq (hU.mem_nhds h0U)
  have hlim : Tendsto H (𝓝[D] p) (𝓝 (σ/2)) := by
    rw [← hHp]
    exact (hH p hpV).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [nhdsWithin_le_nhds (hV.mem_nhds hpV), hsmall, hsheet] with a ha hsa hsh
  exact (hmatch a ha (F a) (r a) hsa hsh.1 hsh.2.1 hsh.2.2).2

/-- The continued primitive quotient is bounded uniformly on a joint
energy/potential neighborhood of a branch point, with the explicit bound one. -/
theorem exists_classicalHill_primitive_ratio_bound_chart
    (p : ℂ × NLS.LinearVolterra.Curve ℂ) (σ : ℂ) (hσ : σ^2 = 1)
    (hbase : classicalHillDiscriminant p.2 p.1 = 2*σ) :
    ∃ V : Set (ℂ × NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧
        ∀ a ∈ V, ∀ z r : ℂ, z^2 ∈ U →
          2*cosh z = σ*classicalHillDiscriminant a.2 a.1 →
          r = 2*σ*sinh z → r ≠ 0 → ‖z/r‖ ≤ 1 := by
  obtain ⟨V, hV, hpV, U, hU, h0U, K, H, _, hH, _, hHp, _, _, hmatch⟩ :=
    exists_classicalHill_primitive_ratio_continuation p σ hσ hbase
  have hnormσ : ‖σ‖ = 1 := by
    have he : ‖σ‖^2 = 1 := by rw [← norm_pow, hσ, norm_one]
    nlinarith [norm_nonneg σ]
  have hHplt : ‖H p‖ < 1 := by
    rw [hHp, norm_div, hnormσ]
    norm_num
  have hgood : ∀ᶠ a in 𝓝 p, a ∈ V ∧ ‖H a‖ < 1 := by
    have hne : ∀ᶠ a in 𝓝 p, ‖H a‖ < 1 :=
      ((hH p hpV).continuousAt.norm).eventually (gt_mem_nhds hHplt)
    filter_upwards [hV.mem_nhds hpV, hne] with a ha hna
    exact ⟨ha, hna⟩
  obtain ⟨W, hsub, hW, hpW⟩ := _root_.mem_nhds_iff.mp hgood
  refine ⟨W, hW, hpW, U, hU, h0U, ?_⟩
  intro a ha z r hz htrace hsheet hr0
  have he := (hmatch a (hsub ha).1 z r hz htrace hsheet hr0).2
  rw [← he]
  exact (hsub ha).2.le

/-- Uniform local estimates for every positive moment, obtained from the
actual continued quotient. The normalized numerator `ψ` only needs its
circle bound here. This avoids dividing a uniform estimate by a root that
vanishes when a gap collapses. -/
theorem exists_classicalHill_positive_moment_bound_chart
    (p : ℂ × NLS.LinearVolterra.Curve ℂ) (σ : ℂ) (hσ : σ^2 = 1)
    (hbase : classicalHillDiscriminant p.2 p.1 = 2*σ) :
    ∃ V : Set (ℂ × NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧
        ∀ (q : NLS.LinearVolterra.Curve ℂ) (c : ℂ) (R : ℝ), 0 ≤ R →
          (∀ z ∈ sphere c R, (z,q) ∈ V) →
          ∀ (F r ψ : ℂ → ℂ) (A B : ℝ), 0 ≤ A → 0 ≤ B →
            (∀ z ∈ sphere c R, ‖F z‖ ≤ A ∧ ‖ψ z‖ ≤ B ∧ (F z)^2 ∈ U ∧
              2*cosh (F z) = σ*classicalHillDiscriminant q z ∧
              r z = 2*σ*sinh (F z) ∧ r z ≠ 0) →
            ∀ m : ℕ, ‖frequencyMoment F (fun z => ψ z/r z) c R (m+1)‖ ≤
              2*Real.pi*R*(A^m*B) := by
  obtain ⟨V, hV, hpV, U, hU, h0U, hbound⟩ :=
    exists_classicalHill_primitive_ratio_bound_chart p σ hσ hbase
  refine ⟨V, hV, hpV, U, hU, h0U, ?_⟩
  intro q c R hR hchart F r ψ A B hA hB hcircle m
  apply circleIntegral.norm_integral_le_of_norm_le_const hR
  intro z hz
  obtain ⟨hF, hψ, hsmall, htrace, hsheet, hr0⟩ := hcircle z hz
  have hr := hbound (z,q) (hchart z hz) (F z) (r z) hsmall htrace hsheet hr0
  change ‖F z^(m+1)*(ψ z/r z)‖ ≤ A^m*B
  have he : F z^(m+1)*(ψ z/r z) = (F z)^m*((F z/r z)*ψ z) := by
    rw [pow_succ]
    ring
  rw [he, norm_mul, norm_pow, norm_mul]
  calc
    _ ≤ A^m*(1*B) := by gcongr
    _ = _ := by ring

/-- The local odd-moment cancellation now uses a chart constructed from the
actual discriminant. Analyticity of `F²` and `F*ψ/r` is proved rather than
assumed. Only the small-primitive and compatible-sheet identities on the
contour must be supplied by the global gap normalization. -/
theorem exists_classicalHill_odd_moment_chart
    (p : ℂ × NLS.LinearVolterra.Curve ℂ) (σ : ℂ) (hσ : σ^2 = 1)
    (hbase : classicalHillDiscriminant p.2 p.1 = 2*σ) :
    ∃ V : Set (ℂ × NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧
        ∀ (q : NLS.LinearVolterra.Curve ℂ) (c : ℂ) (R : ℝ), 0 ≤ R →
          (∀ z ∈ closedBall c R, (z,q) ∈ V) →
          ∀ F r ψ : ℂ → ℂ, AnalyticOnNhd ℂ ψ (closedBall c R) →
            (∀ z ∈ sphere c R, (F z)^2 ∈ U ∧
              2*cosh (F z) = σ*classicalHillDiscriminant q z ∧
              r z = 2*σ*sinh (F z) ∧ r z ≠ 0) →
            ∀ l : ℕ, frequencyMoment F (fun z => ψ z / r z) c R (2*l+1) = 0 := by
  obtain ⟨V, hV, hpV, U, hU, h0U, K, H, hK, hH, _, _, _, _, hmatch⟩ :=
    exists_classicalHill_primitive_ratio_continuation p σ hσ hbase
  refine ⟨V, hV, hpV, U, hU, h0U, ?_⟩
  intro q c R hR hdisk F r ψ hψ hcircle l
  have hk : AnalyticOnNhd ℂ (fun z => K (z,q)) (closedBall c R) := by
    intro z hz
    exact (hK (z,q) (hdisk z hz)).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hh : AnalyticOnNhd ℂ (fun z => H (z,q)) (closedBall c R) := by
    intro z hz
    exact (hH (z,q) (hdisk z hz)).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hi : AnalyticOnNhd ℂ (fun z => K (z,q)^l*(H (z,q)*ψ z)) (closedBall c R) :=
    (hk.pow l).mul (hh.mul hψ)
  unfold frequencyMoment
  calc
    _ = ∮ z in C(c,R), K (z,q)^l*(H (z,q)*ψ z) := by
      apply circleIntegral.integral_congr hR
      intro z hz
      obtain ⟨hsmall, htrace, hsheet, hr0⟩ := hcircle z hz
      obtain ⟨hKz, hHz⟩ := hmatch (z,q) (hdisk z (sphere_subset_closedBall hz))
        (F z) (r z) hsmall htrace hsheet hr0
      change F z^(2*l+1)*(ψ z/r z) = K (z,q)^l*(H (z,q)*ψ z)
      rw [hKz, hHz, pow_add, pow_mul, pow_one]
      ring
    _ = 0 := circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
      hi.continuousOn (fun z hz => (hi z (ball_subset_closedBall hz.1)).differentiableAt)

end NLS.KdV
