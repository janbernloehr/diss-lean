import NLS.ZakharovShabat.ResolventContour

/-!
# Idempotence of resolvent contour operators

Nested-circle integration and the resolvent identity yield the projection law.
Radius deformation then applies to every circle lying in the resolvent set.
-/

open scoped ENNReal
open Complex Metric Set Classical
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A resolvent circle has a slightly larger closed annulus contained in the
resolvent set. Local finiteness of the spectrum supplies a positive radial gap. -/
theorem exists_resolvent_annulus (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hc : sphere c r ⊆ resolventSet hp φ) :
    ∃ R : ℝ, r < R ∧ closedBall c R \ ball c r ⊆ resolventSet hp φ := by
  let K := periodicSpectrum hp φ ∩ closedBall c (r + 1)
  have hK : K.Finite := finite_periodicSpectrum_inter_of_isBounded hp φ isBounded_closedBall
  have hn : r ∉ (fun z : ℂ => dist z c) '' K := by
    rintro ⟨z, hz, hzr⟩
    exact hz.1 (hc (mem_sphere.mpr hzr))
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp
    (((hK.image (fun z : ℂ => dist z c)).isClosed.isOpen_compl).mem_nhds hn)
  let δ := min ε 1 / 2
  have hδ : 0 < δ := half_pos (lt_min hε (by norm_num))
  have hδε : δ < ε := (half_lt_self (lt_min hε (by norm_num))).trans_le (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith [min_le_right ε (1 : ℝ)]
  refine ⟨r + δ, by linarith, ?_⟩
  intro z hz
  by_contra hzr
  have hdlo : r ≤ dist z c := not_lt.mp hz.2
  have hdhi : dist z c ≤ r + δ := mem_closedBall.mp hz.1
  have hzK : z ∈ K := ⟨hzr, mem_closedBall.mpr (by linarith)⟩
  have hdist : dist z c ∈ ball r ε := by
    rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hdlo)]
    linarith
  exact (hεs hdist) ⟨z, hzK, rfl⟩

private theorem integral_inv_sub_zero (c w : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hw : w ∉ closedBall c r) : (∮ z in C(c, r), (z - w)⁻¹) = 0 := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => (z - w)⁻¹) (closedBall c r) := by
    intro z hz
    exact ((differentiableAt_id.sub_const w).inv
      (sub_ne_zero.mpr (fun h => hw (h ▸ hz)))).differentiableWithinAt
  exact (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn).circleIntegral_eq_zero hr

/-- Integrating the resolvent identity against an outer resolvent removes its
constant term on the inner circle. -/
private theorem integral_mul_resolvent_outer (hp : p ≠ ⊤) (φ : PairSpace p)
    (c w : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ)
    (hw : w ∈ resolventSet hp φ) (hwo : w ∉ closedBall c r) :
    (∮ z in C(c, r), resolvent hp φ z * resolvent hp φ w) =
      ∮ z in C(c, r), (w - z)⁻¹ • resolvent hp φ z := by
  have hne (z : ℂ) (hz : z ∈ sphere c r) : w ≠ z :=
    fun h => hwo (h ▸ sphere_subset_closedBall hz)
  have hinv : ContinuousOn (fun z : ℂ => (w - z)⁻¹) (sphere c r) :=
    (continuousOn_const.sub continuousOn_id).inv₀ fun z hz => by
      change w - z ≠ 0
      exact sub_ne_zero.mpr (hne z hz)
  have h₁ : CircleIntegrable (fun z => (w - z)⁻¹ • resolvent hp φ z) c r :=
    (hinv.smul ((analyticOnNhd_resolvent hp φ).continuousOn.mono hc)).circleIntegrable hr
  have h₂ : CircleIntegrable (fun z => (w - z)⁻¹ • resolvent hp φ w) c r :=
    (hinv.smul continuousOn_const).circleIntegrable hr
  have heq : (∮ z in C(c, r), resolvent hp φ z * resolvent hp φ w) =
      ∮ z in C(c, r), (w - z)⁻¹ • resolvent hp φ z - (w - z)⁻¹ • resolvent hp φ w := by
    apply circleIntegral.integral_congr hr
    intro z hz
    dsimp only
    calc
      _ = (w - z)⁻¹ • ((w - z) • (resolvent hp φ z * resolvent hp φ w)) :=
        (inv_smul_smul₀ (sub_ne_zero.mpr (hne z hz)) _).symm
      _ = (w - z)⁻¹ • (resolvent hp φ z - resolvent hp φ w) :=
        congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => (w - z)⁻¹ • A)
          (resolvent_identity hp φ z w (hc hz) hw).symm
      _ = _ := smul_sub _ _ _
  have hi0 : (∮ z in C(c, r), (w - z)⁻¹) = 0 := by
    have he : (fun z : ℂ => (w - z)⁻¹) = fun z => (-1 : ℂ) • (z - w)⁻¹ := by
      funext z
      rw [show w - z = -(z - w) by abel, inv_neg, neg_one_smul]
    rw [he, circleIntegral.integral_smul, integral_inv_sub_zero c w r hr hwo, smul_zero]
  rw [heq, circleIntegral.integral_sub h₁ h₂, circleIntegral.integral_smul_const,
    hi0, zero_smul, sub_zero]

/-- The product of normalized resolvent integrals over two nested circles is
the inner contour operator. No condition on the intervening annulus is needed. -/
theorem resolventCircleIntegral_mul_nested (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ)
    (r R : ℝ) (hr : 0 ≤ r) (hrR : r < R)
    (hc : sphere c r ⊆ resolventSet hp φ) (hC : sphere c R ⊆ resolventSet hp φ) :
    resolventCircleIntegral hp φ c r * resolventCircleIntegral hp φ c R =
      resolventCircleIntegral hp φ c r := by
  have hR : 0 ≤ R := hr.trans hrR.le
  let S := resolvent hp φ
  let Ir := ∮ z in C(c, r), S z
  let IR := ∮ w in C(c, R), S w
  have hir : CircleIntegrable S c r := circleIntegrable_resolvent hp φ c r hr hc
  have hiR : CircleIntegrable S c R := circleIntegrable_resolvent hp φ c R hR hC
  have hneq (t : ℂ × ℂ) (ht : t ∈ sphere c r ×ˢ sphere c R) : t.2 ≠ t.1 := by
    intro h
    have he : r = R := (mem_sphere.mp ht.1).symm.trans
      ((congrArg (fun z => dist z c) h.symm).trans (mem_sphere.mp ht.2))
    exact (ne_of_lt hrR) he
  have hM : ContinuousOn (fun t : ℂ × ℂ => (t.2 - t.1)⁻¹ • S t.1)
      (sphere c r ×ˢ sphere c R) := by
    have hinvc : ContinuousOn (fun t : ℂ × ℂ => (t.2 - t.1)⁻¹)
        (sphere c r ×ˢ sphere c R) :=
      (continuousOn_snd.sub continuousOn_fst).inv₀
        (fun t ht => sub_ne_zero.mpr (hneq t ht))
    exact hinvc.smul (((analyticOnNhd_resolvent hp φ).continuousOn.mono hc).comp
      continuousOn_fst (fun _ h => h.1))
  have hraw : Ir * IR = (2 * Real.pi * I : ℂ) • Ir := by
    calc
      Ir * IR = ∮ w in C(c, R), Ir * S w :=
        NLS.CircleIntegral.map (ContinuousLinearMap.mul ℂ _ Ir) hiR
      _ = ∮ w in C(c, R), ∮ z in C(c, r), S z * S w := by
        apply circleIntegral.integral_congr hR
        intro w _
        exact NLS.CircleIntegral.map ((ContinuousLinearMap.mul ℂ _).flip (S w)) hir
      _ = ∮ w in C(c, R), ∮ z in C(c, r), (w - z)⁻¹ • S z := by
        apply circleIntegral.integral_congr hR
        intro w hw
        apply integral_mul_resolvent_outer hp φ c w r hr hc (hC hw)
        intro hwr
        have hdist := mem_closedBall.mp hwr
        rw [mem_sphere.mp hw] at hdist
        exact hrR.not_ge hdist
      _ = ∮ z in C(c, r), ∮ w in C(c, R), (w - z)⁻¹ • S z :=
        (NLS.CircleIntegral.swap hr hR hM).symm
      _ = ∮ z in C(c, r), (2 * Real.pi * I : ℂ) • S z := by
        apply circleIntegral.integral_congr hr
        intro z hz
        dsimp only
        rw [circleIntegral.integral_smul_const,
          circleIntegral.integral_sub_inv_of_mem_ball
            (show z ∈ ball c R from mem_ball.mpr ((mem_sphere.mp hz).trans_lt hrR))]
      _ = _ := circleIntegral.integral_smul _ _ _ _
  change ((2 * Real.pi * I : ℂ)⁻¹ • Ir) * ((2 * Real.pi * I : ℂ)⁻¹ • IR) =
    (2 * Real.pi * I : ℂ)⁻¹ • Ir
  rw [smul_mul_assoc, mul_smul_comm, hraw]
  simp [smul_smul, mul_assoc, Real.pi_ne_zero]

/-- Every resolvent circle defines an idempotent operator. -/
theorem resolventCircleIntegral_idempotent (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    IsIdempotentElem (resolventCircleIntegral hp φ c r) := by
  rcases hr.eq_or_lt with hzero | hpos
  · have hr0 : r = 0 := hzero.symm
    subst r
    simp [resolventCircleIntegral, circleIntegral.integral_radius_zero, IsIdempotentElem]
  · obtain ⟨R, hrR, ha⟩ := exists_resolvent_annulus hp φ c r hc
    have hC : sphere c R ⊆ resolventSet hp φ := by
      intro z hz
      apply ha
      refine ⟨sphere_subset_closedBall hz, ?_⟩
      intro hzr
      have hd : dist z c < r := mem_ball.mp hzr
      rw [mem_sphere.mp hz] at hd
      exact hrR.not_ge hd.le
    have heq := resolventCircleIntegral_eq_of_annulus_subset hp φ c r R hpos hrR.le ha
    have hmul := resolventCircleIntegral_mul_nested hp φ c r R hr hrR hc hC
    rwa [heq] at hmul

/-- Compactness and idempotence force the contour operator to have finite rank. -/
theorem finiteDimensional_range_resolventCircleIntegral (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    FiniteDimensional ℂ (resolventCircleIntegral hp φ c r).range := by
  let P := resolventCircleIntegral hp φ c r
  have hid := resolventCircleIntegral_idempotent hp φ c r hr hc
  have heq : P.range = Module.End.eigenspace P.toLinearMap 1 := by
    ext x
    rw [Module.End.mem_eigenspace_iff]
    change (∃ y, P y = x) ↔ P x = (1 : ℂ) • x
    rw [one_smul]
    constructor
    · rintro ⟨y, rfl⟩
      exact DFunLike.congr_fun hid y
    · intro hx
      exact ⟨x, hx⟩
  change FiniteDimensional ℂ P.range
  rw [heq]
  exact NLS.CompactSpectrum.finiteDimensional_eigenspace P
    (isCompactOperator_resolventCircleIntegral hp φ c r hr hc) one_ne_zero

/-- The range and kernel of the contour projection form a topological direct sum. -/
theorem isTopCompl_range_ker_resolventCircleIntegral (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    Submodule.IsTopCompl (resolventCircleIntegral hp φ c r).range
      (resolventCircleIntegral hp φ c r).ker :=
  ContinuousLinearMap.IsIdempotentElem.isTopCompl
    (resolventCircleIntegral_idempotent hp φ c r hr hc)

end NLS.ZakharovShabat
