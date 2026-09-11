import NLS.ZakharovShabat.SpectralClusters
import NLS.FunctionalAnalysis.CircleIntegral

/-!
# Circle integrals of the periodic resolvent

The normalized operator-norm circle integral used in Section 3, equation (1.4),
with positively oriented circles and the convention `R(ζ) = (ζ - L)⁻¹`.
The definition is total; its analytic interpretation requires the integration
circle to lie in the resolvent set.
-/

open scoped ENNReal
open Complex Metric Classical
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized, operator-valued Cauchy integral of the full resolvent. -/
def resolventCircleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) :
    PairSpace p →L[ℂ] PairSpace p :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, r), resolvent hp φ z

/-- The same contour integral valued in the one-derivative operator domain. -/
def resolventCircleIntegralToDomain (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) :
    PairSpace p →L[ℂ] Domain p :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, r), resolventToDomain hp φ z

/-- The resolvent is circle integrable on any nonnegative-radius resolvent circle. -/
theorem circleIntegrable_resolvent (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    CircleIntegrable (resolvent hp φ) c r :=
  ((analyticOnNhd_resolvent hp φ).continuousOn.mono hc).circleIntegrable hr

private theorem continuousOn_resolventToDomain_circle (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hc : sphere c r ⊆ resolventSet hp φ) :
    ContinuousOn (resolventToDomain hp φ) (sphere c r) := by
  intro z hz
  exact ((analyticAt_resolventToDomain hp (φ, z) (hc hz)).comp
    (analyticAt_const.prod analyticAt_id)).continuousAt.continuousWithinAt

/-- The domain-valued resolvent is circle integrable on a resolvent circle. -/
theorem circleIntegrable_resolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    CircleIntegrable (resolventToDomain hp φ) c r :=
  (continuousOn_resolventToDomain_circle hp φ c r hc).circleIntegrable hr

/-- Evaluation of the operator integral is the integral of the evaluated resolvent. -/
theorem resolventCircleIntegral_apply (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) (x : PairSpace p) :
    resolventCircleIntegral hp φ c r x =
      (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, r), resolvent hp φ z x := by
  rw [resolventCircleIntegral, smul_apply,
    NLS.CircleIntegral.apply (circleIntegrable_resolvent hp φ c r hr hc) x]

/-- The contour operator factors through the one-derivative domain. -/
theorem resolventCircleIntegral_eq_inclusion (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    resolventCircleIntegral hp φ c r =
      domainInclusion.comp (resolventCircleIntegralToDomain hp φ c r) := by
  apply ContinuousLinearMap.ext
  intro x
  have hi : CircleIntegrable (fun z => resolventToDomain hp φ z x) c r :=
    ((continuousOn_resolventToDomain_circle hp φ c r hc).clm_apply
      continuousOn_const).circleIntegrable hr
  rw [resolventCircleIntegral_apply hp φ c r hr hc]
  change _ = domainInclusion ((resolventCircleIntegralToDomain hp φ c r) x)
  rw [resolventCircleIntegralToDomain, smul_apply,
    NLS.CircleIntegral.apply (circleIntegrable_resolventToDomain hp φ c r hr hc),
    map_smul, NLS.CircleIntegral.map domainInclusion hi]
  rfl

/-- The contour integral is compact, via its domain-valued factorization. -/
theorem isCompactOperator_resolventCircleIntegral (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    IsCompactOperator (resolventCircleIntegral hp φ c r) := by
  have hI : I ∉ freeLattice := notMem_freeLattice_of_im_ne_zero (by simp)
  have heq : (freeResolvent (p := p) I hI).comp (freePencil I) = domainInclusion := by
    apply ContinuousLinearMap.ext
    intro f
    change domainInclusion (freeResolventToDomain I hI (freePencil I f)) = domainInclusion f
    rw [freeResolventToDomain_freePencil]
  rw [resolventCircleIntegral_eq_inclusion hp φ c r hr hc, ← heq, ContinuousLinearMap.comp_assoc]
  exact (isCompactOperator_freeResolvent (p := p) I hI).comp_clm _

/-- A uniform resolvent bound on the circle bounds the normalized integral. -/
theorem norm_resolventCircleIntegral_le (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r M : ℝ)
    (hr : 0 ≤ r) (hM : ∀ z ∈ sphere c r, ‖resolvent hp φ z‖ ≤ M) :
    ‖resolventCircleIntegral hp φ c r‖ ≤ r * M :=
  circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr hM

/-- A disk contained in the resolvent set contributes zero by Cauchy's theorem. -/
theorem resolventCircleIntegral_eq_zero_of_closedBall_subset (hp : p ≠ ⊤)
    (φ : PairSpace p) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : closedBall c r ⊆ resolventSet hp φ) : resolventCircleIntegral hp φ c r = 0 := by
  have hd := (analyticOnNhd_resolvent hp φ).differentiableOn.mono hc
  have hdiff : DiffContOnCl ℂ (resolvent hp φ) (ball c r) :=
    DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn
  rw [resolventCircleIntegral, hdiff.circleIntegral_eq_zero hr, smul_zero]

/-- Changing the circle radius through a closed annulus of resolvent points
does not change the contour operator. -/
theorem resolventCircleIntegral_eq_of_annulus_subset (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (ha : closedBall c R \ ball c r ⊆ resolventSet hp φ) :
    resolventCircleIntegral hp φ c R = resolventCircleIntegral hp φ c r := by
  have heq := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    Set.countable_empty ((analyticOnNhd_resolvent hp φ).continuousOn.mono ha)
    (fun z hz => (analyticOnNhd_resolvent hp φ z (ha
      ⟨ball_subset_closedBall hz.1.1, fun h => hz.1.2 (ball_subset_closedBall h)⟩)).differentiableAt)
  exact congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => (2 * Real.pi * I : ℂ)⁻¹ • A) heq

/-- The resolvent recurrence along one step of a root chain. -/
theorem resolvent_apply_root_step (hp : p ≠ ⊤) (φ : PairSpace p) (ζ z : ℂ)
    (hζ : ζ ∈ resolventSet hp φ) (hζz : ζ ≠ z) (f : Domain p) :
    resolvent hp φ ζ (domainInclusion f) =
      (ζ - z)⁻¹ • domainInclusion f - (ζ - z)⁻¹ • resolvent hp φ ζ (spectralPencil hp φ z f) := by
  have hinv : resolvent hp φ ζ (spectralPencil hp φ ζ f) = domainInclusion f :=
    congrArg domainInclusion (resolventToDomain_spectralPencil hp φ ζ hζ f)
  have heq : spectralPencil hp φ ζ f =
      spectralPencil hp φ z f + (ζ - z) • domainInclusion f := by
    simp only [spectralPencil_apply]
    module
  rw [heq, map_add, map_smul] at hinv
  have h : (ζ - z) • resolvent hp φ ζ (domainInclusion f) =
      domainInclusion f - resolvent hp φ ζ (spectralPencil hp φ z f) := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hinv
  calc
    _ = (ζ - z)⁻¹ • ((ζ - z) • resolvent hp φ ζ (domainInclusion f)) :=
      (inv_smul_smul₀ (sub_ne_zero.mpr hζz) _).symm
    _ = _ := by rw [h, smul_sub]

/-- On an ordinary eigenvector the full resolvent has its scalar simple-pole formula. -/
theorem resolvent_apply_eigenvector (hp : p ≠ ⊤) (φ : PairSpace p) (ζ z : ℂ)
    (hζ : ζ ∈ resolventSet hp φ) (hζz : ζ ≠ z) (f : Domain p)
    (hf : f ∈ periodicEigenspace hp φ z) :
    resolvent hp φ ζ (domainInclusion f) = (ζ - z)⁻¹ • domainInclusion f := by
  have hf0 : spectralPencil hp φ z f = 0 := hf
  rw [resolvent_apply_root_step hp φ ζ z hζ hζz, hf0, map_zero, smul_zero, sub_zero]

/-- A circle enclosing an eigenvalue fixes its included eigenvectors. -/
theorem resolventCircleIntegral_apply_eigenvector (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hc : sphere c r ⊆ resolventSet hp φ)
    (hz : z ∈ ball c r) (f : Domain p) (hf : f ∈ periodicEigenspace hp φ z) :
    resolventCircleIntegral hp φ c r (domainInclusion f) = domainInclusion f := by
  have hr : 0 ≤ r := (pos_of_mem_ball hz).le
  rw [resolventCircleIntegral_apply hp φ c r hr hc]
  have heq : (∮ ζ in C(c, r), resolvent hp φ ζ (domainInclusion f)) =
      ∮ ζ in C(c, r), (ζ - z)⁻¹ • domainInclusion f := by
    apply circleIntegral.integral_congr hr
    intro ζ hζ
    apply resolvent_apply_eigenvector hp φ ζ z (hc hζ) _ f hf
    exact fun h => (sphere_disjoint_ball.le_bot ⟨hζ, h ▸ hz⟩)
  rw [heq, circleIntegral.integral_smul_const, circleIntegral.integral_sub_inv_of_mem_ball hz]
  exact inv_smul_smul₀ (by simp [Real.pi_ne_zero]) _

private theorem integral_inv_pow_succ (c z : ℂ) (r : ℝ) (k : ℕ) :
    (∮ ζ in C(c, r), (ζ - z)⁻¹ ^ (k + 1)) =
      if k = 0 then (∮ ζ in C(c, r), (ζ - z)⁻¹) else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk]
    have heq : (fun ζ : ℂ => (ζ - z)⁻¹ ^ (k + 1)) =
        (fun ζ : ℂ => (ζ - z) ^ (-((k : ℤ) + 1))) := by
      funext ζ
      rw [show -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ) by simp only [Nat.cast_add, Nat.cast_one]]
      simp only [zpow_neg, zpow_natCast, inv_pow]
    rw [heq]
    exact circleIntegral.integral_sub_zpow_of_ne (by omega) c z r

private theorem continuousOn_inv_sub (c z : ℂ) (r : ℝ) (hz : z ∉ sphere c r) :
    ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹) (sphere c r) :=
  (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => by
    change ζ - z ≠ 0
    exact sub_ne_zero.mpr (fun h => hz (h ▸ hζ))

/-- Weighted contour integrals along a finite root chain. Higher pole terms
vanish; the simple-pole integral is the only contribution. -/
theorem circleIntegral_resolvent_root (hp : p ≠ ⊤) (φ : PairSpace p) (c z : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) (hz : z ∉ sphere c r)
    (n : ℕ) (x : PairSpace p) (hx : x ∈ periodicRootSpace hp φ z n) (k : ℕ) :
    (∮ ζ in C(c, r), (ζ - z)⁻¹ ^ k • resolvent hp φ ζ x) =
      if k = 0 then (∮ ζ in C(c, r), (ζ - z)⁻¹) • x else 0 := by
  induction n generalizing x k with
  | zero =>
    have hx0 : x = 0 := hx
    subst x
    simp [circleIntegral]
  | succ n ih =>
    obtain ⟨f, rfl, hf⟩ := (mem_periodicRootSpace_succ hp φ z n x).mp hx
    have hcont := continuousOn_inv_sub c z r hz
    have hR (y : PairSpace p) : ContinuousOn (fun ζ => resolvent hp φ ζ y) (sphere c r) :=
      ((analyticOnNhd_resolvent hp φ).continuousOn.mono hc).clm_apply continuousOn_const
    have heq : (∮ ζ in C(c, r), (ζ - z)⁻¹ ^ k • resolvent hp φ ζ (domainInclusion f)) =
        ∮ ζ in C(c, r), (ζ - z)⁻¹ ^ (k + 1) • domainInclusion f -
          (ζ - z)⁻¹ ^ (k + 1) • resolvent hp φ ζ (spectralPencil hp φ z f) := by
      apply circleIntegral.integral_congr hr
      intro ζ hζ
      dsimp only
      rw [resolvent_apply_root_step hp φ ζ z (hc hζ)
        (fun h => hz (h ▸ hζ)), smul_sub, smul_smul, smul_smul, ← pow_succ]
    have hi1 : CircleIntegrable (fun ζ => (ζ - z)⁻¹ ^ (k + 1) • domainInclusion f) c r :=
      ((hcont.pow (k + 1)).smul continuousOn_const).circleIntegrable hr
    have hi2 : CircleIntegrable (fun ζ => (ζ - z)⁻¹ ^ (k + 1) •
        resolvent hp φ ζ (spectralPencil hp φ z f)) c r :=
      ((hcont.pow (k + 1)).smul (hR _)).circleIntegrable hr
    rw [heq, circleIntegral.integral_sub hi1 hi2,
      ih _ hf (k + 1), if_neg (Nat.succ_ne_zero k), sub_zero,
      circleIntegral.integral_smul_const, integral_inv_pow_succ]
    split_ifs <;> simp

/-- A circle enclosing a spectral value fixes every vector in its full root space. -/
theorem resolventCircleIntegral_apply_root (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hc : sphere c r ⊆ resolventSet hp φ)
    (hz : z ∈ ball c r) (x : PairSpace p) (hx : x ∈ periodicRootSpaceTop hp φ z) :
    resolventCircleIntegral hp φ c r x = x := by
  have hr : 0 ≤ r := (pos_of_mem_ball hz).le
  have hzs : z ∉ sphere c r := fun h => sphere_disjoint_ball.le_bot ⟨h, hz⟩
  obtain ⟨n, hn⟩ := (mem_periodicRootSpaceTop hp φ z x).mp hx
  have h := circleIntegral_resolvent_root hp φ c z r hr hc hzs n x hn 0
  simp only [pow_zero, one_smul] at h
  rw [resolventCircleIntegral_apply hp φ c r hr hc, h,
    circleIntegral.integral_sub_inv_of_mem_ball hz]
  exact inv_smul_smul₀ (by simp [Real.pi_ne_zero]) _

/-- A circle annihilates root vectors whose spectral value lies outside the closed disk. -/
theorem resolventCircleIntegral_apply_other_root (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ)
    (hz : z ∉ closedBall c r) (x : PairSpace p) (hx : x ∈ periodicRootSpaceTop hp φ z) :
    resolventCircleIntegral hp φ c r x = 0 := by
  have hzs : z ∉ sphere c r := fun h => hz (sphere_subset_closedBall h)
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => (ζ - z)⁻¹) (closedBall c r) := by
    intro ζ hζ
    exact ((differentiableAt_id.sub_const z).inv
      (sub_ne_zero.mpr (fun h => hz (h ▸ hζ)))).differentiableWithinAt
  have hzero := (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall)
    hd.continuousOn).circleIntegral_eq_zero hr
  obtain ⟨n, hn⟩ := (mem_periodicRootSpaceTop hp φ z x).mp hx
  have h := circleIntegral_resolvent_root hp φ c z r hr hc hzs n x hn 0
  simp only [pow_zero, one_smul] at h
  rw [resolventCircleIntegral_apply hp φ c r hr hc, h, hzero]
  simp

/-- Any bounded operator commuting with the resolvents along a circle commutes
with their normalized contour integral. -/
theorem commute_resolventCircleIntegral (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ)
    (A : PairSpace p →L[ℂ] PairSpace p)
    (hA : ∀ ζ ∈ sphere c r, Commute A (resolvent hp φ ζ)) :
    Commute A (resolventCircleIntegral hp φ c r) := by
  apply ContinuousLinearMap.ext
  intro x
  change A (resolventCircleIntegral hp φ c r x) = resolventCircleIntegral hp φ c r (A x)
  have hi : CircleIntegrable (fun ζ => resolvent hp φ ζ x) c r :=
    (((analyticOnNhd_resolvent hp φ).continuousOn.mono hc).clm_apply
      continuousOn_const).circleIntegrable hr
  rw [resolventCircleIntegral_apply hp φ c r hr hc,
    resolventCircleIntegral_apply hp φ c r hr hc, map_smul, NLS.CircleIntegral.map A hi]
  congr 1
  apply circleIntegral.integral_congr hr
  intro ζ hζ
  exact DFunLike.congr_fun (hA ζ hζ).eq x

/-- The contour integral commutes with every full resolvent. -/
theorem resolventCircleIntegral_commute_resolvent (hp : p ≠ ⊤) (φ : PairSpace p)
    (c w : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ)
    (hw : w ∈ resolventSet hp φ) :
    Commute (resolventCircleIntegral hp φ c r) (resolvent hp φ w) :=
  (commute_resolventCircleIntegral hp φ c r hr hc _
    (fun ζ hζ => resolvent_commute hp φ w ζ hw (hc hζ))).symm

/-- Algebraic spectral projections commute with the contour integral. -/
theorem periodicSpectralProjection_commute_contour (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    Commute (periodicSpectralProjection hp φ z) (resolventCircleIntegral hp φ c r) :=
  commute_resolventCircleIntegral hp φ c r hr hc _
    (fun ζ hζ => periodicSpectralProjection_commute_resolvent hp φ z ζ (hc hζ))

/-- The contour integral restricts to the identity on each enclosed root-space projection. -/
theorem resolventCircleIntegral_mul_projection (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hc : sphere c r ⊆ resolventSet hp φ) (hz : z ∈ ball c r) :
    resolventCircleIntegral hp φ c r * periodicSpectralProjection hp φ z =
      periodicSpectralProjection hp φ z := by
  apply ContinuousLinearMap.ext
  intro x
  apply resolventCircleIntegral_apply_root hp φ c z r hc hz
  rw [← range_periodicSpectralProjection hp φ z]
  exact LinearMap.mem_range_self _ x

/-- The contour integral annihilates each excluded root-space projection. -/
theorem resolventCircleIntegral_mul_projection_eq_zero (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ)
    (hz : z ∉ closedBall c r) :
    resolventCircleIntegral hp φ c r * periodicSpectralProjection hp φ z = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply resolventCircleIntegral_apply_other_root hp φ c z r hr hc hz
  rw [← range_periodicSpectralProjection hp φ z]
  exact LinearMap.mem_range_self _ x

/-- Composing with a root-space projection selects exactly the parameters inside
the circle. Boundary parameters are resolvent points and contribute zero. -/
theorem resolventCircleIntegral_mul_projection_eq_ite (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    resolventCircleIntegral hp φ c r * periodicSpectralProjection hp φ z =
      if z ∈ ball c r then periodicSpectralProjection hp φ z else 0 := by
  classical
  by_cases hz : z ∈ ball c r
  · rw [if_pos hz]
    exact resolventCircleIntegral_mul_projection hp φ c z r hc hz
  · rw [if_neg hz]
    by_cases hzc : z ∈ closedBall c r
    · have hzs : z ∈ sphere c r := mem_sphere.mpr
        (le_antisymm (mem_closedBall.mp hzc) (not_lt.mp hz))
      rw [(periodicSpectralProjection_eq_zero_iff hp φ z).mpr (hc hzs), mul_zero]
    · exact resolventCircleIntegral_mul_projection_eq_zero hp φ c z r hr hc hzc

/-- On every finite spectral cluster, the contour integral selects precisely
the root spaces whose parameters lie inside the circle. -/
theorem resolventCircleIntegral_mul_cluster (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) (s : Finset ℂ) :
    resolventCircleIntegral hp φ c r * periodicClusterProjection hp φ s =
      periodicClusterProjection hp φ (s.filter (fun z => z ∈ ball c r)) := by
  classical
  rw [periodicClusterProjection, Finset.mul_sum]
  simp_rw [resolventCircleIntegral_mul_projection_eq_ite hp φ c _ r hr hc]
  exact (Finset.sum_filter _ _).symm

end NLS.ZakharovShabat
