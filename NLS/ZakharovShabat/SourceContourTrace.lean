import NLS.ZakharovShabat.SourceContourRanks
import NLS.ZakharovShabat.SymmetricEigenvalues

/-! # Traces of the actual original-norm contour restriction

A bounded sourceContourLift places every spectral-range vector in the original operator
domain. The sourceContourRestriction endomorphism acts by that original operator, and its
power traces agree with the established coefficient-space traces by a proved
conjugation identity. Analyticity uses the original potential topology.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bounded lift of the contour projection into the original one-derivative domain. -/
def sourceContourLift (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ) :
    CoeffPair p →L[ℂ] WeightedCoeffPair (Weight.sobolev 1) p :=
  (WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm.toContinuousLinearMap.comp
    ((resolventCircleIntegralToDomain hp (CoeffPair.toMax p φ) c R).comp (CoeffPair.toMax p).toContinuousLinearMap)

/-- The original operator applied to the contour lift; this is the bounded map L P. -/
def sourceContourOperator (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ) :
    CoeffPair p →L[ℂ] CoeffPair p := (sourceOperator hp φ).comp (sourceContourLift hp φ c R)

theorem sourceContourOperator_eq_conj (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ) :
    sourceContourOperator hp φ c R = (CoeffPair.toMax p).symm.conjContinuousAlgEquiv
      (contourOperator hp (CoeffPair.toMax p φ) c R) := by
  apply ContinuousLinearMap.ext
  intro x
  change (CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p φ)
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) p) ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm
      (resolventCircleIntegralToDomain hp (CoeffPair.toMax p φ) c R (CoeffPair.toMax p x))))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem sourceResolventCircleIntegral_eq_sourceInclusion (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    sourceResolventCircleIntegral hp φ c R = sourceDomainInclusion.comp (sourceContourLift hp φ c R) := by
  rw [sourceResolventCircleIntegral_eq_conj hp φ c R hR hc]
  apply ContinuousLinearMap.ext
  intro x
  change (CoeffPair.toMax p).symm (resolventCircleIntegral hp (CoeffPair.toMax p φ) c R (CoeffPair.toMax p x)) =
    (CoeffPair.toMax p).symm (domainInclusion ((WeightedCoeffPair.toMax (Weight.sobolev 1) p)
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm
        (resolventCircleIntegralToDomain hp (CoeffPair.toMax p φ) c R (CoeffPair.toMax p x)))))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply congrArg (CoeffPair.toMax p).symm
  exact congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A (CoeffPair.toMax p x))
    (resolventCircleIntegral_eq_inclusion hp _ c R hR (by rwa [sourceResolventSet_eq] at hc))

/-- An endomorphism of the actual original-norm contour range. -/
def sourceContourRestriction (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ) :
    (sourceResolventCircleIntegral hp φ c R).range →L[ℂ] (sourceResolventCircleIntegral hp φ c R).range :=
  ProjectionTransport.compressionMap (sourceResolventCircleIntegral hp φ c R) (sourceContourOperator hp φ c R)

theorem sourceProjection_mul_contourOperator (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    sourceResolventCircleIntegral hp φ c R * sourceContourOperator hp φ c R = sourceContourOperator hp φ c R := by
  rw [sourceResolventCircleIntegral_eq_conj hp φ c R hR hc,sourceContourOperator_eq_conj,
    ← map_mul,projection_mul_contourOperator hp _ c R hR (by rwa [sourceResolventSet_eq] at hc)]

/-- On the contour range, the intrinsic map acts by the original operator on its domain lift. -/
theorem sourceContourRestriction_apply (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ)
    (x : (sourceResolventCircleIntegral hp φ c R).range) :
    (sourceContourRestriction hp φ c R x).val = sourceOperator hp φ (sourceContourLift hp φ c R x.val) :=
  congrArg (fun A : CoeffPair p →L[ℂ] CoeffPair p => A x.val)
    (sourceProjection_mul_contourOperator hp φ c R hR hc)

/-- Coefficient-preserving linear identification of the actual contour ranges. -/
def sourceContourRangeEquiv (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    (sourceResolventCircleIntegral hp φ c R).range ≃ₗ[ℂ]
      (resolventCircleIntegral hp (CoeffPair.toMax p φ) c R).range :=
  (LinearEquiv.ofEq _ _ (congrArg (fun A : CoeffPair p →L[ℂ] CoeffPair p => A.range)
    (sourceResolventCircleIntegral_eq_conj hp φ c R hR hc))).trans
      (ConjugatedRanges.rangeEquiv (CoeffPair.toMax p) _)

theorem sourceContourRangeEquiv_apply (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ)
    (x : (sourceResolventCircleIntegral hp φ c R).range) :
    (sourceContourRangeEquiv hp φ c R hR hc x).val = CoeffPair.toMax p x.val := rfl

theorem sourceContourRestriction_conjugate (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    (sourceContourRangeEquiv hp φ c R hR hc).conjAlgEquiv ℂ (sourceContourRestriction hp φ c R).toLinearMap =
      (reducedContourOperator hp (CoeffPair.toMax p φ) (CoeffPair.toMax p φ) c R).toLinearMap := by
  let e := sourceContourRangeEquiv hp φ c R hR hc
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (e (sourceContourRestriction hp φ c R (e.symm x))).val = _
  rw [sourceContourRangeEquiv_apply, sourceContourRestriction_apply hp φ c R hR hc]
  change (CoeffPair.toMax p) (sourceContourOperator hp φ c R (e.symm x).val) = _
  rw [sourceContourOperator_eq_conj]
  change (CoeffPair.toMax p) ((CoeffPair.toMax p).symm
    (contourOperator hp (CoeffPair.toMax p φ) c R (CoeffPair.toMax p (e.symm x).val))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have hex : CoeffPair.toMax p (e.symm x).val = x.val := congrArg Subtype.val (e.apply_symm_apply x)
  rw [hex]
  exact (reducedContourOperator_self_apply hp (CoeffPair.toMax p φ) c R hR
    (by rwa [sourceResolventSet_eq] at hc) x).symm

/-- Trace of a power of the intrinsic original-norm operator restriction. -/
def sourceContourTracePower (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ) (k : ℕ) : ℂ :=
  LinearMap.trace ℂ (sourceResolventCircleIntegral hp φ c R).range ((sourceContourRestriction hp φ c R).toLinearMap^k)

theorem sourceContourTracePower_eq (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) (k : ℕ) :
    sourceContourTracePower hp φ c R k = contourTracePower hp (CoeffPair.toMax p φ) c R k := by
  unfold sourceContourTracePower contourTracePower
  rw [← sourceContourRestriction_conjugate hp φ c R hR hc, ← map_pow, LinearMap.trace_map]

/-- The lifted domain vector represents exactly the given vector of the contour range. -/
theorem sourceInclusion_contourLift_range (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ)
    (x : (sourceResolventCircleIntegral hp φ c R).range) :
    sourceDomainInclusion (sourceContourLift hp φ c R x.val) = x.val := by
  have he := congrArg (fun A : CoeffPair p →L[ℂ] CoeffPair p => A x.val)
    (sourceResolventCircleIntegral_eq_sourceInclusion hp φ c R hR hc)
  change sourceResolventCircleIntegral hp φ c R x.val = sourceDomainInclusion (sourceContourLift hp φ c R x.val) at he
  rw [← he]
  obtain ⟨y,hy⟩ := x.property
  change sourceResolventCircleIntegral hp φ c R y = x.val at hy
  rw [← hy]
  exact congrArg (fun A : CoeffPair p →L[ℂ] CoeffPair p => A y)
    (sourceResolventCircleIntegral_idempotent hp φ c R hR hc)

/-- Every intrinsic power trace is analytic in the original potential norm on admissible circles. -/
theorem analyticAt_sourceContourTracePower (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) (k : ℕ) :
    AnalyticAt ℂ (fun ψ => sourceContourTracePower hp ψ c R k) φ := by
  have hc' : Metric.sphere c R ⊆ resolventSet hp (CoeffPair.toMax p φ) := by
    rwa [sourceResolventSet_eq] at hc
  have ha := (analyticAt_contourTracePower hp (CoeffPair.toMax p φ) c R hR hc' k).comp
    ((CoeffPair.toMax p).analyticAt φ)
  apply ha.congr
  have hn : ∀ᶠ ψ in nhds φ, CoeffPair.toMax p ψ ∈ resolventCircleDomain hp c R :=
    ((isOpen_resolventCircleDomain hp c R).preimage (CoeffPair.toMax p).continuous).mem_nhds hc'
  filter_upwards [hn] with ψ hψ
  exact (sourceContourTracePower_eq hp ψ c R hR (by rwa [sourceResolventSet_eq]) k).symm

/-- The midpoint from the trace of the actual original-norm restriction. -/
def sourceContourMidpoint (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ) : ℂ :=
  sourceContourTracePower hp φ c R 1 / 2

/-- The squared gap from the first two intrinsic traces, allowing eigenvalue collisions. -/
def sourceContourSquaredGap (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ) : ℂ :=
  2 * sourceContourTracePower hp φ c R 2 - (sourceContourTracePower hp φ c R 1)^2

theorem sourceContourMidpoint_eq (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    sourceContourMidpoint hp φ c R = contourMidpoint hp (CoeffPair.toMax p φ) c R := by
  unfold sourceContourMidpoint contourMidpoint
  rw [sourceContourTracePower_eq hp φ c R hR hc]

theorem sourceContourSquaredGap_eq (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    sourceContourSquaredGap hp φ c R = contourSquaredGap hp (CoeffPair.toMax p φ) c R := by
  unfold sourceContourSquaredGap contourSquaredGap
  rw [sourceContourTracePower_eq hp φ c R hR hc,sourceContourTracePower_eq hp φ c R hR hc]

/-- The displayed centered-square trace is half the squared gap, without diagonalizability. -/
theorem sourceContour_centeredSquare_trace (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ)
    (hdim : Module.finrank ℂ (sourceResolventCircleIntegral hp φ c R).range = 2) :
    LinearMap.trace ℂ (sourceResolventCircleIntegral hp φ c R).range
      (((sourceContourRestriction hp φ c R).toLinearMap - sourceContourMidpoint hp φ c R • 1)^2) =
        sourceContourSquaredGap hp φ c R / 2 := by
  let := finiteDimensional_range_sourceResolventCircleIntegral hp φ c R hR hc
  rw [FiniteSpectralTrace.trace_centered_square,hdim]
  simp only [Nat.cast_ofNat]
  unfold sourceContourMidpoint sourceContourSquaredGap sourceContourTracePower
  simp only [pow_one]
  ring

/-- Original-norm trace invariants are the midpoint and squared gap of the enclosed
pair, including a repeated eigenvalue and a possible nontrivial Jordan block. -/
theorem sourceContourMidpoint_squaredGap_eq_pair (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ)
    (hdim : Module.finrank ℂ (sourceResolventCircleIntegral hp φ c R).range = 2)
    (a b : ℂ) (hs : enclosedPeriodicSpectrum hp (CoeffPair.toMax p φ) c R = {a,b}) :
    sourceContourMidpoint hp φ c R = (a+b)/2 ∧ sourceContourSquaredGap hp φ c R = (a-b)^2 ∧
      LinearMap.trace ℂ (sourceResolventCircleIntegral hp φ c R).range
        (((sourceContourRestriction hp φ c R).toLinearMap - sourceContourMidpoint hp φ c R • 1)^2) =
          (a-b)^2/2 := by
  have hd : Module.finrank ℂ (resolventCircleIntegral hp (CoeffPair.toMax p φ) c R).range = 2 := by
    rwa [finrank_range_sourceResolventCircleIntegral hp φ c R hR hc] at hdim
  have h := contourMidpoint_squaredGap_eq_pair hp (CoeffPair.toMax p φ) c R hR
    (by rwa [sourceResolventSet_eq] at hc) hd a b hs
  have hm : sourceContourMidpoint hp φ c R = (a+b)/2 :=
    (sourceContourMidpoint_eq hp φ c R hR hc).trans h.1
  have hg : sourceContourSquaredGap hp φ c R = (a-b)^2 :=
    (sourceContourSquaredGap_eq hp φ c R hR hc).trans h.2.1
  exact ⟨hm,hg,(sourceContour_centeredSquare_trace hp φ c R hR hc hdim).trans (congrArg (fun z : ℂ => z/2) hg)⟩

/-- Analyticity includes the printed half-squared-gap normalization. -/
theorem analyticAt_sourceContourMidpoint_and_halfSquaredGap (hp : p ≠ ⊤) (φ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    AnalyticAt ℂ (fun ψ => sourceContourMidpoint hp ψ c R) φ ∧
      AnalyticAt ℂ (fun ψ => sourceContourSquaredGap hp ψ c R / 2) φ := by
  have h₁ := analyticAt_sourceContourTracePower hp φ c R hR hc 1
  have h₂ := analyticAt_sourceContourTracePower hp φ c R hR hc 2
  exact ⟨h₁.div_const,((analyticAt_const.mul h₂).sub (h₁.pow 2)).div_const⟩

/-- The source midpoint in the quarter-pi disk at pi*n. -/
def sourcePeriodicMidpoint (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) : ℂ :=
  sourceContourMidpoint hp φ ((Real.pi : ℂ)*n) (Real.pi/4)

/-- The source squared gap in the quarter-pi disk at pi*n. -/
def sourcePeriodicSquaredGap (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) : ℂ :=
  sourceContourSquaredGap hp φ ((Real.pi : ℂ)*n) (Real.pi/4)

/-- At the free potential both eigenvalues coincide at pi*n. -/
theorem sourcePeriodicMidpoint_squaredGap_zero (hp : p ≠ ⊤) (n : ℤ) :
    sourcePeriodicMidpoint hp (0 : CoeffPair p) n = (Real.pi : ℂ)*n ∧
      sourcePeriodicSquaredGap hp (0 : CoeffPair p) n = 0 := by
  have hr : 0 < Real.pi/4 := by positivity
  have hc : Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4) ⊆ sourceResolventSet hp (0 : CoeffPair p) := by
    rw [sourceResolventSet_eq,map_zero]
    exact sphere_subset_resolventSet_of_smallPotential hp 0 n hr le_rfl (by simpa using hr)
  change sourceContourMidpoint hp 0 _ _ = _ ∧ sourceContourSquaredGap hp 0 _ _ = _
  rw [sourceContourMidpoint_eq hp 0 _ _ hr.le hc,sourceContourSquaredGap_eq hp 0 _ _ hr.le hc,map_zero]
  exact periodicMidpoint_squaredGap_zero hp n

end NLS.ZakharovShabat
