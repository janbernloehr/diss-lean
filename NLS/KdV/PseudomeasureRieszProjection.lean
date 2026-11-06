import NLS.KdV.PseudomeasureRootSpaces
import NLS.FunctionalAnalysis.CircleResolventProjection
import NLS.FunctionalAnalysis.ProjectionRank
import NLS.Fourier.PeriodicSingularMultiplicationFamily

/-!
# Actual Riesz projections for the original singular Hill operator

The integral is taken in the operator norm on the original H-minus-one base
space. Every circle contained in the full physical resolvent gives a compact
idempotent and therefore an actual finite-dimensional spectral range.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Joint operator-norm analyticity uses the actual potential-to-multiplication map. -/
theorem analyticAt_endpointHillNormalizedPencil_joint (r : ℝ) (hr1 : r < 1/2)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) :
    AnalyticAt ℂ (fun x : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ =>
      endpointHillNormalizedPencil r hr1 x.1 x.2) p := by
  let V := (hminusOneMultiplicationFamily (L := 2)).comp
    (endpointHillHminusOne SpectralWeight.one r hr1)
  have hV : AnalyticAt ℂ (fun x : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ => V x.1) p :=
    (V.analyticAt p.1).comp analyticAt_fst
  exact SchurComplement.analyticAt_compCLM analyticAt_const
    ((analyticAt_const.add hV).sub (analyticAt_snd.smul analyticAt_const))

/-- The full original H1-valued inverse is jointly norm analytic wherever it is invertible. -/
theorem analyticAt_endpointHillResolventToH1_joint (r : ℝ) (hr1 : r < 1/2)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hp : p.2 ∈ endpointHillResolventSet r hr1 p.1) :
    AnalyticAt ℂ (fun x : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ =>
      endpointHillResolventToH1 r hr1 x.1 x.2) p := by
  have hu := (mem_endpointHillResolventSet_iff_isUnit r hr1 p.1 p.2).mp hp
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ) _ hu).comp
    (f := fun x : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ =>
      endpointHillNormalizedPencil r hr1 x.1 x.2)
    (analyticAt_endpointHillNormalizedPencil_joint r hr1 p)
  exact SchurComplement.analyticAt_compCLM hi analyticAt_const

/-- The actual compact H-minus-one resolvent is jointly analytic in potential and spectral parameter. -/
theorem analyticAt_endpointHillBaseResolvent_joint (r : ℝ) (hr1 : r < 1/2)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hp : p.2 ∈ endpointHillResolventSet r hr1 p.1) :
    AnalyticAt ℂ (fun x : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ =>
      endpointHillBaseResolvent r hr1 x.1 x.2) p :=
  SchurComplement.analyticAt_compCLM analyticAt_const
    (analyticAt_endpointHillResolventToH1_joint r hr1 p hp)

/-- The actual compact base resolvent is norm analytic on the full physical resolvent set. -/
theorem analyticAt_endpointHillBaseResolvent (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ)
    (hz : z ∈ endpointHillResolventSet r hr1 q) :
    AnalyticAt ℂ (endpointHillBaseResolvent r hr1 q) z :=
  SchurComplement.analyticAt_compCLM analyticAt_const
    (analyticAt_endpointHillResolventToH1 r hr1 q z hz)

/-- The negative of the original (L-z) inverse has the conventional (z-L) orientation. -/
theorem endpointHill_oriented_resolvent_identity (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z w : ℂ)
    (hz : z ∈ endpointHillResolventSet r hr1 q) (hw : w ∈ endpointHillResolventSet r hr1 q) :
    -endpointHillBaseResolvent r hr1 q z-(-endpointHillBaseResolvent r hr1 q w) =
      (w-z) • ((-endpointHillBaseResolvent r hr1 q z)*(-endpointHillBaseResolvent r hr1 q w)) := by
  rw [neg_mul_neg,neg_sub_neg,← neg_sub,endpointHillBaseResolvent_sub r hr1 q z w hz hw,
    ← neg_smul,neg_sub]
  rfl


/-- The actual circular spectral projection on original H-minus-one. -/
def endpointHillRieszProjection (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (c : ℂ) (ρ : ℝ) :
    FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  CircleIntegral.normalized (fun z => -endpointHillBaseResolvent r hr1 q z) c ρ

/-- A circle in the full physical resolvent defines an actual idempotent. -/
theorem isIdempotentElem_endpointHillRieszProjection (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ endpointHillResolventSet r hr1 q) :
    IsIdempotentElem (endpointHillRieszProjection r hr1 q c ρ) := by
  apply CircleIntegral.isIdempotentElem_normalized_resolvent_of_open _
    (endpointHillResolventSet r hr1 q) (isOpen_endpointHillResolventSet r hr1 q) c ρ hρ hc
  · intro z hz
    exact (analyticAt_endpointHillBaseResolvent r hr1 q z hz).neg
  · exact fun z hz w hw => endpointHill_oriented_resolvent_identity r hr1 q z w hz hw

/-- The actual singular Riesz projection is compact in the original base norm. -/
theorem isCompactOperator_endpointHillRieszProjection (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (c : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hc : sphere c ρ ⊆ endpointHillResolventSet r hr1 q) :
    IsCompactOperator (endpointHillRieszProjection r hr1 q c ρ) := by
  apply CircleIntegral.isCompactOperator_normalized hρ
  · intro z hz
    exact ((analyticAt_endpointHillBaseResolvent r hr1 q z (hc hz)).neg).continuousAt.continuousWithinAt
  · exact fun z _ => (isCompactOperator_endpointHillBaseResolvent r hr1 q z).neg

/-- Its spectral range is genuinely finite dimensional on the original H-minus-one space. -/
theorem finiteDimensional_endpointHillRieszProjection_range (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ endpointHillResolventSet r hr1 q) :
    FiniteDimensional ℂ (endpointHillRieszProjection r hr1 q c ρ).range :=
  CircleIntegral.finiteDimensional_range_of_compact_idempotent _
    (isIdempotentElem_endpointHillRieszProjection r hr1 q c ρ hρ hc)
    (isCompactOperator_endpointHillRieszProjection r hr1 q c ρ hρ.le hc)

/-- An actual physical eigenvector enclosed by the circle lies in the projection range. -/
theorem endpointHillRieszProjection_eigenvector_inside (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ endpointHillResolventSet r hr1 q)
    (μ : ℂ) (hμ : μ ∈ ball c ρ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      μ • singularHillDomainInclusion f) :
    endpointHillRieszProjection r hr1 q c ρ (singularHillDomainInclusion f) =
      singularHillDomainInclusion f := by
  have hint : CircleIntegrable (fun z => -endpointHillBaseResolvent r hr1 q z) c ρ :=
    (show ContinuousOn (fun z => -endpointHillBaseResolvent r hr1 q z) (sphere c ρ) from
      fun z hz => ((analyticAt_endpointHillBaseResolvent r hr1 q z (hc hz)).neg).continuousAt.continuousWithinAt).circleIntegrable hρ.le
  change (2*Real.pi*Complex.I:ℂ)⁻¹ •
    ((∮ z in C(c,ρ), -endpointHillBaseResolvent r hr1 q z) (singularHillDomainInclusion f)) = _
  rw [CircleIntegral.apply hint]
  have he : (∮ z in C(c,ρ), (-endpointHillBaseResolvent r hr1 q z) (singularHillDomainInclusion f)) =
      ∮ z in C(c,ρ), (z-μ)⁻¹ • singularHillDomainInclusion f := by
    apply circleIntegral.integral_congr hρ.le
    intro z hz
    have hμz : μ ≠ z := fun he => by
      rw [he] at hμ
      exact not_lt.mpr (mem_sphere.mp hz).ge hμ
    change -(endpointHillBaseResolvent r hr1 q z (singularHillDomainInclusion f)) = _
    rw [endpointHillBaseResolvent_eigenvector r hr1 q z μ (hc hz) hμz f hf,
      ← neg_smul,← inv_neg,neg_sub]
  rw [he,circleIntegral.integral_smul_const,circleIntegral.integral_sub_inv_of_mem_ball hμ,
    smul_smul,inv_mul_cancel₀,one_smul]
  simp [Real.pi_ne_zero]

/-- Every actual physical eigenvector outside the disk is annihilated by the projection. -/
theorem endpointHillRieszProjection_eigenvector_outside (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ endpointHillResolventSet r hr1 q)
    (μ : ℂ) (hμ : μ ∉ closedBall c ρ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      μ • singularHillDomainInclusion f) :
    endpointHillRieszProjection r hr1 q c ρ (singularHillDomainInclusion f) = 0 := by
  have hint : CircleIntegrable (fun z => -endpointHillBaseResolvent r hr1 q z) c ρ :=
    (show ContinuousOn (fun z => -endpointHillBaseResolvent r hr1 q z) (sphere c ρ) from
      fun z hz => ((analyticAt_endpointHillBaseResolvent r hr1 q z (hc hz)).neg).continuousAt.continuousWithinAt).circleIntegrable hρ.le
  change (2*Real.pi*Complex.I:ℂ)⁻¹ •
    ((∮ z in C(c,ρ), -endpointHillBaseResolvent r hr1 q z) (singularHillDomainInclusion f)) = _
  rw [CircleIntegral.apply hint]
  have he : (∮ z in C(c,ρ), (-endpointHillBaseResolvent r hr1 q z) (singularHillDomainInclusion f)) =
      ∮ z in C(c,ρ), (z-μ)⁻¹ • singularHillDomainInclusion f := by
    apply circleIntegral.integral_congr hρ.le
    intro z hz
    have hμz : μ ≠ z := (ne_of_mem_of_not_mem (sphere_subset_closedBall hz) hμ).symm
    change -(endpointHillBaseResolvent r hr1 q z (singularHillDomainInclusion f)) = _
    rw [endpointHillBaseResolvent_eigenvector r hr1 q z μ (hc hz) hμz f hf,
      ← neg_smul,← inv_neg,neg_sub]
  rw [he,circleIntegral.integral_smul_const,CircleIntegral.integral_sub_inv_eq_zero hρ.le hμ,
    zero_smul,smul_zero]

/-- Actual projections vary continuously along any continuous potential family
with a common physical resolvent circle. -/
theorem continuousOn_endpointHillRieszProjection (r : ℝ) (hr1 : r < 1/2)
    {X : Type*} [TopologicalSpace X]
    (q : X → WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (s : Set X) (hq : ContinuousOn q s) (c : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hc : ∀ x ∈ s, sphere c ρ ⊆ endpointHillResolventSet r hr1 (q x)) :
    ContinuousOn (fun x => endpointHillRieszProjection r hr1 (q x) c ρ) s := by
  apply CircleIntegral.continuousOn_normalized _ s c ρ hρ
  have hm : ContinuousOn (fun p : X × ℂ => (q p.1,p.2)) (s ×ˢ sphere c ρ) :=
    (hq.comp continuous_fst.continuousOn (fun _ h => h.1)).prodMk continuous_snd.continuousOn
  intro p hp
  exact ((analyticAt_endpointHillBaseResolvent_joint r hr1 (q p.1,p.2)
    (hc p.1 hp.1 hp.2)).neg).continuousAt.comp_continuousWithinAt
      (f := fun p : X × ℂ => (q p.1,p.2)) (hm p hp)

/-- The rank of actual singular spectral projections is invariant on a preconnected
potential family with a common physical resolvent circle. -/
theorem endpointHillRieszProjection_rank_eq (r : ℝ) (hr1 : r < 1/2)
    {X : Type*} [TopologicalSpace X]
    (q : X → WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (s : Set X) (hs : IsPreconnected s) (hq : ContinuousOn q s)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : ∀ x ∈ s, sphere c ρ ⊆ endpointHillResolventSet r hr1 (q x))
    {a b : X} (ha : a ∈ s) (hb : b ∈ s) :
    Module.finrank ℂ (endpointHillRieszProjection r hr1 (q a) c ρ).range =
      Module.finrank ℂ (endpointHillRieszProjection r hr1 (q b) c ρ).range :=
  ProjectionRank.finrank_eq_on_preconnected hs _
    (continuousOn_endpointHillRieszProjection r hr1 q s hq c ρ hρ.le hc)
    (fun x hx => isIdempotentElem_endpointHillRieszProjection r hr1 (q x) c ρ hρ (hc x hx))
    (fun x hx => finiteDimensional_endpointHillRieszProjection_range r hr1 (q x) c ρ hρ (hc x hx)) ha hb

end NLS.KdV
