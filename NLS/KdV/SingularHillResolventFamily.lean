import NLS.KdV.PseudomeasureRieszProjection

/-! Joint operator-norm resolvent dependence on the full original H-minus-one
potential, without requiring endpoint-norm convergence of the potential. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Fixed free normalization of the original pencil, for every H-minus-one potential. -/
def singularHillNormalizedPencil (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  singularHillFreeInverse.comp (singularHillOperator q-z • singularHillDomainInclusion)

/-- The full original physical resolvent set, with the unchanged H1 domain. -/
def singularHillResolventSet (q : FourierLebesgueSpace (2:ℝ) (-1) 2) : Set ℂ :=
  {z | Function.Bijective (singularHillOperator q-z • singularHillDomainInclusion)}

/-- Free normalization neither adds nor removes any physical resolvent point. -/
theorem mem_singularHillResolventSet_iff_isUnit
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    z ∈ singularHillResolventSet q ↔ IsUnit (singularHillNormalizedPencil q z) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  change Function.Bijective (singularHillOperator q-z • singularHillDomainInclusion) ↔
    Function.Bijective (singularHillNormalizedPencil q z)
  constructor
  · intro h
    exact singularHillFreeIsomorphism.symm.bijective.comp h
  · intro h
    constructor
    · intro f g hfg
      apply h.1
      exact congrArg singularHillFreeInverse hfg
    · intro g
      obtain ⟨f, hf⟩ := h.2 (singularHillFreeInverse g)
      exact ⟨f, singularHillFreeIsomorphism.symm.injective hf⟩

/-- Joint analyticity uses the FULL original H-minus-one norm on potentials. -/
theorem analyticAt_singularHillNormalizedPencil_joint
    (p : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ) :
    AnalyticAt ℂ (fun x : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ =>
      singularHillNormalizedPencil x.1 x.2) p := by
  have hV := ((hminusOneMultiplicationFamily (L := 2)).analyticAt p.1).comp analyticAt_fst
  exact SchurComplement.analyticAt_compCLM analyticAt_const
    ((analyticAt_const.add hV).sub (analyticAt_snd.smul analyticAt_const))

/-- The full joint physical resolvent locus is open in H-minus-one times C. -/
theorem isOpen_singularHillJointResolvent :
    IsOpen {p : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ | p.2 ∈ singularHillResolventSet p.1} := by
  have hc : Continuous (fun p : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ =>
      singularHillNormalizedPencil p.1 p.2) :=
    continuous_iff_continuousAt.mpr (fun p => (analyticAt_singularHillNormalizedPencil_joint p).continuousAt)
  have he : {p : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ | p.2 ∈ singularHillResolventSet p.1} =
      (fun p => singularHillNormalizedPencil p.1 p.2) ⁻¹' {T | IsUnit T} := by
    ext p
    exact mem_singularHillResolventSet_iff_isUnit p.1 p.2
  rw [he]
  exact Units.isOpen.preimage hc

/-- Total inverse family into the original full H1 domain. -/
def singularHillResolventToH1 (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  (Ring.inverse (singularHillNormalizedPencil q z)).comp singularHillFreeInverse

/-- The actual resolvent on the original H-minus-one base. -/
def singularHillBaseResolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  singularHillDomainInclusion.comp (singularHillResolventToH1 q z)

/-- Every original H1 vector is recovered from its full physical pencil image. -/
theorem singularHillResolventToH1_left (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (hz : z ∈ singularHillResolventSet q) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillResolventToH1 q z (singularHillOperator q f-z • singularHillDomainInclusion f) = f := by
  have hu := (mem_singularHillResolventSet_iff_isUnit q z).mp hz
  exact congrArg (fun T : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ]
    FourierLebesgueSpace (2:ℝ) 1 2 => T f)
    (Ring.inverse_mul_cancel (singularHillNormalizedPencil q z) hu)

/-- Every original H-minus-one datum is solved on the entire original H1 domain. -/
theorem singularHillResolventToH1_right (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (hz : z ∈ singularHillResolventSet q) (g : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularHillOperator q (singularHillResolventToH1 q z g)-
      z • singularHillDomainInclusion (singularHillResolventToH1 q z g) = g := by
  have hu := (mem_singularHillResolventSet_iff_isUnit q z).mp hz
  apply singularHillFreeIsomorphism.symm.injective
  exact congrArg (fun T : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ]
    FourierLebesgueSpace (2:ℝ) 1 2 => T (singularHillFreeInverse g))
    (Ring.mul_inverse_cancel (singularHillNormalizedPencil q z) hu)

/-- Joint H1-valued inverse analyticity at every physical resolvent pair. -/
theorem analyticAt_singularHillResolventToH1_joint
    (p : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ) (hp : p.2 ∈ singularHillResolventSet p.1) :
    AnalyticAt ℂ (fun x : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ =>
      singularHillResolventToH1 x.1 x.2) p := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ) _
    ((mem_singularHillResolventSet_iff_isUnit p.1 p.2).mp hp)).comp
      (f := fun x : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ => singularHillNormalizedPencil x.1 x.2)
      (analyticAt_singularHillNormalizedPencil_joint p)
  exact SchurComplement.analyticAt_compCLM hi analyticAt_const

/-- Joint norm analyticity of the actual original H-minus-one resolvent. -/
theorem analyticAt_singularHillBaseResolvent_joint
    (p : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ) (hp : p.2 ∈ singularHillResolventSet p.1) :
    AnalyticAt ℂ (fun x : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ =>
      singularHillBaseResolvent x.1 x.2) p :=
  SchurComplement.analyticAt_compCLM analyticAt_const (analyticAt_singularHillResolventToH1_joint p hp)

/-- The base inverse is compact in the original H-minus-one norm. -/
theorem isCompactOperator_singularHillBaseResolvent
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    IsCompactOperator (singularHillBaseResolvent q z) :=
  isCompactOperator_singularHillDomainInclusion.comp_clm (singularHillResolventToH1 q z)

/-- Exact agreement with the previously constructed endpoint inverse. -/
theorem singularHillResolventToH1_endpoint (r : ℝ) (hr : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    singularHillResolventToH1 (endpointHillHminusOne SpectralWeight.one r hr q) z =
      endpointHillResolventToH1 r hr q z := rfl

/-- Exact agreement of the original base inverses, on and off the resolvent set. -/
theorem singularHillBaseResolvent_endpoint (r : ℝ) (hr : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    singularHillBaseResolvent (endpointHillHminusOne SpectralWeight.one r hr q) z =
      endpointHillBaseResolvent r hr q z := rfl

/-- A whole compact spectral circle remains in the full resolvent on an open
set of original H-minus-one potentials. -/
theorem isOpen_singularHillResolventCircle (c : ℂ) (ρ : ℝ) :
    IsOpen {q : FourierLebesgueSpace (2:ℝ) (-1) 2 | sphere c ρ ⊆ singularHillResolventSet q} := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  exact (isCompact_sphere c ρ).eventually_forall_of_forall_eventually
    (fun z hz => isOpen_singularHillJointResolvent.mem_nhds (hq hz))

/-- The original H-minus-one circular spectral projection. -/
def singularHillRieszProjection (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (ρ : ℝ) :
    FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  CircleIntegral.normalized (fun z => -singularHillBaseResolvent q z) c ρ

/-- The projection agrees exactly with the verified actual endpoint projection. -/
theorem singularHillRieszProjection_endpoint (r : ℝ) (hr : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (c : ℂ) (ρ : ℝ) :
    singularHillRieszProjection (endpointHillHminusOne SpectralWeight.one r hr q) c ρ =
      endpointHillRieszProjection r hr q c ρ := rfl

/-- Original H-minus-one continuous families with a common physical resolvent
circle have operator-norm continuous actual projections. -/
theorem continuousOn_singularHillRieszProjection {X : Type*} [TopologicalSpace X]
    (q : X → FourierLebesgueSpace (2:ℝ) (-1) 2) (s : Set X) (hq : ContinuousOn q s)
    (c : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hc : ∀ x ∈ s, sphere c ρ ⊆ singularHillResolventSet (q x)) :
    ContinuousOn (fun x => singularHillRieszProjection (q x) c ρ) s := by
  apply CircleIntegral.continuousOn_normalized _ s c ρ hρ
  have hm : ContinuousOn (fun p : X × ℂ => (q p.1,p.2)) (s ×ˢ sphere c ρ) :=
    (hq.comp continuous_fst.continuousOn (fun _ h => h.1)).prodMk continuous_snd.continuousOn
  intro p hp
  exact ((analyticAt_singularHillBaseResolvent_joint (q p.1,p.2)
    (hc p.1 hp.1 hp.2)).neg).continuousAt.comp_continuousWithinAt
      (f := fun p : X × ℂ => (q p.1,p.2)) (hm p hp)

end NLS.KdV
