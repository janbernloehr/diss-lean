import NLS.KdV.PseudomeasureResolvent
import NLS.FunctionalAnalysis.CompactSpectrum
import NLS.KdV.SingularHillOperatorDomain

/-! # Closedness and discreteness of the original singular endpoint Hill operator

The actual operator acts on original H-minus-one with original H1 domain,
as in Appendix C. Its graph is closed, its domain is dense and each bounded
spectral region contains only finitely many eigenvalues. No spectral labels,
asymptotic enumeration or algebraic-multiplicity identification is assumed.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The graph of the actual source operator, embedded in its original base space. -/
def endpointHillGraph (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    Set (FourierLebesgueSpace (2:ℝ) (-1) 2 × FourierLebesgueSpace (2:ℝ) (-1) 2) :=
  {p | ∃ f : FourierLebesgueSpace (2:ℝ) 1 2,
    singularHillDomainInclusion f = p.1 ∧
      singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f = p.2}

/-- One actual resolvent gives an exact closed-equation characterization of the physical graph. -/
theorem endpointHillGraph_eq (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) :
    endpointHillGraph r hr1 q = {p | endpointHillBaseResolvent r hr1 q a (p.2-a • p.1) = p.1} := by
  ext p
  constructor
  · rintro ⟨f,hf,hL⟩
    change endpointHillBaseResolvent r hr1 q a (p.2-a • p.1) = p.1
    rw [← hf, ← hL]
    change singularHillDomainInclusion (endpointHillResolventToH1 r hr1 q a
      (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
        a • singularHillDomainInclusion f)) = singularHillDomainInclusion f
    rw [endpointHillResolventToH1_left r hr1 q a ha f]
  · intro h
    let f := endpointHillResolventToH1 r hr1 q a (p.2-a • p.1)
    change singularHillDomainInclusion f = p.1 at h
    refine ⟨f,h,?_⟩
    have he := endpointHillResolventToH1_right r hr1 q a ha (p.2-a • p.1)
    change singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
      a • singularHillDomainInclusion f = p.2-a • p.1 at he
    rw [h] at he
    exact sub_left_inj.mp he

/-- The source unbounded operator is closed on its full original H1 domain. -/
theorem isClosed_endpointHillGraph (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    IsClosed (endpointHillGraph r hr1 q) := by
  obtain ⟨a,ha⟩ := endpointHillResolventSet_nonempty r hr hr1 q
  rw [endpointHillGraph_eq r hr1 q a ha]
  exact isClosed_eq ((endpointHillBaseResolvent r hr1 q a).continuous.comp
    (continuous_snd.sub (continuous_fst.const_smul a))) continuous_fst

/-- The actual physical eigen-equation transports to the compact base resolvent. -/
theorem endpointHillBaseResolvent_eigenvector (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a z : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) (hza : z ≠ a)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) :
    endpointHillBaseResolvent r hr1 q a (singularHillDomainInclusion f) =
      (z-a)⁻¹ • singularHillDomainInclusion f := by
  have h := endpointHillResolventToH1_left r hr1 q a ha f
  rw [hf, ← sub_smul, map_smul] at h
  have he := congrArg (fun v => (z-a)⁻¹ • v) h
  rw [inv_smul_smul₀ (sub_ne_zero.mpr hza)] at he
  change singularHillDomainInclusion
    (endpointHillResolventToH1 r hr1 q a (singularHillDomainInclusion f)) = _
  rw [he, map_smul]

/-- Every physical spectral point becomes a nonzero eigenvalue of the actual compact resolvent. -/
theorem endpointHillSpectrum_compact_eigenvalue (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a z : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) (hz : z ∈ endpointHillSpectrum r hr1 q) :
    Module.End.HasEigenvalue (endpointHillBaseResolvent r hr1 q a).toLinearMap (z-a)⁻¹ := by
  have hza : z ≠ a := by rintro rfl; exact hz ha
  obtain ⟨f,hf0,hf⟩ := (mem_endpointHillSpectrum_iff r hr hr1 q z).mp hz
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := singularHillDomainInclusion f)
  refine ⟨Module.End.mem_eigenspace_iff.mpr
    (endpointHillBaseResolvent_eigenvector r hr1 q a z ha hza f hf), ?_⟩
  intro h
  apply hf0
  apply singularHillDomainInclusion_injective
  simpa only [map_zero] using h

/-- Each bounded spectral region contains only finitely many actual physical eigenvalues. -/
theorem finite_endpointHillSpectrum_norm_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (R : ℝ) :
    Set.Finite {z : ℂ | z ∈ endpointHillSpectrum r hr1 q ∧ ‖z‖ ≤ R} := by
  obtain ⟨a,ha⟩ := endpointHillResolventSet_nonempty r hr hr1 q
  let B := max R 0 + ‖a‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let S := {μ : ℂ | Module.End.HasEigenvalue
    (endpointHillBaseResolvent r hr1 q a).toLinearMap μ ∧ B⁻¹ ≤ ‖μ‖}
  have hS : Set.Finite S := CompactSpectrum.finite_eigenvalues_norm_ge
    (endpointHillBaseResolvent r hr1 q a) (isCompactOperator_endpointHillBaseResolvent r hr1 q a)
      (inv_pos.mpr hB)
  have hi : Function.Injective (fun z : ℂ => (z-a)⁻¹) := by
    intro z y h
    exact sub_left_inj.mp (inv_injective h)
  apply (hS.preimage hi.injOn).subset
  rintro z ⟨hz,hzR⟩
  refine ⟨endpointHillSpectrum_compact_eigenvalue r hr hr1 q a z ha hz, ?_⟩
  rw [norm_inv]
  have hza : z-a ≠ 0 := sub_ne_zero.mpr (by rintro rfl; exact hz ha)
  apply inv_anti₀ (norm_pos_iff.mpr hza)
  exact (norm_sub_le _ _).trans (by dsimp [B]; linarith [le_max_left R 0])

/-- The source unbounded operator is closed in the standard partial-linear-map API. -/
theorem isClosed_endpointHillPartialOperator (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    (singularHillPartialOperator (endpointHillHminusOne SpectralWeight.one r hr1 q)).IsClosed := by
  change IsClosed ((singularHillPartialOperator
    (endpointHillHminusOne SpectralWeight.one r hr1 q)).graph :
      Set (FourierLebesgueSpace (2:ℝ) (-1) 2 × FourierLebesgueSpace (2:ℝ) (-1) 2))
  rw [singularHillPartialOperator_graph]
  exact isClosed_endpointHillGraph r hr hr1 q

end NLS.KdV
