import NLS.KdV.SingularHillFredholm

/-! Closedness and spectral discreteness on the full original H-minus-one
potential space, with the entire original H1 operator domain unchanged. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The spectrum of the original full-domain operator at arbitrary H-minus-one potential. -/
def singularHillSpectrum (q : FourierLebesgueSpace (2:ℝ) (-1) 2) : Set ℂ :=
  (singularHillResolventSet q)ᶜ

/-- Every spectral point is an ACTUAL full-domain eigenvalue. -/
theorem mem_singularHillSpectrum_iff (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    z ∈ singularHillSpectrum q ↔ ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
      singularHillOperator q f = z • singularHillDomainInclusion f :=
  not_mem_singularHillResolventSet_iff q z

/-- The full original resolvent set is open in the spectral parameter. -/
theorem isOpen_singularHillResolventSet (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    IsOpen (singularHillResolventSet q) :=
  isOpen_singularHillJointResolvent.preimage
    ((continuous_const : Continuous (fun _ : ℂ => q)).prodMk continuous_id)

/-- The graph of the actual source operator, embedded in its original base space. -/
def singularHillGraph (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    Set (FourierLebesgueSpace (2:ℝ) (-1) 2 × FourierLebesgueSpace (2:ℝ) (-1) 2) :=
  {p | ∃ f : FourierLebesgueSpace (2:ℝ) 1 2,
    singularHillDomainInclusion f = p.1 ∧
      singularHillOperator q f = p.2}

/-- One actual resolvent gives an exact closed-equation characterization of the physical graph. -/
theorem singularHillGraph_eq (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ)
    (ha : a ∈ singularHillResolventSet q) :
    singularHillGraph q = {p | singularHillBaseResolvent q a (p.2-a • p.1) = p.1} := by
  ext p
  constructor
  · rintro ⟨f,hf,hL⟩
    change singularHillBaseResolvent q a (p.2-a • p.1) = p.1
    rw [← hf, ← hL]
    change singularHillDomainInclusion (singularHillResolventToH1 q a
      (singularHillOperator q f -
        a • singularHillDomainInclusion f)) = singularHillDomainInclusion f
    rw [singularHillResolventToH1_left q a ha f]
  · intro h
    let f := singularHillResolventToH1 q a (p.2-a • p.1)
    change singularHillDomainInclusion f = p.1 at h
    refine ⟨f,h,?_⟩
    have he := singularHillResolventToH1_right q a ha (p.2-a • p.1)
    change singularHillOperator q f -
      a • singularHillDomainInclusion f = p.2-a • p.1 at he
    rw [h] at he
    exact sub_left_inj.mp he

/-- The source unbounded operator is closed on its full original H1 domain. -/
theorem isClosed_singularHillGraph (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    IsClosed (singularHillGraph q) := by
  obtain ⟨a,ha⟩ := singularHillResolventSet_nonempty q
  rw [singularHillGraph_eq q a ha]
  exact isClosed_eq ((singularHillBaseResolvent q a).continuous.comp
    (continuous_snd.sub (continuous_fst.const_smul a))) continuous_fst

/-- The actual physical eigen-equation transports to the compact base resolvent. -/
theorem singularHillBaseResolvent_eigenvector (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularHillResolventSet q) (hza : z ≠ a)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator q f =
      z • singularHillDomainInclusion f) :
    singularHillBaseResolvent q a (singularHillDomainInclusion f) =
      (z-a)⁻¹ • singularHillDomainInclusion f := by
  have h := singularHillResolventToH1_left q a ha f
  rw [hf, ← sub_smul, map_smul] at h
  have he := congrArg (fun v => (z-a)⁻¹ • v) h
  rw [inv_smul_smul₀ (sub_ne_zero.mpr hza)] at he
  change singularHillDomainInclusion
    (singularHillResolventToH1 q a (singularHillDomainInclusion f)) = _
  rw [he, map_smul]

/-- Every physical spectral point becomes a nonzero eigenvalue of the actual compact resolvent. -/
theorem singularHillSpectrum_compact_eigenvalue (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularHillResolventSet q) (hz : z ∈ singularHillSpectrum q) :
    Module.End.HasEigenvalue (singularHillBaseResolvent q a).toLinearMap (z-a)⁻¹ := by
  have hza : z ≠ a := by rintro rfl; exact hz ha
  obtain ⟨f,hf0,hf⟩ := (mem_singularHillSpectrum_iff q z).mp hz
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := singularHillDomainInclusion f)
  refine ⟨Module.End.mem_eigenspace_iff.mpr
    (singularHillBaseResolvent_eigenvector q a z ha hza f hf), ?_⟩
  intro h
  apply hf0
  apply singularHillDomainInclusion_injective
  simpa only [map_zero] using h

/-- Each bounded spectral region contains only finitely many actual physical eigenvalues. -/
theorem finite_singularHillSpectrum_norm_le (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (R : ℝ) :
    Set.Finite {z : ℂ | z ∈ singularHillSpectrum q ∧ ‖z‖ ≤ R} := by
  obtain ⟨a,ha⟩ := singularHillResolventSet_nonempty q
  let B := max R 0 + ‖a‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let S := {μ : ℂ | Module.End.HasEigenvalue
    (singularHillBaseResolvent q a).toLinearMap μ ∧ B⁻¹ ≤ ‖μ‖}
  have hS : Set.Finite S := CompactSpectrum.finite_eigenvalues_norm_ge
    (singularHillBaseResolvent q a) (isCompactOperator_singularHillBaseResolvent q a)
      (inv_pos.mpr hB)
  have hi : Function.Injective (fun z : ℂ => (z-a)⁻¹) := by
    intro z y h
    exact sub_left_inj.mp (inv_injective h)
  apply (hS.preimage hi.injOn).subset
  rintro z ⟨hz,hzR⟩
  refine ⟨singularHillSpectrum_compact_eigenvalue q a z ha hz, ?_⟩
  rw [norm_inv]
  have hza : z-a ≠ 0 := sub_ne_zero.mpr (by rintro rfl; exact hz ha)
  apply inv_anti₀ (norm_pos_iff.mpr hza)
  exact (norm_sub_le _ _).trans (by dsimp [B]; linarith [le_max_left R 0])

/-- The source unbounded operator is closed in the standard partial-linear-map API. -/
theorem isClosed_singularHillPartialOperator (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    (singularHillPartialOperator q).IsClosed := by
  change IsClosed ((singularHillPartialOperator
    q).graph :
      Set (FourierLebesgueSpace (2:ℝ) (-1) 2 × FourierLebesgueSpace (2:ℝ) (-1) 2))
  rw [singularHillPartialOperator_graph]
  exact isClosed_singularHillGraph q

/-- Original physical reality makes the ENTIRE actual H-minus-one spectrum real. -/
theorem singularHillSpectrum_im_zero_of_real (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : q.val = q.val.conjugate) (z : ℂ) (hz : z ∈ singularHillSpectrum q) : z.im = 0 := by
  obtain ⟨f, hf0, hf⟩ := (mem_singularHillSpectrum_iff q z).mp hz
  exact singularHill_eigenvalue_im_eq_zero q hq z f hf0 hf

/-- The original full spectrum agrees exactly with every verified endpoint realization. -/
theorem singularHillSpectrum_endpoint (r : ℝ) (hr : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    singularHillSpectrum (endpointHillHminusOne SpectralWeight.one r hr q) =
      endpointHillSpectrum r hr q := rfl

end NLS.KdV
