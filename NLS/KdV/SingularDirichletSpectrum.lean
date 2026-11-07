import NLS.KdV.SingularDirichletResolventFamily

/-! # The complete native Dirichlet spectrum

The entire zero-trace H1 domain and its full continuous dual are retained.
The Fredholm alternative excludes non-eigenvalue spectrum. Compactness of
an actual full-base inverse gives local finiteness for every complex source.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
local instance dirichletSpectrumH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletSpectrumH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletSpectrumBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletSpectrumBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- The full spectrum on the native H-minus-one base. -/
def singularDirichletSpectrum (q : FourierLebesgueSpace (2:ℝ) (-1) 2) : Set ℂ :=
  (singularDirichletResolventSet q)ᶜ

/-- There is no spectrum beyond the genuine native point eigenvalues. -/
theorem mem_singularDirichletSpectrum_iff
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    z ∈ singularDirichletSpectrum q ↔ ∃ f : UnitDirichletH1, f ≠ 0 ∧
      singularDirichletOperator q f = z • singularDirichletDomainInclusion f :=
  not_mem_singularDirichletResolventSet_iff q z

/-- Full spectrum is exactly the independently normalized characteristic zero set. -/
theorem mem_singularDirichletSpectrum_source_iff (q : PeriodOneHminusOne) (z : ℂ) :
    z ∈ singularDirichletSpectrum (periodOneOriginal q) ↔ hillHminusDirichlet q z = 0 :=
  (mem_singularDirichletSpectrum_iff (periodOneOriginal q) z).trans
    (hillHminusDirichlet_eq_zero_iff_native_eigen q z).symm

/-- The full native resolvent set is open in energy. -/
theorem isOpen_singularDirichletResolventSet (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    IsOpen (singularDirichletResolventSet q) :=
  isOpen_singularDirichletJointResolvent.preimage
    ((continuous_const : Continuous (fun _ : ℂ => q)).prodMk continuous_id)

/-- The full native spectrum is closed. -/
theorem isClosed_singularDirichletSpectrum (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    IsClosed (singularDirichletSpectrum q) :=
  (isOpen_singularDirichletResolventSet q).isClosed_compl

/-- The actual physical eigen-equation transports to the compact base resolvent. -/
theorem singularDirichletBaseResolvent_eigenvector (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) (hza : z ≠ a)
    (f : UnitDirichletH1)
    (hf : singularDirichletOperator q f =
      z • singularDirichletDomainInclusion f) :
    singularDirichletBaseResolvent q a (singularDirichletDomainInclusion f) =
      (z-a)⁻¹ • singularDirichletDomainInclusion f := by
  have h := singularDirichletResolventToH1_left q a ha f
  rw [hf] at h
  have hs : z • singularDirichletDomainInclusion f-a • singularDirichletDomainInclusion f =
      (z-a) • singularDirichletDomainInclusion f := by module
  rw [hs, map_smul] at h
  have he := congrArg (fun v => (z-a)⁻¹ • v) h
  rw [inv_smul_smul₀ (sub_ne_zero.mpr hza)] at he
  change singularDirichletDomainInclusion
    (singularDirichletResolventToH1 q a (singularDirichletDomainInclusion f)) = _
  rw [he, map_smul]

/-- Every physical spectral point becomes a nonzero eigenvalue of the actual compact resolvent. -/
theorem singularDirichletSpectrum_compact_eigenvalue (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) (hz : z ∈ singularDirichletSpectrum q) :
    Module.End.HasEigenvalue (singularDirichletBaseResolvent q a).toLinearMap (z-a)⁻¹ := by
  have hza : z ≠ a := by rintro rfl; exact hz ha
  obtain ⟨f,hf0,hf⟩ := (mem_singularDirichletSpectrum_iff q z).mp hz
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := singularDirichletDomainInclusion f)
  refine ⟨Module.End.mem_eigenspace_iff.mpr
    (singularDirichletBaseResolvent_eigenvector q a z ha hza f hf), ?_⟩
  intro h
  apply hf0
  apply singularDirichletDomainInclusion_injective
  simpa only [map_zero] using h

/-- Each bounded spectral region contains only finitely many actual physical eigenvalues. -/
theorem finite_singularDirichletSpectrum_norm_le (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (R : ℝ) :
    Set.Finite {z : ℂ | z ∈ singularDirichletSpectrum q ∧ ‖z‖ ≤ R} := by
  obtain ⟨a,ha⟩ := singularDirichletResolventSet_nonempty q
  let B := max R 0 + ‖a‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let S := {μ : ℂ | Module.End.HasEigenvalue
    (singularDirichletBaseResolvent q a).toLinearMap μ ∧ B⁻¹ ≤ ‖μ‖}
  have hS : Set.Finite S := CompactSpectrum.finite_eigenvalues_norm_ge
    (singularDirichletBaseResolvent q a) (isCompactOperator_singularDirichletBaseResolvent q a)
      (inv_pos.mpr hB)
  have hi : Function.Injective (fun z : ℂ => (z-a)⁻¹) := by
    intro z y h
    exact sub_left_inj.mp (inv_injective h)
  apply (hS.preimage hi.injOn).subset
  rintro z ⟨hz,hzR⟩
  refine ⟨singularDirichletSpectrum_compact_eigenvalue q a z ha hz, ?_⟩
  rw [norm_inv]
  have hza : z-a ≠ 0 := sub_ne_zero.mpr (by rintro rfl; exact hz ha)
  apply inv_anti₀ (norm_pos_iff.mpr hza)
  exact (norm_sub_le _ _).trans (by dsimp [B]; linarith [le_max_left R 0])

/-- Reality of the original potential makes the full native spectrum real. -/
theorem singularDirichletSpectrum_im_zero_of_real
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (hq : q.val = q.val.conjugate)
    (z : ℂ) (hz : z ∈ singularDirichletSpectrum q) : z.im = 0 := by
  obtain ⟨f, hf, he⟩ := (mem_singularDirichletSpectrum_iff q z).mp hz
  exact singularDirichlet_eigenvalue_im_eq_zero q hq z f hf he

end NLS.KdV
