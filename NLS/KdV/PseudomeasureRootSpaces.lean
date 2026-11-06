import NLS.KdV.PseudomeasureSpectrum
import NLS.KdV.SingularHillRootSpace
import NLS.KdV.PseudomeasureEllipticRegularity
import NLS.FunctionalAnalysis.CompactGeneralized

/-! # Full algebraic root spaces of the original endpoint Hill operator

Every actual finite root-chain level and the full physical algebraic root
space are transported exactly to one actual compact base resolvent. They
are finite dimensional and stabilize after finitely many steps. No equality
with the analytic order of the two-mode determinant is inferred here.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open NLS.FunctionalAnalysis

/-- The actual full original physical pencil at a resolvent point, as a Banach isomorphism. -/
def endpointHillPencilEquiv (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) :
    FourierLebesgueSpace (2:ℝ) 1 2 ≃L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  ContinuousLinearEquiv.ofBijective
    (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) -
      a • singularHillDomainInclusion)
        (LinearMap.ker_eq_bot.mpr ha.1) (LinearMap.range_eq_top.mpr ha.2)

theorem endpointHillPencilEquiv_apply (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    endpointHillPencilEquiv r hr1 q a ha f =
      singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
        a • singularHillDomainInclusion f := rfl

/-- The inverse is the already constructed actual original-domain resolvent. -/
theorem endpointHillPencilEquiv_symm (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) (g : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    (endpointHillPencilEquiv r hr1 q a ha).symm g = endpointHillResolventToH1 r hr1 q a g := by
  apply (endpointHillPencilEquiv r hr1 q a ha).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, endpointHillPencilEquiv_apply]
  exact (endpointHillResolventToH1_right r hr1 q a ha g).symm

/-- The generic base resolvent is the exact original compact H-minus-one resolvent. -/
theorem pencilResolvent_endpointHillPencilEquiv (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) :
    pencilResolvent singularHillDomainInclusion.toLinearMap
      (endpointHillPencilEquiv r hr1 q a ha).toLinearEquiv =
        (endpointHillBaseResolvent r hr1 q a).toLinearMap := by
  ext g
  change singularHillDomainInclusion ((endpointHillPencilEquiv r hr1 q a ha).symm g) = _
  rw [endpointHillPencilEquiv_symm]
  rfl

/-- The original physical pencil is exactly the spectral shift of this domain-to-base isomorphism. -/
theorem endpointHillPencil_eq_resolvent_shift (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a z : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) :
    (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) -
      z • singularHillDomainInclusion).toLinearMap =
      (endpointHillPencilEquiv r hr1 q a ha).toLinearMap -
        (z-a) • singularHillDomainInclusion.toLinearMap := by
  ext f
  change singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
    z • singularHillDomainInclusion f =
      endpointHillPencilEquiv r hr1 q a ha f - (z-a) • singularHillDomainInclusion f
  rw [endpointHillPencilEquiv_apply, sub_smul]
  abel

/-- Every actual finite physical root-chain level equals the corresponding compact-resolvent generalized eigenspace. -/
theorem endpointHillRootSpace_eq_resolvent (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a z : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) (hza : z ≠ a) (n : ℕ) :
    singularHillRootSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z n =
      Module.End.genEigenspace (endpointHillBaseResolvent r hr1 q a).toLinearMap (z-a)⁻¹ n := by
  unfold singularHillRootSpace
  rw [endpointHillPencil_eq_resolvent_shift r hr1 q a z ha]
  have h := pencilRootSpace_eq_resolvent_genEigenspace singularHillDomainInclusion.toLinearMap
    singularHillDomainInclusion_injective (endpointHillPencilEquiv r hr1 q a ha).toLinearEquiv
      (z-a) (sub_ne_zero.mpr hza) n
  rwa [pencilResolvent_endpointHillPencilEquiv] at h

/-- The full physical algebraic root space equals the complete nonzero compact-resolvent generalized eigenspace. -/
theorem endpointHillRootSpaceTop_eq_resolvent (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a z : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) (hza : z ≠ a) :
    singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z =
      Module.End.genEigenspace (endpointHillBaseResolvent r hr1 q a).toLinearMap (z-a)⁻¹ ⊤ := by
  unfold singularHillRootSpaceTop
  rw [endpointHillPencil_eq_resolvent_shift r hr1 q a z ha]
  have h := pencilRootSpaceTop_eq_resolvent_genEigenspace singularHillDomainInclusion.toLinearMap
    singularHillDomainInclusion_injective (endpointHillPencilEquiv r hr1 q a ha).toLinearEquiv
      (z-a) (sub_ne_zero.mpr hza)
  rwa [pencilResolvent_endpointHillPencilEquiv] at h

/-- A physical resolvent point has no nonzero actual algebraic root vectors. -/
theorem endpointHillRootSpaceTop_eq_bot_of_mem_resolvent (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ)
    (hz : z ∈ endpointHillResolventSet r hr1 q) :
    singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z = ⊥ :=
  pencilRootSpaceTop_eq_bot_of_injective singularHillDomainInclusion.toLinearMap
    (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) -
      z • singularHillDomainInclusion).toLinearMap hz.1

/-- Full physical algebraic root spaces are finite dimensional at every complex parameter. -/
theorem finiteDimensional_endpointHillRootSpaceTop (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    FiniteDimensional ℂ (singularHillRootSpaceTop
      (endpointHillHminusOne SpectralWeight.one r hr1 q) z) := by
  obtain ⟨a,ha⟩ := endpointHillResolventSet_nonempty r hr hr1 q
  by_cases hza : z = a
  · subst z
    rw [endpointHillRootSpaceTop_eq_bot_of_mem_resolvent r hr1 q a ha]
    infer_instance
  · rw [endpointHillRootSpaceTop_eq_resolvent r hr1 q a z ha hza]
    exact CompactSpectrum.finiteDimensional_genEigenspace_top
      (endpointHillBaseResolvent r hr1 q a) (isCompactOperator_endpointHillBaseResolvent r hr1 q a)
        (inv_ne_zero (sub_ne_zero.mpr hza))

/-- The full physical algebraic root space is attained at a finite chain length. -/
theorem exists_endpointHillRootSpace_eq_top (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    ∃ N : ℕ, singularHillRootSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z N =
      singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z := by
  obtain ⟨a,ha⟩ := endpointHillResolventSet_nonempty r hr hr1 q
  by_cases hza : z = a
  · subst z
    refine ⟨0,?_⟩
    rw [endpointHillRootSpaceTop_eq_bot_of_mem_resolvent r hr1 q a ha]
    rfl
  · obtain ⟨N,hN⟩ := CompactSpectrum.exists_genEigenspace_eq_top
      (endpointHillBaseResolvent r hr1 q a) (isCompactOperator_endpointHillBaseResolvent r hr1 q a)
        (inv_ne_zero (sub_ne_zero.mpr hza))
    exact ⟨N,by rw [endpointHillRootSpace_eq_resolvent r hr1 q a z ha hza,
      endpointHillRootSpaceTop_eq_resolvent r hr1 q a z ha hza]; exact hN⟩

/-- The actual finite physical algebraic multiplicity, defined from the full original root space. -/
def endpointHillAlgebraicMultiplicity (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) : ℕ :=
  letI := finiteDimensional_endpointHillRootSpaceTop r hr hr1 q z
  Module.finrank ℂ (singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z)

/-- Actual algebraic multiplicity equals that of any actual compact resolvent at the transformed value. -/
theorem endpointHillAlgebraicMultiplicity_eq_resolvent (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a z : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) (hza : z ≠ a) :
    endpointHillAlgebraicMultiplicity r hr hr1 q z = Module.finrank ℂ
      (Module.End.genEigenspace (endpointHillBaseResolvent r hr1 q a).toLinearMap (z-a)⁻¹ ⊤) := by
  unfold endpointHillAlgebraicMultiplicity
  rw [endpointHillRootSpaceTop_eq_resolvent r hr1 q a z ha hza]

/-- The eventual finite root-chain levels all equal the full physical algebraic root space. -/
theorem endpointHillRootSpace_stabilizes (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      singularHillRootSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z n =
        singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z := by
  obtain ⟨N,hN⟩ := exists_endpointHillRootSpace_eq_top r hr hr1 q z
  refine ⟨N,fun n hn => le_antisymm ?_ ?_⟩
  · exact le_iSup (fun n => singularHillRootSpace
      (endpointHillHminusOne SpectralWeight.one r hr1 q) z n) n
  · rw [← hN]
    exact pencilRootSpace_mono _ _ hn

/-- Actual physical algebraic multiplicity is positive exactly on the actual physical spectrum. -/
theorem endpointHillAlgebraicMultiplicity_pos_iff (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    0 < endpointHillAlgebraicMultiplicity r hr hr1 q z ↔ z ∈ endpointHillSpectrum r hr1 q := by
  let := finiteDimensional_endpointHillRootSpaceTop r hr hr1 q z
  constructor
  · intro h
    by_contra hnot
    have hz : z ∈ endpointHillResolventSet r hr1 q := by
      simpa only [endpointHillSpectrum, Set.mem_compl_iff, not_not] using hnot
    unfold endpointHillAlgebraicMultiplicity at h
    rw [endpointHillRootSpaceTop_eq_bot_of_mem_resolvent r hr1 q z hz, finrank_bot] at h
    exact Nat.not_lt_zero _ h
  · intro hz
    obtain ⟨f,hf0,hf⟩ := (mem_endpointHillSpectrum_iff r hr hr1 q z).mp hz
    have hlevel : singularHillDomainInclusion f ∈
        singularHillRootSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z 1 :=
      (mem_singularHillRootSpace_one _ z _).mpr ⟨f,rfl,hf⟩
    have htop : singularHillDomainInclusion f ∈
        singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z :=
      (mem_singularHillRootSpaceTop _ z _).mpr ⟨1,hlevel⟩
    change 0 < Module.finrank ℂ (singularHillRootSpaceTop
      (endpointHillHminusOne SpectralWeight.one r hr1 q) z)
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨singularHillDomainInclusion f,htop⟩,?_⟩
    intro he
    apply hf0
    apply singularHillDomainInclusion_injective
    have h := congrArg Subtype.val he
    change singularHillDomainInclusion f = (0 : FourierLebesgueSpace (2:ℝ) (-1) 2) at h
    simpa only [map_zero] using h

/-- The endpoint realization of an original H1 vector is the same original H-minus-one vector. -/
theorem endpointHillHminusOne_H1EndpointInclusion (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    endpointHillHminusOne SpectralWeight.one r hr1 (H1EndpointInclusion r hr f) =
      singularHillDomainInclusion f := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [endpointHillHminusOne_coefficient, H1EndpointInclusion_apply,
    singularHillDomainInclusion_coefficient]

/-- Every actual physical algebraic root vector has the source's two-order improved endpoint regularity. -/
theorem endpointHillRootSpaceTop_regular (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ)
    (x : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hx : x ∈ singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z) :
    ∃ u : FourierLebesgueSpace (2:ℝ) (-r+2) ⊤, u.val = x.val := by
  obtain ⟨f,g,hf,hg⟩ := exists_H1_chain_rhs_of_mem_singularHillRootSpaceTop _ z x hx
  have hE : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
      z • singularHillDomainInclusion f =
        endpointHillHminusOne SpectralWeight.one r hr1 (H1EndpointInclusion r hr g) := by
    rw [endpointHillHminusOne_H1EndpointInclusion]
    exact hg
  have hm := singularHill_inhomogeneous_memlp r hr hr1 q (H1EndpointInclusion r hr g) z f hE
  have hm' : Memℓp (fun k => (Weight.sobolev (-r+2) k:ℂ)*f.val (mode (-k))) ⊤ := by
    simpa only [SpectralWeight.negativeSobolev_eq_product, SpectralWeight.one_apply, one_mul,
      show -(r-2) = -r+2 by ring] using hm
  let a : WeightedCoeff (Weight.sobolev (-r+2)) ⊤ := ⟨fun k => f.val (mode (-k)),hm'⟩
  refine ⟨(sobolevCoefficients (-r+2) ⊤).symm a,?_⟩
  have hfx : f.val = x.val := by
    simpa only [singularHillDomainInclusion_val] using
      congrArg (fun v : FourierLebesgueSpace (2:ℝ) (-1) 2 => v.val) hf
  rw [← hfx]
  apply Distribution.ext_coefficients
  intro k
  change ((sobolevCoefficients (-r+2) ⊤) ((sobolevCoefficients (-r+2) ⊤).symm a)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]

end NLS.KdV
