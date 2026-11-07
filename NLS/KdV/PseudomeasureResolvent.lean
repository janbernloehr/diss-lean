import NLS.KdV.PseudomeasureFredholm
import NLS.KdV.PseudomeasureZeroCount

/-! # The full original H-minus-one resolvent of the endpoint Hill operator

The operator is the source's unbounded operator on H-minus-one with original
H1 domain. Its full pencil is bijective exactly off its physical eigenvalues.
The high-strip determinant criterion is upgraded from a homogeneous criterion
to full resolvent invertibility. A proved nonempty resolvent and compact
base-space inverse are constructed, without restricting the right-hand side
to the endpoint class.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The full resolvent set of the actual original H1-to-H-minus-one pencil. -/
def endpointHillResolventSet (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) : Set ℂ :=
  {z | Function.Bijective (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) -
    z • singularHillDomainInclusion)}

/-- A fixed free normalization preserves the full original physical resolvent set. -/
theorem mem_endpointHillResolventSet_iff_isUnit (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    z ∈ endpointHillResolventSet r hr1 q ↔ IsUnit (endpointHillNormalizedPencil r hr1 q z) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact endpointHillPencil_bijective_iff_normalized r hr1 q z

/-- The source operator's spectrum is the complement of its full physical resolvent set. -/
def endpointHillSpectrum (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) : Set ℂ :=
  (endpointHillResolventSet r hr1 q)ᶜ

/-- A normalized pencil is injective exactly when its physical eigenspace is zero. -/
theorem endpointHillNormalizedPencil_injective_iff (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    Function.Injective (endpointHillNormalizedPencil r hr1 q z) ↔
      ∀ f : FourierLebesgueSpace (2:ℝ) 1 2,
        singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
          z • singularHillDomainInclusion f → f = 0 := by
  constructor
  · intro hi f hf
    apply hi
    rw [map_zero]
    exact (endpointHillNormalizedPencil_apply_eq_zero_iff r hr1 q z f).mpr hf
  · intro h f g hfg
    apply sub_eq_zero.mp
    apply h
    apply (endpointHillNormalizedPencil_apply_eq_zero_iff r hr1 q z (f-g)).mp
    rw [map_sub, hfg, sub_self]

/-- At every complex parameter, the full singular spectrum consists exactly of actual eigenvalues. -/
theorem mem_endpointHillSpectrum_iff (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    z ∈ endpointHillSpectrum r hr1 q ↔
      ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
        singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
          z • singularHillDomainInclusion f := by
  change (z ∉ endpointHillResolventSet r hr1 q) ↔ _
  rw [mem_endpointHillResolventSet_iff_isUnit, ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · intro h
    by_contra hn
    have hi : Function.Injective (endpointHillNormalizedPencil r hr1 q z) := by
      apply (endpointHillNormalizedPencil_injective_iff r hr1 q z).mpr
      intro f hf
      by_contra hf0
      exact hn ⟨f,hf0,hf⟩
    exact h (endpointHillNormalizedPencil_bijective_of_injective r hr hr1 q z hi)
  · rintro ⟨f,hf0,hf⟩ h
    apply hf0
    exact (endpointHillNormalizedPencil_injective_iff r hr1 q z).mp h.1 f hf

/-- On the corrected high strip, the actual determinant detects full resolvent failure. -/
theorem mem_endpointHillSpectrum_iff_determinant (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    z ∈ endpointHillSpectrum r hr1 q ↔ endpointReducedDeterminant r hr hr1 n (q,z) = 0 :=
  (mem_endpointHillSpectrum_iff r hr hr1 q z).trans
    (endpointReducedDeterminant_eq_zero_iff r hr hr1 n hn (q,z) hz hs).symm

/-- A total original-domain resolvent family, equal to the actual inverse on the resolvent set. -/
def endpointHillResolventToH1 (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  (Ring.inverse (endpointHillNormalizedPencil r hr1 q z)).comp singularHillFreeInverse

/-- The original-domain resolvent recovers every H1 vector from its full physical pencil image. -/
theorem endpointHillResolventToH1_left (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ)
    (hz : z ∈ endpointHillResolventSet r hr1 q) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    endpointHillResolventToH1 r hr1 q z
      (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
        z • singularHillDomainInclusion f) = f := by
  have hu := (mem_endpointHillResolventSet_iff_isUnit r hr1 q z).mp hz
  have h := congrArg (fun T : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ]
    FourierLebesgueSpace (2:ℝ) 1 2 => T f)
      (Ring.inverse_mul_cancel (endpointHillNormalizedPencil r hr1 q z) hu)
  exact h

/-- Every original H-minus-one right-hand side has a solution, with no endpoint regularity premise. -/
theorem endpointHillResolventToH1_right (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ)
    (hz : z ∈ endpointHillResolventSet r hr1 q) (g : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q)
        (endpointHillResolventToH1 r hr1 q z g) -
      z • singularHillDomainInclusion (endpointHillResolventToH1 r hr1 q z g) = g := by
  have hu := (mem_endpointHillResolventSet_iff_isUnit r hr1 q z).mp hz
  apply singularHillFreeIsomorphism.symm.injective
  exact congrArg (fun T : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ]
    FourierLebesgueSpace (2:ℝ) 1 2 => T (singularHillFreeInverse g))
      (Ring.mul_inverse_cancel (endpointHillNormalizedPencil r hr1 q z) hu)

/-- The actual resolvent acting on the original H-minus-one base space. -/
def endpointHillBaseResolvent (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  singularHillDomainInclusion.comp (endpointHillResolventToH1 r hr1 q z)

/-- The full base-space resolvent is compact in the original H-minus-one norm. -/
theorem isCompactOperator_endpointHillBaseResolvent (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    IsCompactOperator (endpointHillBaseResolvent r hr1 q z) :=
  isCompactOperator_singularHillDomainInclusion.comp_clm (endpointHillResolventToH1 r hr1 q z)

/-- The actual original-domain resolvent is norm analytic wherever the physical pencil is invertible. -/
theorem analyticAt_endpointHillResolventToH1 (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ)
    (hz : z ∈ endpointHillResolventSet r hr1 q) :
    AnalyticAt ℂ (endpointHillResolventToH1 r hr1 q) z := by
  have hu := (mem_endpointHillResolventSet_iff_isUnit r hr1 q z).mp hz
  have hA := analyticAt_endpointHillNormalizedPencil_spectral r hr1 q z
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ) _ hu).comp
    (f := endpointHillNormalizedPencil r hr1 q) hA
  exact SchurComplement.analyticAt_compCLM hi analyticAt_const

/-- The physical resolvent set is open in the spectral parameter. -/
theorem isOpen_endpointHillResolventSet (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    IsOpen (endpointHillResolventSet r hr1 q) := by
  have hc : Continuous (endpointHillNormalizedPencil r hr1 q) :=
    continuous_iff_continuousAt.mpr (fun z => (analyticAt_endpointHillNormalizedPencil_spectral r hr1 q z).continuousAt)
  have he : endpointHillResolventSet r hr1 q =
      endpointHillNormalizedPencil r hr1 q ⁻¹' {T | IsUnit T} := by
    ext z
    exact mem_endpointHillResolventSet_iff_isUnit r hr1 q z
  rw [he]
  exact Units.isOpen.preimage hc

/-- A concrete point in each sufficiently high strip belongs to the full physical resolvent set. -/
theorem endpointHill_resolvent_point (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    (freeHillValue n:ℂ)+(n:ℂ)*Complex.I ∈ endpointHillResolventSet r hr1 q := by
  let z : ℂ := (freeHillValue n:ℂ)+(n:ℂ)*Complex.I
  have hz : z ∈ reducedHillStrip n := by
    change |z.re-freeHillValue n| ≤ 6*(n:ℝ)
    simp [z]
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnorm : ‖z-(freeHillValue n:ℂ)‖ = n := by simp [z]
  by_contra hnot
  have he : endpointReducedDeterminant r hr hr1 n (q,z) = 0 :=
    (mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn z hz q hs).mp hnot
  have hL := endpointReducedDeterminant_zero_localization r hr hr1 n hn q hs z hz he
  rw [hnorm] at hL
  have hS : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  linarith

/-- Every complex endpoint potential has a nonempty full original H-minus-one resolvent set. -/
theorem endpointHillResolventSet_nonempty (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    (endpointHillResolventSet r hr1 q).Nonempty := by
  obtain ⟨N,hN,hcut⟩ := exists_endpointHill_cutoff r hr1 ‖q‖
  exact ⟨_, endpointHill_resolvent_point r hr hr1 N hN q (hcut N le_rfl)⟩

/-- The actual original-domain inverses satisfy the full resolvent identity. -/
theorem endpointHillResolventToH1_sub_apply (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z a : ℂ)
    (hz : z ∈ endpointHillResolventSet r hr1 q) (ha : a ∈ endpointHillResolventSet r hr1 q)
    (g : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    endpointHillResolventToH1 r hr1 q z g - endpointHillResolventToH1 r hr1 q a g =
      (z-a) • endpointHillResolventToH1 r hr1 q z
        (singularHillDomainInclusion (endpointHillResolventToH1 r hr1 q a g)) := by
  let f := endpointHillResolventToH1 r hr1 q a g
  have hP := endpointHillResolventToH1_right r hr1 q a ha g
  have hcross : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
      z • singularHillDomainInclusion f = g + (a-z) • singularHillDomainInclusion f := by
    change singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
      a • singularHillDomainInclusion f = g at hP
    rw [← hP]
    module
  have h := endpointHillResolventToH1_left r hr1 q z hz f
  rw [hcross, map_add, map_smul] at h
  change endpointHillResolventToH1 r hr1 q z g - f = _
  rw [← h]
  module

/-- The compact original H-minus-one resolvents obey the physical resolvent identity. -/
theorem endpointHillBaseResolvent_sub (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z a : ℂ)
    (hz : z ∈ endpointHillResolventSet r hr1 q) (ha : a ∈ endpointHillResolventSet r hr1 q) :
    endpointHillBaseResolvent r hr1 q z - endpointHillBaseResolvent r hr1 q a =
      (z-a) • (endpointHillBaseResolvent r hr1 q z).comp (endpointHillBaseResolvent r hr1 q a) := by
  apply ContinuousLinearMap.ext
  intro g
  have h := congrArg singularHillDomainInclusion
    (endpointHillResolventToH1_sub_apply r hr1 q z a hz ha g)
  rw [map_sub, map_smul] at h
  exact h

end NLS.KdV
