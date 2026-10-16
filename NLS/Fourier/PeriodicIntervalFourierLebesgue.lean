import NLS.Fourier.PeriodicFourierLebesgueEndpoints
import NLS.Fourier.PhysicalIntervalL2
import NLS.Fourier.ArbitraryPeriodFourierLebesgue
import NLS.SequenceSpaces.ExponentEmbedding

/-!
# Lemma A.9: interval functions as original Fourier–Lebesgue distributions

For every positive physical period, the source's subcritical and half-regularity
hypotheses place the actual normalized interval functional in the original FLᑫ
space. No endpoint matching is assumed. At zero regularity, ordinary L² data
suffices, including target two and infinity, with the exact L^(-1/2) bound.

The generic coefficient constructor is identified with integration against the
original input on every smooth test. `l2OriginalEmbedding` uses the normalized
L² class stored on the reference circle; `intervalPullback L` recovers its
physical representative, and `ofIntervalL2` accepts arbitrary interval data.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

/-- Ordinary square-integrable interval data defines an original distribution. -/
theorem intervalIntegrable_of_memLp_two {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) : IntervalIntegrable f volume 0 L :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt (Fact.out : 0 < L))).mpr
    (hf.integrable (by norm_num))

/-- Lemma A.9 for 0≤s<1/2, with no fractional-energy assumption at s=0. -/
theorem ofL1_mem_fourierLebesgue_of_intervalSobolev {s q : ℝ}
    (hs : 0 ≤ s) (hs₁ : s < 1/2) (hq : 1/(s+1/2) < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : 0 < s → fractionalIntervalEnergy s L f < ⊤) :
    Distribution.ofL1 f (intervalIntegrable_of_memLp_two hf) ∈
      periodicFourierLebesgueSubmodule Weight.one (ENNReal.ofReal q) := by
  change Memℓp (fun n : ℤ => (Weight.one n : ℂ) *
    Distribution.ofL1 f (intervalIntegrable_of_memLp_two hf) (mode (-n))) _
  simpa only [Weight.one_apply,Complex.ofReal_one,one_mul,Distribution.ofL1_coefficient] using
    memlp_intervalFourierCoefficient_of_nonneg (Fact.out : 0 < L) hs hs₁ hq f hf hE

/-- The separate half-regularity assertion of A.9 for every finite q>1. -/
theorem ofL1_mem_fourierLebesgue_of_intervalHalfSobolev {q : ℝ} (hq : 1 < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy (1/2) L f < ⊤) :
    Distribution.ofL1 f (intervalIntegrable_of_memLp_two hf) ∈
      periodicFourierLebesgueSubmodule Weight.one (ENNReal.ofReal q) := by
  change Memℓp (fun n : ℤ => (Weight.one n : ℂ) *
    Distribution.ofL1 f (intervalIntegrable_of_memLp_two hf) (mode (-n))) _
  simpa only [Weight.one_apply,Complex.ofReal_one,one_mul,Distribution.ofL1_coefficient] using
    memlp_intervalFourierCoefficient_of_half (Fact.out : 0 < L) hq f hf hE

/-- Ordinary interval L² data belongs to every original FLᑫ with q≥2, including infinity. -/
theorem ofL1_mem_fourierLebesgue_of_intervalL2 {q : ℝ≥0∞} (hq : 2 ≤ q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) :
    Distribution.ofL1 f (intervalIntegrable_of_memLp_two hf) ∈ periodicFourierLebesgueSubmodule Weight.one q := by
  change Memℓp (fun n : ℤ => (Weight.one n : ℂ) *
    Distribution.ofL1 f (intervalIntegrable_of_memLp_two hf) (mode (-n))) _
  simpa only [Weight.one_apply,Complex.ofReal_one,one_mul,Distribution.ofL1_coefficient] using
    memlp_intervalFourierCoefficient_of_memLp (Fact.out : 0 < L) hq f hf

namespace PeriodicFourierLebesgue
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Realize proved interval coefficient membership in the original distribution space. -/
def ofIntervalFourierCoefficients (f : ℝ → ℂ)
    (hm : Memℓp (intervalFourierCoefficient L f) p) : PeriodicFourierLebesgue L Weight.one p :=
  (unweightedCoefficients p).symm (intervalFourierCoefficients L f hm)

/-- The constructor retains every actual normalized physical Fourier integral. -/
theorem ofIntervalFourierCoefficients_coefficient (f : ℝ → ℂ)
    (hm : Memℓp (intervalFourierCoefficient L f) p) (n : ℤ) :
    (ofIntervalFourierCoefficients f hm).val (mode (-n)) = intervalFourierCoefficient L f n := by
  rw [← unweightedCoefficients_apply,ofIntervalFourierCoefficients,LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- For integrable input, coefficient synthesis is its original interval functional. -/
theorem ofIntervalFourierCoefficients_val (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume 0 L) (hm : Memℓp (intervalFourierCoefficient L f) p) :
    (ofIntervalFourierCoefficients f hm).val = Distribution.ofL1 f hf := by
  apply Distribution.ext_coefficients
  intro n
  rw [ofIntervalFourierCoefficients_coefficient,Distribution.ofL1_coefficient]

/-- The action on every original smooth test has exactly the factor 1/L. -/
theorem ofIntervalFourierCoefficients_apply (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume 0 L) (hm : Memℓp (intervalFourierCoefficient L f) p)
    (g : SmoothPeriodicTest L) :
    (ofIntervalFourierCoefficients f hm).val g = (L:ℂ)⁻¹ * ∫ x in (0:ℝ)..L, f x*g x := by
  rw [ofIntervalFourierCoefficients_val f hf,Distribution.ofL1_apply]

/-- The original-space norm is exactly the norm of the actual coefficient sequence. -/
theorem norm_ofIntervalFourierCoefficients (f : ℝ → ℂ)
    (hm : Memℓp (intervalFourierCoefficient L f) p) :
    ‖ofIntervalFourierCoefficients f hm‖ = ‖intervalFourierCoefficients L f hm‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- Embed ordinary interval L² data into every original FLᑫ with q≥2. -/
def ofIntervalL2 {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) : PeriodicFourierLebesgue L Weight.one q :=
  ofIntervalFourierCoefficients f (memlp_intervalFourierCoefficient_of_memLp (Fact.out : 0 < L) hq f hf)

/-- The L² construction represents the original interval function. -/
theorem ofIntervalL2_val {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) :
    (ofIntervalL2 hq f hf).val = Distribution.ofL1 f (intervalIntegrable_of_memLp_two hf) :=
  ofIntervalFourierCoefficients_val f _ _

/-- The zero-regularity bound retains exactly the physical factor L^(-1/2). -/
theorem norm_ofIntervalL2_le {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) :
    ‖ofIntervalL2 hq f hf‖ ≤ Real.sqrt (1 / L) * Real.sqrt (intervalSquareEnergy L f).toReal := by
  rw [ofIntervalL2,norm_ofIntervalFourierCoefficients]
  exact norm_intervalFourierCoefficients_of_memLp_le (Fact.out : 0 < L) hq f hf _

/-- The original-space A.9 constructor, including zero regularity. -/
def ofIntervalSobolev {s q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 ≤ s) (hs₁ : s < 1/2) (hq : 1/(s+1/2) < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : 0 < s → fractionalIntervalEnergy s L f < ⊤) : PeriodicFourierLebesgue L Weight.one (ENNReal.ofReal q) :=
  ofIntervalFourierCoefficients f
    (memlp_intervalFourierCoefficient_of_nonneg (Fact.out : 0 < L) hs hs₁ hq f hf hE)

/-- The subcritical constructor preserves the original interval functional. -/
theorem ofIntervalSobolev_val {s q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 ≤ s) (hs₁ : s < 1/2) (hq : 1/(s+1/2) < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : 0 < s → fractionalIntervalEnergy s L f < ⊤) :
    (ofIntervalSobolev hs hs₁ hq f hf hE).val = Distribution.ofL1 f (intervalIntegrable_of_memLp_two hf) :=
  ofIntervalFourierCoefficients_val f _ _

/-- The original-space constructor for the separate half-regularity conclusion. -/
def ofIntervalHalfSobolev {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy (1/2) L f < ⊤) : PeriodicFourierLebesgue L Weight.one (ENNReal.ofReal q) :=
  ofIntervalFourierCoefficients f (memlp_intervalFourierCoefficient_of_half (Fact.out : 0 < L) hq f hf hE)

/-- The half-regularity constructor preserves the original interval functional. -/
theorem ofIntervalHalfSobolev_val {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy (1/2) L f < ⊤) :
    (ofIntervalHalfSobolev hq f hf hE).val = Distribution.ofL1 f (intervalIntegrable_of_memLp_two hf) :=
  ofIntervalFourierCoefficients_val f _ _

/-- The continuous injection from normalized physical L² classes into original FLᑫ. -/
def l2OriginalEmbedding {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q) :
    CircleL2 →L[ℂ] PeriodicFourierLebesgue L Weight.one q :=
  (unweightedCoefficients q).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.exponentInclusion hq).comp fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The normalized L² map uses the actual physical interval Fourier coefficients. -/
theorem l2OriginalEmbedding_coefficient {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q)
    (f : CircleL2) (n : ℤ) : (l2OriginalEmbedding (L := L) hq f).val (mode (-n)) =
      intervalFourierCoefficient L (intervalPullback L f) n := by
  rw [← unweightedCoefficients_apply]
  change unweightedCoefficients q ((unweightedCoefficients q).symm
    (Coeff.exponentInclusion hq (fourierBasis.repr f))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply,Coeff.exponentInclusion_apply,fourierBasis_repr,
    intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L)]

/-- The normalized L² map represents its physical interval pullback. -/
theorem l2OriginalEmbedding_val {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q) (f : CircleL2) :
    (l2OriginalEmbedding (L := L) hq f).val = Distribution.ofL1 (intervalPullback L f)
      (intervalIntegrable_of_memLp_two (memLp_intervalPullback (Fact.out : 0 < L) f)) := by
  apply Distribution.ext_coefficients
  intro n
  rw [l2OriginalEmbedding_coefficient,Distribution.ofL1_coefficient]

/-- The normalized L² map is injective, including the infinity target. -/
theorem l2OriginalEmbedding_injective {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q) :
    Function.Injective (l2OriginalEmbedding (L := L) hq) :=
  (unweightedCoefficients q).symm.injective.comp
    ((Coeff.exponentInclusion_injective hq).comp fourierBasis.repr.injective)

/-- The L² map is contractive in the normalized circle norm. -/
theorem norm_l2OriginalEmbedding_le {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q) (f : CircleL2) :
    ‖l2OriginalEmbedding (L := L) hq f‖ ≤ ‖f‖ := by
  change ‖(unweightedCoefficients q).symm (Coeff.exponentInclusion hq (fourierBasis.repr f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (Coeff.norm_exponentInclusion_le hq _).trans_eq (fourierBasis.repr.norm_map f)

/-- Passing arbitrary input through its L² quotient gives the same original distribution. -/
theorem l2OriginalEmbedding_intervalL2Class {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) :
    l2OriginalEmbedding (L := L) hq (intervalL2Class (Fact.out : 0 < L) f hf) = ofIntervalL2 hq f hf := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  rw [l2OriginalEmbedding_coefficient,intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L),
    fourierCoeff_intervalL2Class,ofIntervalL2,ofIntervalFourierCoefficients_coefficient]

end PeriodicFourierLebesgue

end NLS.Fourier
