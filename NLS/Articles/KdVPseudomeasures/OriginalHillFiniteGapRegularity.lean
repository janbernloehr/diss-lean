import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapMiura
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapApproximation
import NLS.SequenceSpaces.PeriodOneMiuraSobolevRegularity
import NLS.KdV.PeriodOneOriginalPositiveRegularity
import NLS.Fourier.PeriodOneSmoothSynthesis
import NLS.Fourier.PeriodOneSynthesisAlgebra
import NLS.SequenceSpaces.WeightedSingle

/-! Genuine finite-gap regularity of the ACTUAL original native Hill source.
Actual shifted real Miura lifts have ACTUAL Dirac finite-gap data, so the
verified real Dirac all-order bootstrap and the actual Miura formula prove
all Sobolev orders and an exact smooth physical representative. -/
noncomputable section
open Set Complex NLS.KdV NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.Articles.KdVPseudomeasures

/-- Every ACTUAL native Hill finite-gap potential has every nonnegative
Sobolev order, with the SAME full original coefficient sequence. -/
theorem hillRealFiniteGap_mem_all_sobolev (q : HillRealMeanZeroSource)
    (hf : q ∈ hillRealFiniteGapLocus) (s : ℝ) (hs : 0 ≤ s) :
    Memℓp (fun k => (Weight.sobolev s k:ℂ)*(hillRealMeanZeroInclusion q).val k) 2 := by
  obtain ⟨c,_,_,u,hu,_⟩ := exists_real_periodOneMiura_shift_outside_spectrum
    (hillRealMeanZeroInclusion q) q.property 0
  have hu' : periodOneMiura u.val=hillRealMeanZeroInclusion q+
      periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ)) := by
    simpa only [Complex.ofReal_pow] using hu
  have hreg := periodOneMiura_mem_all_sobolev u.val
    (fun t ht => hillRealFiniteGap_miura_mem_all_sobolev q hf u (c^2) hu' t ht) s hs
  have hc : Memℓp (fun k => (Weight.sobolev s k:ℂ)*
      (periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2))).val k) 2 := by
    have h := (WeightedCoeff.single (p := 2) (Weight.sobolev s) 0 ((c:ℂ)^2)).property
    change Memℓp (fun k => (Weight.sobolev s k:ℂ)*(WeightedCoeff.single (p := 2) (Weight.sobolev s) 0 ((c:ℂ)^2)).val k) 2 at h
    simpa only [WeightedCoeff.single_val,periodOneL2Inclusion_apply,lp.single_apply] using h
  convert! hreg.sub hc using 1
  funext k
  change (Weight.sobolev s k:ℂ)*(hillRealMeanZeroInclusion q).val k=
    (Weight.sobolev s k:ℂ)*(periodOneMiura u.val).val k-
      (Weight.sobolev s k:ℂ)*(periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2))).val k
  have he : (periodOneMiura u.val).val k=(hillRealMeanZeroInclusion q).val k+
      (periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2))).val k := by rw [hu]; rfl
  rw [he]
  ring

/-- Every original physical finite-gap potential has a representative in
EVERY original positive Sobolev space; the ENTIRE distribution is unchanged. -/
theorem exists_originalHillFiniteGap_regular_realization (q : OriginalHminusOnePotential)
    (hf : originalHillRealMeanZeroSource q ∈ hillRealFiniteGapLocus) (s : ℝ) (hs : 0 ≤ s) :
    ∃ Q : NLS.Fourier.FourierLebesgueSpace (2:ℝ) s 2,
      Q.val=q.val.val := by
  have hreg := hillRealFiniteGap_mem_all_sobolev (originalHillRealMeanZeroSource q) hf s hs
  rw [originalHillRealMeanZeroSource_inclusion] at hreg
  obtain ⟨Q,hQ⟩ := exists_periodOneOriginal_positive_regular_realization
    (originalPeriodOneCoefficients q) s hs hreg
  exact ⟨Q,hQ.trans (congrArg Subtype.val (periodOneOriginal_originalPeriodOneCoefficients q))⟩

/-- An ACTUAL native finite-gap source has a globally smooth period-one
physical function whose normalized Fourier coefficients are exactly its own. -/
theorem exists_hillRealFiniteGap_smooth_representative (q : HillRealMeanZeroSource)
    (hf : q ∈ hillRealFiniteGapLocus) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ (∀ x, (f x).im=0) ∧
      ∀ k : ℤ, periodOneCoefficient f k=(hillRealMeanZeroInclusion q).val k := by
  let u : Coeff 2 := ⟨(hillRealMeanZeroInclusion q).val,by
    change Memℓp (hillRealMeanZeroInclusion q).val 2
    simpa only [Weight.sobolev_zero_apply,Complex.ofReal_one,one_mul] using
      hillRealFiniteGap_mem_all_sobolev q hf 0 le_rfl⟩
  let a : Coeff 1 := ⟨(hillRealMeanZeroInclusion q).val,by
    change Memℓp (hillRealMeanZeroInclusion q).val 1
    have h := memlp_one_sobolev_of_all_hilbert u
      (fun s hs => hillRealFiniteGap_mem_all_sobolev q hf s hs) 0 le_rfl
    simpa only [Weight.sobolev_zero_apply,Complex.ofReal_one,one_mul] using h⟩
  have hfix : star (Coeff.reflection a)=a := by
    ext k
    change (starRingEnd ℂ) ((hillRealMeanZeroInclusion q).val (-k))=(hillRealMeanZeroInclusion q).val k
    change (starRingEnd ℂ) (q.val.val.val (-k))=q.val.val.val k
    rw [q.property k,Complex.conj_conj]
  refine ⟨periodOneSynthesis a,?_,periodOneSynthesis_periodic a,?_,fun k => periodOneCoefficient_synthesis a k⟩
  · exact contDiff_periodOneSynthesis_of_all_sobolev (p := 2) (by simp) a
      (fun s hs => hillRealFiniteGap_mem_all_sobolev q hf s hs)
  · intro x
    have h := congrArg Complex.im (periodOneSynthesis_conjugateReflection a x)
    rw [hfix,Complex.conj_im] at h
    linarith

/-- Actual smooth native sources: the full actual raw source has every
nonnegative Sobolev order. Physical reality and zero mean are retained. -/
def hillRealSmoothLocus : Set HillRealMeanZeroSource :=
  {q | ∀ s : ℝ, 0 ≤ s → Memℓp (fun k => (Weight.sobolev s k:ℂ)*(hillRealMeanZeroInclusion q).val k) 2}

theorem hillRealFiniteGap_subset_smooth : hillRealFiniteGapLocus ⊆ hillRealSmoothLocus :=
  fun q hq s hs => hillRealFiniteGap_mem_all_sobolev q hq s hs

/-- Smooth physical sources are dense in the ORIGINAL Hminus-one norm. -/
theorem dense_hillRealSmoothLocus : Dense hillRealSmoothLocus :=
  dense_hillRealFiniteGapLocus.mono hillRealFiniteGap_subset_smooth

/-- The ACTUAL full native injectivity problem reduces to the SAME actual
map on smooth physical sources. Smooth/global injectivity are not assumed proved. -/
theorem hillPhysicalNative_injective_iff_injOn_smooth :
    Function.Injective hillRealSignedMap ↔ InjOn hillRealSignedMap hillRealSmoothLocus := by
  constructor
  · exact fun h => h.injOn
  · intro h
    apply hillPhysicalNative_injective_iff_injOn_finiteGap.mpr
    exact h.mono hillRealFiniteGap_subset_smooth

/-- The actual physical L2 source stratum, with no change of distribution. -/
def hillRealL2Locus : Set HillRealMeanZeroSource :=
  {q | Memℓp (hillRealMeanZeroInclusion q).val 2}

theorem hillRealFiniteGap_subset_L2 : hillRealFiniteGapLocus ⊆ hillRealL2Locus := by
  intro q hq
  change Memℓp (hillRealMeanZeroInclusion q).val 2
  simpa only [Weight.sobolev_zero_apply,Complex.ofReal_one,one_mul] using
    hillRealFiniteGap_mem_all_sobolev q hq 0 le_rfl

/-- Global ACTUAL native injectivity is equivalent to ACTUAL injectivity
on the ordinary physical L2 source, as in the classical-to-rough argument.
The L2 injectivity obligation itself remains separate and unproved. -/
theorem hillPhysicalNative_injective_iff_injOn_L2 :
    Function.Injective hillRealSignedMap ↔ InjOn hillRealSignedMap hillRealL2Locus := by
  constructor
  · exact fun h => h.injOn
  · intro h
    apply hillPhysicalNative_injective_iff_injOn_finiteGap.mpr
    exact h.mono hillRealFiniteGap_subset_L2

end NLS.Articles.KdVPseudomeasures
