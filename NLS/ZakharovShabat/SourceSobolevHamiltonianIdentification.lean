import NLS.ZakharovShabat.SourceSobolevFiniteGapDensity
import NLS.ZakharovShabat.SourceSobolevPhysicalCorrection
import NLS.ZakharovShabat.SourceRenormalizedHamiltonian
import NLS.ZakharovShabat.SourceFiniteGapHamiltonianExponent

/-! # Identification of the physical H¹ correction with the FL⁴ extension

The actual finite-gap identity passes to every real H¹ source using the
proved H¹ finite-gap density. Both the physical correction and the literal
cubic-moment sum are continuous in this topology. Exponent compatibility
identifies the same physical finite-gap source in the Hilbert and FL⁴ spaces.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The original H¹ source included continuously into FL⁴, with unchanged coefficients. -/
def sobolevSourceFL4 : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] CoeffPair 4 :=
  (CoeffPair.exponentInclusion (by norm_num : (2 : ℝ≥0∞) ≤ 4)).comp sobolevSourceInclusion

/-- The same inclusion on the real loci. -/
def realSobolevSourceFL4 (a : realTypeSobolevSourceLocus) : realTypeSourceLocus 4 :=
  realTypeSourceExponentInclusion (by norm_num : (2 : ℝ≥0∞) ≤ 4)
    ⟨sobolevSourceInclusion a.val, a.property⟩

/-- Finite-gap reconstruction keeps the original H¹ coefficients exactly. -/
theorem sourceFiniteGapSobolevPair_sobolevSource (a : realTypeSobolevSourceLocus)
    (hf : a ∈ sourceSobolevFiniteGapLocus) :
    sourceFiniteGapSobolevPair (by simp) (by norm_num)
      ⟨sobolevSourceInclusion a.val, a.property⟩ hf = a.val := by
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · exact sobolevSourceInclusion_fst a.val n
  · exact sobolevSourceInclusion_snd a.val n

namespace SourcePrimitivePowerAtlas
variable {W : Set (CoeffPair 4)}
variable (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)

/-- On finite-gap H¹ sources the FL⁴ extension is the original physical correction. -/
theorem renormalizedHamiltonian_eq_sobolevPhysicalCorrection_of_finiteGap
    (a : realTypeSobolevSourceLocus) (hf : a ∈ sourceSobolevFiniteGapLocus) :
    A.renormalizedHamiltonian (sobolevSourceFL4 a.val) = sourceSobolevPhysicalCorrection a.val := by
  let φ : realTypeSourceLocus 2 := ⟨sobolevSourceInclusion a.val,a.property⟩
  have hφ : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) := hf
  have hχ := (sourceFiniteGapLocus_exponent_iff (by simp) (by simp) (by norm_num) (by norm_num)
    (by norm_num : (2 : ℝ≥0∞) ≤ 4) φ).mp hφ
  have he := sourceFiniteGapRenormalizedHamiltonian_real_exponent
    (by simp) (by simp) (by norm_num) (by norm_num) (by norm_num : (2 : ℝ≥0∞) ≤ 4) φ hφ
  have hcal := sourceSobolevPhysicalCorrection_sourceFiniteGapSobolevPair φ hφ
  have hpair : sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hφ = a.val :=
    sourceFiniteGapSobolevPair_sobolevSource a hf
  rw [hpair] at hcal
  exact (A.renormalizedHamiltonian_eq_finiteGap (realSobolevSourceFL4 a) hχ).trans
    (he.symm.trans hcal.symm)

/-- The physical H¹ renormalization equals the cubic-moment FL⁴ extension at every real H¹ source. -/
theorem renormalizedHamiltonian_eq_sobolevPhysicalCorrection (a : realTypeSobolevSourceLocus) :
    A.renormalizedHamiltonian (sobolevSourceFL4 a.val) = sourceSobolevPhysicalCorrection a.val := by
  obtain ⟨U,_,_,hreal,_,hA,_,_⟩ := A.exists_renormalizedHamiltonian_analytic
  have hcont : Continuous (fun b : realTypeSobolevSourceLocus =>
      A.renormalizedHamiltonian (sobolevSourceFL4 b.val) - sourceSobolevPhysicalCorrection b.val) := by
    apply continuous_iff_continuousAt.mpr
    intro b
    have hcA : ContinuousAt A.renormalizedHamiltonian (sobolevSourceFL4 b.val) :=
      (hA (realSobolevSourceFL4 b).val (hreal (realSobolevSourceFL4 b).property)).continuousAt
    have hc : ContinuousAt (fun c : realTypeSobolevSourceLocus =>
        A.renormalizedHamiltonian (sobolevSourceFL4 c.val)) b :=
      hcA.comp (f := fun c : realTypeSobolevSourceLocus => sobolevSourceFL4 c.val)
        (sobolevSourceFL4.continuous.continuousAt.comp continuous_subtype_val.continuousAt)
    exact hc.sub ((continuousAt_sourceSobolevPhysicalCorrection b.val b.property).comp
      continuous_subtype_val.continuousAt)
  apply sub_eq_zero.mp
  exact eq_of_continuousOn_of_sourceSobolevFiniteGap isOpen_univ hcont.continuousOn 0
    (fun b _ hb => sub_eq_zero.mpr (A.renormalizedHamiltonian_eq_sobolevPhysicalCorrection_of_finiteGap b hb))
    a (mem_univ _)

/-- The identity uses the literal absolutely convergent weighted action subtraction and cubic moments. -/
theorem sobolevPhysicalHamiltonian_identity (a : realTypeSobolevSourceLocus) :
    periodOneSobolevHamiltonian a.val - 2*(periodOneSobolevMass a.val)^2 -
      (∑' n : ℤ, sourceSobolevWeightedAction a.val n) =
        -(4/3 : ℂ)*(∑' n : ℤ, A.moment n 3 (sobolevSourceFL4 a.val)) := by
  rw [← sourceSobolevWeightedActionSum_eq_tsum a.val a.property]
  exact (A.renormalizedHamiltonian_eq_sobolevPhysicalCorrection a).symm

end SourcePrimitivePowerAtlas

/-- An actual constructed primitive atlas satisfies the physical identity for every real H¹ source. -/
theorem exists_sobolevPhysicalHamiltonian_identification :
    ∃ W : Set (CoeffPair 4), ∃ A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W,
      ∀ a : realTypeSobolevSourceLocus,
        A.renormalizedHamiltonian (sobolevSourceFL4 a.val) = sourceSobolevPhysicalCorrection a.val := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (p := 4) (by simp) (by norm_num)
  exact ⟨W,A,A.renormalizedHamiltonian_eq_sobolevPhysicalCorrection⟩

/-- Coefficient preservation makes the H¹-to-FL⁴ inclusion injective. -/
theorem sobolevSourceFL4_injective : Function.Injective sobolevSourceFL4 := by
  intro a b hab
  have h : sobolevSourceInclusion a = sobolevSourceInclusion b :=
    CoeffPair.exponentInclusion_injective (by norm_num : (2 : ℝ≥0∞) ≤ 4) hab
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · simpa only [sobolevSourceInclusion_fst] using congrArg (fun x : CoeffPair 2 => x.fst n) h
  · simpa only [sobolevSourceInclusion_snd] using congrArg (fun x : CoeffPair 2 => x.snd n) h

/-- The actual physical H¹ correction is real and nonpositive. -/
theorem sourceSobolevPhysicalCorrection_nonpos (a : realTypeSobolevSourceLocus) :
    (sourceSobolevPhysicalCorrection a.val).re ≤ 0 ∧ (sourceSobolevPhysicalCorrection a.val).im = 0 := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (p := 4) (by simp) (by norm_num)
  rw [← A.renormalizedHamiltonian_eq_sobolevPhysicalCorrection a]
  exact A.real_renormalizedHamiltonian_nonpos (realSobolevSourceFL4 a)

/-- The physical H¹ correction vanishes exactly at the zero source. -/
theorem sourceSobolevPhysicalCorrection_eq_zero_iff (a : realTypeSobolevSourceLocus) :
    sourceSobolevPhysicalCorrection a.val = 0 ↔ a.val = 0 := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (p := 4) (by simp) (by norm_num)
  rw [← A.renormalizedHamiltonian_eq_sobolevPhysicalCorrection a]
  change A.renormalizedHamiltonian (realSobolevSourceFL4 a).val = 0 ↔ _
  refine (A.real_renormalizedHamiltonian_eq_zero_iff (realSobolevSourceFL4 a)).trans ?_
  constructor
  · intro h
    apply sobolevSourceFL4_injective
    have he := congrArg (fun x : realTypeSourceSubmodule 4 => x.val) h
    simpa only [map_zero, ZeroMemClass.coe_zero] using! he
  · intro h
    apply Subtype.ext
    change sobolevSourceFL4 a.val = 0
    rw [h, map_zero]

end NLS.ZakharovShabat
