import NLS.ZakharovShabat.SourceActionDifferentialIndependence
import NLS.ZakharovShabat.SourceOriginalActionIntegrals
import NLS.ZakharovShabat.SourceRealCotangent
import NLS.ZakharovShabat.SourceRealTypeDecomposition
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Real action differentials and the exact closed-gap criterion

The original action integrals in the introduction, printed p. 9,
have independent differentials precisely on their open-gap index set.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original complex action differential is real on real-type perturbations. -/
theorem isSourceRealCotangent_sourceComplexAction (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (φ : realTypeSourceSubmodule p) :
    IsSourceRealCotangent (fderiv ℂ (sourceComplexAction hp hp1 n) φ.val) := by
  apply isSourceRealCotangent_fderiv_of_eventually_real _
    (⟨φ.val,φ.property⟩ : realTypeSourceLocus p)
    (analyticAt_sourceComplexAction_of_realType hp hp1 n φ.val φ.property).differentiableAt
  filter_upwards [] with ψ
  intro hψ
  rw [sourceComplexAction_eq_sourceRealAction hp hp1 n ψ hψ]
  exact (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 ψ hψ n).2.1

/-- The real action derivative is the real part of the original complex derivative. -/
theorem fderiv_originalRealActionIntegral_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (φ h : realTypeSourceSubmodule p) :
    (fderiv ℝ (originalRealActionIntegral hp hp1 n) φ) h =
      ((fderiv ℂ (sourceComplexAction hp hp1 n) φ.val) h.val).re := by
  have hF := (analyticAt_sourceComplexAction_of_realType hp hp1 n
    φ.val φ.property).differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hd := Complex.reCLM.hasFDerivAt.comp φ
    (hF.comp φ (realTypeSourceSubmodule p).subtypeL.hasFDerivAt)
  exact congrArg (fun L => L h) hd.fderiv

/-- The actual real action differentials are independent on the open gaps,
at every finite original Fourier-Lebesgue exponent greater than one. -/
theorem linearIndependent_originalRealActionIntegral_fderiv_open_gaps
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) :
    LinearIndependent ℝ
      (fun n : {n : ℤ // canonicalPeriodicGap hp hp1
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0} =>
        fderiv ℝ (originalRealActionIntegral hp hp1 n.val) φ) := by
  classical
  rw [linearIndependent_iff']
  intro S a ha n hn
  have hr (h : realTypeSourceSubmodule p) :
      (∑ k ∈ S, (a k : ℂ)*(fderiv ℂ (sourceComplexAction hp hp1 k.val) φ.val) h.val) = 0 := by
    apply Complex.ext
    · have he := congrArg (fun L : realTypeSourceSubmodule p →L[ℝ] ℝ => L h) ha
      simpa only [sum_apply,smul_apply,smul_eq_mul,zero_apply,
        fderiv_originalRealActionIntegral_apply,Complex.re_sum,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.zero_re] using he
    · have hzero (k : {n : ℤ // canonicalPeriodicGap hp hp1
          (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0}) :
          ((fderiv ℂ (sourceComplexAction hp hp1 k.val) φ.val) h.val).im = 0 :=
        isSourceRealCotangent_sourceComplexAction hp hp1 k.val φ h.val h.property
      simp only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        hzero,mul_zero,zero_mul,add_zero,Finset.sum_const_zero,Complex.zero_im]
  have hc : (∑ k ∈ S, (a k : ℂ) • fderiv ℂ (sourceComplexAction hp hp1 k.val) φ.val) = 0 := by
    ext v
    have hv := sourceRealPart_add_I_smul_sourceImagPart v
    have hR := hr ⟨sourceRealPart v,sourceRealPart_realType v⟩
    have hI := hr ⟨sourceImagPart v,sourceImagPart_realType v⟩
    rw [← hv]
    simp only [sum_apply,smul_apply,smul_eq_mul,zero_apply,map_add,map_smul]
    rw [hR,hI]
  have hl := linearIndependent_sourceComplexAction_fderiv_open_gaps hp hp1
    (⟨φ.val,φ.property⟩ : realTypeSourceLocus p)
  have hz := (linearIndependent_iff'.mp hl) S (fun k => (a k : ℂ)) hc n hn
  exact_mod_cast hz

/-- At a collapsed gap the real action has a minimum, so its differential vanishes. -/
theorem fderiv_originalRealActionIntegral_eq_zero_of_closed_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) :
    fderiv ℝ (originalRealActionIntegral hp hp1 n) φ = 0 := by
  have hg : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0 := by
    simpa only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap] using hn
  have hz : originalRealActionIntegral hp hp1 n φ = 0 := by
    rw [originalRealActionIntegral,sourceComplexAction_eq_sourceRealAction hp hp1 n _ φ.property,
      (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ.val φ.property n).2.2.mpr hg]
    rfl
  apply IsLocalMin.fderiv_eq_zero
  apply Filter.Eventually.of_forall
  intro ψ
  rw [hz,originalRealActionIntegral,sourceComplexAction_eq_sourceRealAction hp hp1 n _ ψ.property]
  exact (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 ψ.val ψ.property n).1

/-- Vanishing of the original real action differential is exactly gap collapse. -/
theorem fderiv_originalRealActionIntegral_eq_zero_iff_closed_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    fderiv ℝ (originalRealActionIntegral hp hp1 n) φ = 0 ↔
      canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) n = 0 := by
  constructor
  · intro hz
    by_contra hn
    exact (linearIndependent_originalRealActionIntegral_fderiv_open_gaps hp hp1 φ).ne_zero
      ⟨n,hn⟩ hz
  · exact fderiv_originalRealActionIntegral_eq_zero_of_closed_gap hp hp1 φ n

/-- All real action differentials are independent precisely at sources with all gaps open. -/
theorem linearIndependent_originalRealActionIntegral_fderiv_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) :
    LinearIndependent ℝ (fun n : ℤ => fderiv ℝ (originalRealActionIntegral hp hp1 n) φ) ↔
      ∀ n : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) n ≠ 0 := by
  constructor
  · intro h n hn
    exact h.ne_zero n (fderiv_originalRealActionIntegral_eq_zero_of_closed_gap hp hp1 φ n hn)
  · intro h
    exact (linearIndependent_originalRealActionIntegral_fderiv_open_gaps hp hp1 φ).comp
      (fun n : ℤ => ⟨n,h n⟩) (fun a b hab => congrArg Subtype.val hab)

end NLS.ZakharovShabat
