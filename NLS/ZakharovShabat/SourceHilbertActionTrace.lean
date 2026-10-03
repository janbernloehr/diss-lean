import NLS.ZakharovShabat.SourceFiniteGapActionTrace
import NLS.ZakharovShabat.SourceHilbertActionTraceReduction

/-! # The action–mass trace formula for every real Hilbert source -/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat
namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The finite-gap contour identity computes the actual ℓ¹ total. -/
theorem hilbert_totalAction_eq_mass_finiteGap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    sourceHilbertTotalAction s φ = (sourceHilbertMass φ.val).re := by
  classical
  have hclosed : ∀ n ∉ hf.toFinset,
      sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val n = 0 := by
    intro n hn
    by_contra hgap
    apply hn
    apply hf.mem_toFinset.mpr
    change canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0
    simpa only [sourcePeriodicGapDisplacement_apply] using hgap
  rw [D.hilbert_totalAction_eq_sum_of_closed_tail φ hf.toFinset hclosed]
  have he := congrArg Complex.re (sourceFiniteGap_sum_actions_eq_mass φ hf)
  simpa only [Complex.re_sum] using he

/-- Continuity and actual finite-gap density give the trace formula on the
entire real Hilbert source space. -/
theorem hilbert_totalAction_eq_mass
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    sourceHilbertTotalAction s φ = (sourceHilbertMass φ.val).re :=
  D.hilbert_traceFormula_iff_finiteGap.mpr D.hilbert_totalAction_eq_mass_finiteGap φ

/-- The total spectral action is half the squared norm of the source pair. -/
theorem hilbert_totalAction_eq_half_norm_sq
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    sourceHilbertTotalAction s φ = ‖φ.val‖^2/2 := by
  rw [D.hilbert_totalAction_eq_mass φ,
    sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property, Complex.ofReal_re]

/-- The infinite action sum has no remaining finite-gap or asymptotic premise. -/
theorem hilbert_sum_actions_eq_half_norm_sq
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    (∑' n : ℤ, (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re) = ‖φ.val‖^2/2 := by
  rw [← D.hilbert_totalAction_eq_tsum φ, D.hilbert_totalAction_eq_half_norm_sq φ]

/-- The two real Birkhoff components preserve the source pair's squared norm. -/
theorem hilbert_real_map_norm_sq
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    ‖(sourceRealBirkhoffMap (by simp) (by norm_num) s φ).1‖^2 +
      ‖(sourceRealBirkhoffMap (by simp) (by norm_num) s φ).2‖^2 = ‖φ.val‖^2 := by
  have he := D.hilbert_totalAction_eq_half_norm_sq φ
  rw [sourceHilbertTotalAction_eq_output_norms] at he
  linarith

/-- The actual Hilbert Birkhoff map has the singleton zero fiber. -/
theorem hilbert_real_map_eq_zero_iff
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    sourceRealBirkhoffMap (by simp) (by norm_num) s φ = 0 ↔ φ = 0 := by
  have he := D.hilbert_real_map_norm_sq φ
  constructor
  · intro hz
    rw [hz] at he
    simp only [Prod.fst_zero, Prod.snd_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] at he
    apply Subtype.ext
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg φ.val]
  · intro hz
    have hv : φ.val = 0 := congrArg Subtype.val hz
    rw [hv, norm_zero] at he
    apply Prod.ext
    · apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖(sourceRealBirkhoffMap (by simp) (by norm_num) s φ).2‖,
        norm_nonneg (sourceRealBirkhoffMap (by simp) (by norm_num) s φ).1]
    · apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖(sourceRealBirkhoffMap (by simp) (by norm_num) s φ).1‖,
        norm_nonneg (sourceRealBirkhoffMap (by simp) (by norm_num) s φ).2]

end SourceBirkhoffMapComplexData

/-- The literal spectral trace identity is independent of a chosen Birkhoff family. -/
theorem sourceHilbert_sum_actions_eq_half_norm_sq (φ : realTypeSourceSubmodule 2) :
    (∑' n : ℤ, (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re) = ‖φ.val‖^2/2 := by
  obtain ⟨_, _, _, _, D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  exact D.hilbert_sum_actions_eq_half_norm_sq φ

end NLS.ZakharovShabat
