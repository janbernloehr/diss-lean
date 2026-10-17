import NLS.SequenceSpaces.WeightedRealInclusion
import NLS.ZakharovShabat.SourceWeightedRealSpaces

/-! # Original weighted membership and the unweighted target inclusion

A real source has an original weighted representative exactly when its
raw Fourier components carry that weight. The target inclusion preserves
raw coefficients continuously, with the source frequency convention w(2n).
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An original weighted representative is equivalent to raw weighted source membership. -/
theorem exists_originalWeightedRealSource_iff (w : SpectralWeight) (φ : realTypeSourceSubmodule p) :
    (∃ a : weightedRealSourceSubmodule (p := p) w, originalWeightedRealSource w a = φ) ↔
      Memℓp (fun n : ℤ => (w (2*n):ℂ)*φ.val.fst n) p ∧
        Memℓp (fun n : ℤ => (w (2*n):ℂ)*φ.val.snd n) p := by
  constructor
  · rintro ⟨a,rfl⟩
    simpa only [originalWeightedRealSource_fst,originalWeightedRealSource_snd] using
      (show Memℓp (fun n => (w (2*n):ℂ)*a.val.fst.val n) p ∧
        Memℓp (fun n => (w (2*n):ℂ)*a.val.snd.val n) p from
          ⟨a.val.fst.property,a.val.snd.property⟩)
  · rintro ⟨h₁,h₂⟩
    let a1 : WeightedCoeff (sourceFrequencyWeight w) p := ⟨φ.val.fst,h₁⟩
    let a2 : WeightedCoeff (sourceFrequencyWeight w) p := ⟨φ.val.snd,h₂⟩
    let b : WeightedCoeffPair (sourceFrequencyWeight w) p := WithLp.toLp p (a1,a2)
    have hb : b ∈ weightedRealSourceSubmodule w := by
      rw [mem_weightedRealSourceSubmodule_iff]
      exact φ.property
    let a : weightedRealSourceSubmodule (p := p) w := ⟨b,hb⟩
    refine ⟨a,?_⟩
    apply Subtype.ext
    apply (WithLp.equiv p _).injective
    apply Prod.ext <;> apply lp.ext <;> funext n
    · exact originalWeightedRealSource_fst w a n
    · exact originalWeightedRealSource_snd w a n

/-- Forget the target weight without changing either original real coefficient. -/
def originalWeightedRealTarget (w : SpectralWeight) :
    WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p)
      →L[ℝ] (RealCoeff p × RealCoeff p) :=
  WeightedRealCoeff.forgetPairWeightCLM (sourceFrequencyWeight w) (fun n => w.one_le (2*n))

@[simp] theorem originalWeightedRealTarget_fst (w : SpectralWeight)
    (a : WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p))
    (n : ℤ) : ((originalWeightedRealTarget w a).1 n:ℂ) = a.fst.val.val n :=
  WeightedRealCoeff.coe_forgetWeightCLM_apply _ _ _ _

@[simp] theorem originalWeightedRealTarget_snd (w : SpectralWeight)
    (a : WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p))
    (n : ℤ) : ((originalWeightedRealTarget w a).2 n:ℂ) = a.snd.val.val n :=
  WeightedRealCoeff.coe_forgetWeightCLM_apply _ _ _ _

theorem originalWeightedRealTarget_injective (w : SpectralWeight) :
    Function.Injective (originalWeightedRealTarget (p := p) w) :=
  WeightedRealCoeff.forgetPairWeightCLM_injective _ _

/-- The included target still has its original weight, in real coordinates. -/
theorem originalWeightedRealTarget_mem (w : SpectralWeight)
    (a : WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p)) :
    Memℓp (fun n : ℤ => w (2*n)*(originalWeightedRealTarget w a).1 n) p ∧
      Memℓp (fun n : ℤ => w (2*n)*(originalWeightedRealTarget w a).2 n) p :=
  ⟨WeightedRealCoeff.mem_weighted_forgetWeightCLM (sourceFrequencyWeight w) (fun n => w.one_le (2*n)) a.fst,
    WeightedRealCoeff.mem_weighted_forgetWeightCLM (sourceFrequencyWeight w) (fun n => w.one_le (2*n)) a.snd⟩

end NLS.ZakharovShabat
