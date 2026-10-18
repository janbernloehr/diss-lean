import NLS.ZakharovShabat.SourcePrimitivePowerSharpCubic
import NLS.ZakharovShabat.SourceH1ZeroModeMomentCriterion

/-! # The remaining spectral representation obligation at the H1 endpoint

A positive exterior-kernel representation of the actual zero-gap arcosh
profile, together with its integrable majorant, implies the literal m=1
estimate of Lemma 27.2. The moment atlas is constructed internally.
Existence of that representation at arbitrary open zero gaps is not
proved here; the unrestricted printed endpoint remains unresolved.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- A proved exterior-kernel formula at the actual zero gap would settle the m=1 endpoint. -/
theorem sourceH1_energy_le_lemma272_of_zero_gap_kernel_representation
    (a : realTypeSobolevSourceLocus)
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.SFinite μ]
    (c s : α → ℝ) (hcm : Measurable c) (hsm : Measurable s)
    (hc : ∀ b, 0 ≤ c b) (hs : ∀ b, 1 < |s b|)
    (hint : MeasureTheory.Integrable (fun b => c b/(|s b|-1)) μ)
    (hrep : ∀ x ∈ Set.Icc (0:ℝ) Real.pi,
      sourceRealGapCosineProfile (by simp) (by norm_num) (sobolevSourceFL4 a.val) 0 x =
        (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceFL4 a.val))
          (periodOnePotential_mem (sobolevSourceFL4 a.val)) 0).re/2*
          Real.sin x*(1+(∫ b, c b/|s b-Real.cos x| ∂μ))) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      (1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (by simp : (4:ℝ≥0∞) ≠ ⊤) (by norm_num)
  have h := A.real_action_sq_le_cubic_of_exterior_kernel_representation
    ⟨sobolevSourceFL4 a.val,(realSobolevSourceFL4 a).property⟩ 0 μ c s hcm hsm hc hs hint hrep
  rw [← sourceH1_actionTerm_zero_eq_FL4 a 0] at h
  exact A.sourceH1_energy_le_lemma272_of_zero_moment a h

end NLS.ZakharovShabat
