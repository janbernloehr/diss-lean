import NLS.ZakharovShabat.SourceHilbertActionTrace
import NLS.ZakharovShabat.SourceHilbertCoefficientCompactness
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Properness from bounded coefficient continuity of spectral actions

The trace formula supplies a bound on sources and rules out energy loss.
The only remaining spectral input is continuity of each action along bounded
coefficientwise convergent source sequences. That input is explicit here.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ZakharovShabat

/-- The spectral continuity obligation needed for Hilbert properness.
Only convergence of the first Fourier component is required because sources are real. -/
def SourceHilbertActionsContinuousOnBoundedCoefficients : Prop :=
  ∀ (a : ℕ → realTypeSourceSubmodule 2) (b : realTypeSourceSubmodule 2),
    Bornology.IsBounded (range a) →
    (∀ n : ℤ, Tendsto (fun k => (a k).val.fst n) atTop (𝓝 (b.val.fst n))) →
    ∀ n : ℤ, Tendsto
      (fun k => (sourceRealAction (by simp) (by norm_num) (a k).val (a k).property n).re)
      atTop (𝓝 ((sourceRealAction (by simp) (by norm_num) b.val b.property n).re))

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The ℓ¹ norm of the nonnegative action sequence is exactly the source energy. -/
theorem hilbert_realActionSequence_norm_eq_half_norm_sq
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    ‖sourceHilbertRealActionSequence s φ‖ = ‖φ‖^2/2 := by
  rw [D.hilbert_realActionSequence_norm_eq_sum φ, D.hilbert_sum_actions_eq_half_norm_sq φ]
  rfl

/-- A bounded family of action sequences has bounded source preimages. -/
theorem hilbert_source_bounded_of_actions_bounded
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    {α : Type*} (a : α → realTypeSourceSubmodule 2)
    (hb : Bornology.IsBounded (range (fun k => sourceHilbertRealActionSequence s (a k)))) :
    Bornology.IsBounded (range a) := by
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C+1, ?_⟩
  rintro _ ⟨k, rfl⟩
  have hk := hC _ ⟨k, rfl⟩
  rw [D.hilbert_realActionSequence_norm_eq_half_norm_sq] at hk
  nlinarith [sq_nonneg (‖a k‖-1)]

/-- Convergence of the actual action sequences prevents energy loss and
upgrades a coefficientwise source limit to a strong source limit. -/
theorem hilbert_tendsto_of_coefficientwise_of_actions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    {α : Type*} {l : Filter α} (a : α → realTypeSourceSubmodule 2)
    (b : realTypeSourceSubmodule 2)
    (ht : ∀ n : ℤ, Tendsto (fun k => (a k).val.fst n) l (𝓝 (b.val.fst n)))
    (hI : Tendsto (fun k => sourceHilbertRealActionSequence s (a k)) l
      (𝓝 (sourceHilbertRealActionSequence s b))) :
    Tendsto a l (𝓝 b) := by
  apply tendsto_realTypeSource_of_coefficientwise_of_norm_sq a b ht
  have hn := hI.norm.mul_const 2
  simpa only [D.hilbert_realActionSequence_norm_eq_half_norm_sq, div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hn

/-- Bounded coefficient continuity of individual spectral actions, together
with the proved trace formula, makes the full ℓ¹ action map proper. -/
theorem hilbert_realActionSequence_proper_of_bounded_coefficient_continuity
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (hcont : SourceHilbertActionsContinuousOnBoundedCoefficients) :
    IsProperMap (sourceHilbertRealActionSequence s) := by
  have hIcont : Continuous (sourceHilbertRealActionSequence s) :=
    continuous_iff_continuousAt.mpr fun φ =>
      (D.hilbert_realActionSequence_analytic φ (mem_univ φ)).continuousAt
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hIcont, ?_⟩
  intro K hK
  apply IsSeqCompact.isCompact
  intro a ha
  have hbI : Bornology.IsBounded (range (fun k => sourceHilbertRealActionSequence s (a k))) :=
    hK.isBounded.subset (by rintro _ ⟨k, rfl⟩; exact ha k)
  have hba := D.hilbert_source_bounded_of_actions_bounded a hbI
  obtain ⟨I, hIK, σ, hσ, hIσ⟩ := hK.tendsto_subseq ha
  have hbσ : Bornology.IsBounded (range (a ∘ σ)) :=
    hba.subset (range_comp_subset_range _ _)
  obtain ⟨b, τ, hτ, ht, _⟩ := exists_realTypeSource_coefficientwise_subseq (a ∘ σ) hbσ
  have hγ : StrictMono (σ ∘ τ) := hσ.comp hτ
  have hI : Tendsto (fun k => sourceHilbertRealActionSequence s (a ((σ ∘ τ) k))) atTop (𝓝 I) :=
    hIσ.comp hτ.tendsto_atTop
  have hbc : Bornology.IsBounded (range (a ∘ (σ ∘ τ))) :=
    hba.subset (range_comp_subset_range _ _)
  have he : I = sourceHilbertRealActionSequence s b := by
    apply lp.ext
    funext n
    have hcoord := (lp.evalCLM ℝ (fun _ : ℤ => ℝ) 1 n).continuous.continuousAt.tendsto.comp hI
    have haction := hcont (a ∘ (σ ∘ τ)) b hbc ht n
    simp_rw [← D.hilbert_realActionSequence_apply] at haction
    exact tendsto_nhds_unique hcoord haction
  have hstrong : Tendsto (a ∘ (σ ∘ τ)) atTop (𝓝 b) :=
    D.hilbert_tendsto_of_coefficientwise_of_actions _ b ht (he ▸ hI)
  have hbK : sourceHilbertRealActionSequence s b ∈ K := he ▸ hIK
  exact ⟨b, hbK, σ ∘ τ, hγ, hstrong⟩

/-- The same explicit spectral continuity input suffices for properness of
the actual real Hilbert Birkhoff map. -/
theorem hilbert_real_map_proper_of_bounded_coefficient_continuity
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (hcont : SourceHilbertActionsContinuousOnBoundedCoefficients) :
    IsProperMap (sourceRealBirkhoffMap (by simp) (by norm_num) s) :=
  D.hilbert_real_map_proper_of_actionSequence_proper
    (D.hilbert_realActionSequence_proper_of_bounded_coefficient_continuity hcont)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
