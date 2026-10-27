import NLS.ZakharovShabat.SourceBirkhoffSobolevGlobalInverse
import NLS.SequenceSpaces.WeightedFiniteBlock
import NLS.ZakharovShabat.SourceHilbertActionReduction

/-! # Continuous Sobolev lifts of curves with a common finite gap support -/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat

private def realFiniteBlock (w : Weight) (S : Finset ℤ) (a : RealCoeff 2) :
    WeightedRealCoeff w 2 :=
  WeightedCoeff.reCLM w 2 (WeightedCoeff.finiteBlock w S (fun n => (a n : ℂ)))

private theorem realFiniteBlock_val (w : Weight) (S : Finset ℤ) (a : RealCoeff 2) (n : ℤ) :
    (realFiniteBlock w S a).val.val n = if n ∈ S then (a n : ℂ) else 0 := by
  have hr : WeightedCoeff.finiteBlock (p := 2) w S (fun n => (a n : ℂ)) ∈
      WeightedCoeff.realLocus w 2 := by
    intro k
    simp only [WeightedCoeff.finiteBlock_val]
    split_ifs <;> rfl
  have h := WeightedCoeff.complexCLM_reCLM w 2 _ hr
  exact (congrArg (fun b : WeightedCoeff w 2 => b.val n) h).trans
    (WeightedCoeff.finiteBlock_val w S _ n)

private theorem continuous_realFiniteBlock (w : Weight) (S : Finset ℤ) :
    Continuous (realFiniteBlock w S) := by
  apply (WeightedCoeff.reCLM w 2).continuous.comp
  apply continuous_iff_continuousAt.mpr
  intro a
  exact WeightedCoeff.continuousAt_finiteBlock w S _ a (fun n _ =>
    Complex.continuous_ofReal.continuousAt.comp (lp.evalCLM ℝ (fun _ : ℤ => ℝ) 2 n).continuous.continuousAt)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- A Hilbert-continuous source curve whose open gaps stay in one finite
set has a continuous lift in every native nonnegative Sobolev norm.
The inclusion preserves the original source coefficients at every parameter. -/
theorem exists_continuous_sobolev_lift_of_finite_gap_support
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    {X : Type*} [TopologicalSpace X] (γ : X → realTypeSourceSubmodule 2) (hγ : Continuous γ)
    (S : Finset ℤ)
    (hS : ∀ x k, k ∉ S → canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (γ x).val) (periodOnePotential_mem _) k = 0)
    (σ : ℝ) (hσ : 0 ≤ σ) :
    ∃ F : X → weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ),
      Continuous F ∧ ∀ x,
        originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (F x) = γ x := by
  let w := sourceSobolevSpectralWeight σ hσ
  let z := fun x => D.hilbertRealHomeomorph (γ x)
  let Z := fun x => WithLp.toLp 2
    (realFiniteBlock (sourceFrequencyWeight w) S (z x).1,
      realFiniteBlock (sourceFrequencyWeight w) S (z x).2)
  have hz : Continuous z := D.hilbertRealHomeomorph.continuous.comp hγ
  have hZ : Continuous Z := (WithLp.prod_continuous_toLp 2 _ _).comp
    (((continuous_realFiniteBlock _ S).comp hz.fst).prodMk
      ((continuous_realFiniteBlock _ S).comp hz.snd))
  have he (x : X) : originalWeightedRealTarget w (Z x) = z x := by
    have hzero (k : ℤ) (hk : k ∉ S) : (z x).1 k = 0 ∧ (z x).2 k = 0 :=
      (D.real_coordinates_zero_iff_gap_zero (γ x) k).mpr
        (by simpa only [sourcePeriodicGapDisplacement_apply] using hS x k hk)
    apply Prod.ext <;> ext k
    · apply Complex.ofReal_injective
      rw [originalWeightedRealTarget_fst]
      change (realFiniteBlock _ S (z x).1).val.val k = ((z x).1 k : ℂ)
      rw [realFiniteBlock_val]
      split_ifs with hk
      · rfl
      · rw [(hzero k hk).1,Complex.ofReal_zero]
    · apply Complex.ofReal_injective
      rw [originalWeightedRealTarget_snd]
      change (realFiniteBlock _ S (z x).2).val.val k = ((z x).2 k : ℂ)
      rw [realFiniteBlock_val]
      split_ifs with hk
      · rfl
      · rw [(hzero k hk).2,Complex.ofReal_zero]
  let H := D.originalWeightedRealSobolevHomeomorph (by rfl) σ hσ
  refine ⟨fun x => H.symm (Z x),H.symm.continuous.comp hZ,fun x => ?_⟩
  change originalWeightedRealSource _
    ((D.originalWeightedRealSobolevEquiv (by rfl) σ hσ).symm (Z x)) = γ x
  rw [D.originalWeightedRealSource_sobolevEquiv_symm,he]
  exact D.hilbertRealHomeomorph.symm_apply_apply (γ x)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
