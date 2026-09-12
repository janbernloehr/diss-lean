import NLS.Fourier.PeriodicSobolevLift
import NLS.ZakharovShabat.IntervalExtension

/-!
# Classical Dirichlet and Neumann interval extensions

The original domains consist of `H¹[0,1]` pairs with equal or opposite endpoint
values. Their signed-swap extensions are now constructed in the actual weighted
period-two domain, with exact physical reconstruction on `[0,2]`.
This establishes the Sobolev extension part; spectral intertwining is separate.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat.BoundaryCondition

/-- The original classical endpoint domain, without a period-one assumption. -/
structure HasClassicalIntervalDomain (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) : Prop where
  fst_regular : HasIntervalH1Regularity (fun x => (f x).1)
  snd_regular : HasIntervalH1Regularity (fun x => (f x).2)
  left : (f 0).1 = extensionSign b * (f 0).2
  right : (f 1).1 = extensionSign b * (f 1).2

private theorem reverse_endpoint (b : BoundaryCondition) {u v : ℂ}
    (h : u = extensionSign b * v) : v = extensionSign b * u := by
  rw [h, ← mul_assoc, extensionSign_sq, one_mul]

/-- The reflected classical interval pair in the one-derivative Fourier domain. -/
def classicalIntervalExtension (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) : Domain 2 :=
  (foldedSobolevCoefficients (extensionSign b) (fun x => (f x).1) (fun x => (f x).2)
      hf.fst_regular hf.snd_regular hf.left hf.right,
    foldedSobolevCoefficients (extensionSign b) (fun x => (f x).2) (fun x => (f x).1)
      hf.snd_regular hf.fst_regular (reverse_endpoint b hf.left) (reverse_endpoint b hf.right))

/-- The first component uses the actual normalized physical Fourier integrals. -/
@[simp] theorem classicalIntervalExtension_fst (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (n : ℤ) :
    (classicalIntervalExtension b f hf).1.val n =
      periodTwoCoefficient (fun x => (intervalExtension b f x).1) n :=
  foldedSobolevCoefficients_apply _ _ _ hf.fst_regular hf.snd_regular hf.left hf.right n

/-- The second component uses the actual normalized physical Fourier integrals. -/
@[simp] theorem classicalIntervalExtension_snd (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (n : ℤ) :
    (classicalIntervalExtension b f hf).2.val n =
      periodTwoCoefficient (fun x => (intervalExtension b f x).2) n :=
  foldedSobolevCoefficients_apply _ _ _ hf.snd_regular hf.fst_regular
    (reverse_endpoint b hf.left) (reverse_endpoint b hf.right) n

/-- The weighted coordinates satisfy the same signed reflection graph as the physical extension. -/
theorem classicalIntervalExtension_reflection (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (n : ℤ) :
    (classicalIntervalExtension b f hf).1.val n =
      extensionSign b * (classicalIntervalExtension b f hf).2.val (-n) := by
  rw [classicalIntervalExtension_fst, classicalIntervalExtension_snd]
  change periodTwoCoefficient (folded (extensionSign b) (fun x => (f x).1) (fun x => (f x).2)) n =
    extensionSign b * periodTwoCoefficient
      (folded (extensionSign b) (fun x => (f x).2) (fun x => (f x).1)) (-n)
  rw [periodTwoCoefficient_folded_of_intervalIntegrable _
    hf.fst_regular.1.continuousOn.intervalIntegrable hf.snd_regular.1.continuousOn.intervalIntegrable,
    periodTwoCoefficient_folded_of_intervalIntegrable _
    hf.snd_regular.1.continuousOn.intervalIntegrable hf.fst_regular.1.continuousOn.intervalIntegrable]
  rw [neg_neg, mul_add, ← mul_assoc, extensionSign_sq, one_mul, add_comm]

/-- The extension belongs to the selected closed weighted boundary domain. -/
theorem classicalIntervalExtension_mem (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) : classicalIntervalExtension b f hf ∈ domain b := by
  cases b
  · rw [domain, mem_weightedDirichletSubspace]
    intro n
    simpa only [extensionSign, one_mul] using classicalIntervalExtension_reflection .dirichlet f hf n
  · rw [domain, mem_weightedNeumannSubspace]
    intro n
    simpa only [extensionSign, neg_one_mul] using classicalIntervalExtension_reflection .neumann f hf n

/-- Synthesis recovers both components of the physical signed-swap extension. -/
theorem classicalIntervalExtension_reconstruct (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    (sobolevSynthesis (by simp) (classicalIntervalExtension b f hf).1 (x : AddCircle (2 : ℝ)),
      sobolevSynthesis (by simp) (classicalIntervalExtension b f hf).2 (x : AddCircle (2 : ℝ))) =
      intervalExtension b f x := by
  apply Prod.ext
  · exact sobolevSynthesis_foldedSobolevCoefficients _ _ _ hf.fst_regular hf.snd_regular hf.left hf.right hx
  · exact sobolevSynthesis_foldedSobolevCoefficients _ _ _ hf.snd_regular hf.fst_regular
      (reverse_endpoint b hf.left) (reverse_endpoint b hf.right) hx

/-- Restriction recovers the original classical interval function, including both endpoints. -/
theorem classicalIntervalExtension_restrict (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (sobolevSynthesis (by simp) (classicalIntervalExtension b f hf).1 (x : AddCircle (2 : ℝ)),
      sobolevSynthesis (by simp) (classicalIntervalExtension b f hf).2 (x : AddCircle (2 : ℝ))) =
      f x := by
  rw [classicalIntervalExtension_reconstruct b f hf ⟨hx.1, hx.2.trans (by norm_num)⟩,
    intervalExtension_left b f x hx.2]

/-- Equal weighted extensions identify the original functions on their whole interval. -/
theorem classicalIntervalExtension_injective_on_interval (b : BoundaryCondition)
    (f g : ℝ → ℂ × ℂ) (hf : HasClassicalIntervalDomain b f) (hg : HasClassicalIntervalDomain b g)
    (h : classicalIntervalExtension b f hf = classicalIntervalExtension b g hg) : EqOn f g (Icc 0 1) := by
  intro x hx
  rw [← classicalIntervalExtension_restrict b f hf hx, ← classicalIntervalExtension_restrict b g hg hx, h]

end NLS.ZakharovShabat.BoundaryCondition
