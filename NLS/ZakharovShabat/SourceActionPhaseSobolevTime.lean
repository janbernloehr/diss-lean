import NLS.ZakharovShabat.SourceActionPhaseFiniteGap
import NLS.ZakharovShabat.SourceFiniteGapSobolevTime

/-! # Strong physical H¹ time regularity of actual finite-gap phase lifts

The common original closed-gap tail and full Hilbert-norm time derivative
upgrade the canonical physical representatives to H¹ time differentiability.
No particular hierarchy frequency or physical PDE is assumed here.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.ZakharovShabat.SourceActionFrequency
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The actual canonical physical H¹ pair along a finite-gap source lift. -/
def finiteGapSobolevCurve (F : SourceActionFrequency (p := 2) (by simp) (by norm_num))
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    ScalarDomain 2 × ScalarDomain 2 :=
  sourceFiniteGapSobolevPair (by simp) (by norm_num) (F.imageFlow D φ time)
    (F.imageFlow_finiteGap D φ hf time (F.mem_imageDomain_of_le_two D le_rfl φ time))

/-- Every such canonical representative is differentiable in the full
physical H¹ norm at every real time. -/
theorem differentiable_finiteGapSobolevCurve
    (F : SourceActionFrequency (p := 2) (by simp) (by norm_num))
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    Differentiable ℝ (F.finiteGapSobolevCurve D φ hf) := by
  classical
  obtain ⟨S,hS⟩ := D.exists_complex_support_finiteGap φ hf
  intro time
  apply differentiableAt_sourceFiniteGapSobolevPair (F.imageFlow D φ)
    (fun r => F.imageFlow_finiteGap D φ hf r (F.mem_imageDomain_of_le_two D le_rfl φ r)) time
    (F.hasDerivAt_imageFlow_finiteAction D le_rfl le_rfl φ S hS time).differentiableAt
    (hf.toFinset.sup Int.natAbs+1)
  apply Eventually.of_forall
  intro r n hn
  have hclosed : sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val n = 0 := by
    rw [sourcePeriodicGapDisplacement_apply]
    by_contra hne
    have hmem : n ∈ hf.toFinset := hf.mem_toFinset.mpr hne
    have hle := Finset.le_sup (f := Int.natAbs) hmem
    omega
  simpa only [sourcePeriodicGapDisplacement_apply] using
    (F.imageFlow_closed_gap_and_action_differential D φ r (F.mem_imageDomain_of_le_two D le_rfl φ r) n hclosed).1

/-- The stronger physical time derivative has exactly the original
source-norm derivative after forgetting only the Sobolev weight. -/
theorem finiteGapSobolevCurve_deriv_inclusion
    (F : SourceActionFrequency (p := 2) (by simp) (by norm_num))
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    sobolevSourceInclusion (deriv (F.finiteGapSobolevCurve D φ hf) time) =
      deriv (fun r => (F.imageFlow D φ r).val) time := by
  have hd := (F.differentiable_finiteGapSobolevCurve D φ hf time).hasDerivAt
  have hi := (sobolevSourceInclusion.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time hd
  change HasDerivAt (fun r => sobolevSourceInclusion (sourceFiniteGapSobolevPair (by simp) (by norm_num)
    (F.imageFlow D φ r) (F.imageFlow_finiteGap D φ hf r (F.mem_imageDomain_of_le_two D le_rfl φ r)))) _ time at hi
  simp only [sobolevSourceInclusion_sourceFiniteGapSobolevPair] at hi
  exact hi.deriv.symm

end NLS.ZakharovShabat.SourceActionFrequency
