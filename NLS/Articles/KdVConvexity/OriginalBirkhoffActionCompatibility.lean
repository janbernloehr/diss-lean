import NLS.Articles.KdVConvexity.PhysicalActionHamiltonian
import NLS.KdV.HillOriginalBirkhoffMap

/-! # Exact compatibility with the fixed original physical Birkhoff map -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

def nativeH1OriginalBirkhoffSource
    (q : RealHillWeightedPotential hillH1SpectralWeight) (hm : q.val.val 0=0) :
    hillRealMeanZeroSourceSubmodule :=
  ⟨⟨hillPeriodOneUnitPotential hillH1SpectralWeight q.val,
      hillPeriodOneUnitPotential_even hillH1SpectralWeight q.val,
      hillPeriodOneUnitPotential_real hillH1SpectralWeight q.val q.property⟩,
    (mem_hillRealMeanZeroSourceSubmodule _).mpr (by
      change (hillForgetWeight hillH1SpectralWeight 2
        (hillPeriodOnePotential hillH1SpectralWeight q.val)).val 0=0
      rw [hillForgetWeight_apply,show (0 : ℤ)=2*0 by norm_num,hillPeriodOnePotential_even]
      exact hm)⟩

/-- The actions used to define the physical Hstar are literally the
original Birkhoff actions (x_n^2+y_n^2)/2, at every positive source index.
This includes low and closed gaps, with the fixed canonical orientation. -/
theorem physicalHilbertActions_eq_original_Birkhoff_actions
    (q : RealHillWeightedPotential hillH1SpectralWeight) (hm : q.val.val 0=0) (k : ℕ) :
    physicalHilbertActions hillH1SpectralWeight q ⟨k+1,by omega⟩ =
      (((((hillOriginalBirkhoffMap (nativeH1OriginalBirkhoffSource q hm)).val k).1^2+
        ((hillOriginalBirkhoffMap (nativeH1OriginalBirkhoffSource q hm)).val k).2^2)/2 : ℝ) : ℂ) := by
  apply (physicalHilbertActions_apply hillH1SpectralWeight q ⟨k+1,by omega⟩).trans
  apply congrArg Complex.ofReal
  change hillPeriodOneAction hillH1SpectralWeight q.val q.property (k+1) =
    (((hillOriginalBirkhoffMap (nativeH1OriginalBirkhoffSource q hm)).val k).1^2+
      ((hillOriginalBirkhoffMap (nativeH1OriginalBirkhoffSource q hm)).val k).2^2)/2
  have he := hillOriginalBirkhoffMap_action_identity (nativeH1OriginalBirkhoffSource q hm) k
  change ((hillOriginalBirkhoffMap (nativeH1OriginalBirkhoffSource q hm)).val k).1^2+
      ((hillOriginalBirkhoffMap (nativeH1OriginalBirkhoffSource q hm)).val k).2^2 =
    2*hillPeriodOneAction hillH1SpectralWeight q.val q.property (k+1) at he
  nlinarith

end NLS.Articles.KdVConvexity
