import NLS.KdV.PhysicalSharpFrequencyDecayData
import NLS.KdV.PhysicalSharpOffDiagonalParameterization

/-! The FULL actual corrected physical frequency has the sharp
source weight on ONE chart. Big-O is uniform on a full complex
neighborhood; the little-o conclusion here is POINTWISE there. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

theorem PhysicalFrequencyParameterization.exists_sharp_frequency_decay
    (A : PhysicalFrequencyParameterization E t ht J) (ht1 : t≤2/3)
    (q : E) (hq : q∈A.domain) (hqr : IsRealPeriodOneHminusOne (J q)) :
    A.HasSharpFrequencyDecay q := by
  obtain ⟨Td,hTd,hqTd,hTdA,K,Md,hMd,hdb,hdt⟩ :=
    A.exists_sharp_diagonal_cancellation_decay (by linarith) q hq hqr
  obtain ⟨To,hTo,hqTo,_hToA,Mo,hMo,hob,hot⟩ := A.exists_sharp_offDiagonal_decay ht1 q hq hqr
  exact A.sharpFrequencyDecay_of_parts q Td hTd hqTd hTdA K Md hMd hdb hdt To hTo hqTo Mo hMo hob hot

end NLS.KdV
