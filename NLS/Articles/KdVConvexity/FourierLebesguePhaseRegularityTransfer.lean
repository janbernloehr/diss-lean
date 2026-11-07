import NLS.Articles.KdVConvexity.FourierLebesguePhaseCompatibility
import NLS.SequenceSpaces.WeightedRawMembershipTransport
import NLS.SequenceSpaces.PhysicalSobolevExponentInclusion

/-! # Higher native regularity transferred through literal source coefficients -/
noncomputable section
set_option autoImplicit false
open Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem fourierLebesguePhaseEvolution_mem_higher_order
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (s r : ℝ) (hs : -1/2≤s) (hr : -1/2≤r)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (a : physicalRealMeanZeroWeightedExponent (Weight.sobolev r) p)
    (he : ∀ j : ℤ, q.val.val j=a.val.val j) (t : ℝ) :
    Memℓp (fun j => (Weight.sobolev r j : ℂ)*
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q).val.val j) p :=
  weighted_memℓp_of_raw_eq (Weight.sobolev r) p _ _
    (D.fourierLebesguePhaseEvolution B r hr p hp h2p t a).val.property
    (D.fourierLebesguePhaseEvolution_compatible B s r hs hr p p hp hp h2p h2p q a he t)

theorem fourierLebesguePhaseEvolution_preserves_all_sobolev
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (s : ℝ) (hs : -1/2≤s)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) 2)
    (hall : ∀ r : ℝ, 0≤r → Memℓp (fun j => (Weight.sobolev r j : ℂ)*q.val.val j) 2)
    (t : ℝ) : ∀ r : ℝ, 0≤r → Memℓp (fun j => (Weight.sobolev r j : ℂ)*
      (D.fourierLebesguePhaseEvolution B s hs 2 (by simp) (by norm_num) t q).val.val j) 2 := by
  intro r hr
  obtain ⟨a,ha⟩ := exists_physicalWeightedRelift (Weight.sobolev s) (Weight.sobolev r) q (hall r hr)
  exact D.fourierLebesguePhaseEvolution_mem_higher_order B s r hs (by linarith)
    2 (by simp) (by norm_num) q a ha t

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
