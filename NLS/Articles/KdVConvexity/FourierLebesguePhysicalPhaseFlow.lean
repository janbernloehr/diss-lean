import NLS.Articles.KdVConvexity.FourierLebesguePhysicalActions
import NLS.SequenceSpaces.SignedPositiveFrequency
import NLS.SequenceSpaces.PhysicalRealMeanZeroPhaseFlowExponent

/-! # Global continuous phase evolution at the actual physical KdV frequencies

The original raw quadratic actions determine the already-constructed
physical frequency family. Opposite signed phases preserve every action,
so this is a genuine continuous group in each original native target.
PDE recovery and the source's approximation solution notion are separate
remaining obligations for Theorem 1.3.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
namespace BasePhysicalFrequencyExtension
variable (B : BasePhysicalFrequencyExtension) (s : ℝ) (hs : -1/2≤s)
  (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]

def fourierLebesguePhysicalFrequency
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) (n : ℕ+) : ℝ :=
  (B.frequency n (fourierLebesguePhysicalActions s hs p hp h2p z)).re

theorem fourierLebesguePhysicalFrequency_coe
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) (n : ℕ+) :
    (B.fourierLebesguePhysicalFrequency s hs p hp h2p z n : ℂ)=
      B.frequency n (fourierLebesguePhysicalActions s hs p hp h2p z) := by
  apply Complex.ext
  · rfl
  · exact (B.frequency_real_on_cone _
      (fourierLebesguePhysicalActions_nonnegative s hs p hp h2p z) n).symm

theorem continuous_fourierLebesguePhysicalFrequency (n : ℕ+) :
    Continuous (fun z => B.fourierLebesguePhysicalFrequency s hs p hp h2p z n) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact Complex.continuous_re.continuousAt.comp
    ((B.analytic n _ (B.contains_cone (fourierLebesguePhysicalActions_nonnegative s hs p hp h2p z))).continuousAt.comp
      (continuous_fourierLebesguePhysicalActions s hs p hp h2p).continuousAt)

def fourierLebesguePhysicalPhaseFlow (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p :=
  physicalRealMeanZeroPhaseFlow _
    (signedPositiveFrequency (B.fourierLebesguePhysicalFrequency s hs p hp h2p z))
    (signedPositiveFrequency_neg _) t z

theorem fourierLebesguePhysicalPhaseFlow_apply (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) (j : ℤ) :
    (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p t z).val.val j=
      Complex.exp (((t*signedPositiveFrequency
        (B.fourierLebesguePhysicalFrequency s hs p hp h2p z) j : ℝ) : ℂ)*I)*z.val.val j :=
  physicalRealMeanZeroPhaseFlow_apply _ _ _ t z j

theorem fourierLebesguePhysicalPhaseFlow_positive (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) (n : ℕ+) :
    (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p t z).val.val n=
      Complex.exp ((t : ℂ)*B.frequency n
        (fourierLebesguePhysicalActions s hs p hp h2p z)*I)*z.val.val n := by
  rw [B.fourierLebesguePhysicalPhaseFlow_apply,signedPositiveFrequency_positive,
    ofReal_mul,B.fourierLebesguePhysicalFrequency_coe]

@[simp] theorem fourierLebesguePhysicalPhaseFlow_zero
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p 0 z=z :=
  physicalRealMeanZeroPhaseFlow_zero _ _ _ z

theorem continuous_fourierLebesguePhysicalPhaseFlow :
    Continuous (fun x : ℝ × physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p =>
      B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p x.1 x.2) := by
  exact continuous_physicalRealMeanZeroPhaseFlow_family _ hp
    (fun z => signedPositiveFrequency (B.fourierLebesguePhysicalFrequency s hs p hp h2p z))
    (fun _ => signedPositiveFrequency_neg _) id
    (continuous_signedPositiveFrequency _ (B.continuous_fourierLebesguePhysicalFrequency s hs p hp h2p))
    continuous_id

@[simp] theorem fourierLebesguePhysicalPhaseFlow_actions (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    fourierLebesguePhysicalActions s hs p hp h2p
      (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p t z)=
        fourierLebesguePhysicalActions s hs p hp h2p z := by
  apply Subtype.ext
  funext k
  rw [fourierLebesguePhysicalActions_apply,fourierLebesguePhysicalActions_apply]
  exact physicalRealMeanZeroPhaseFlow_signed_product _ _ _ t z _

@[simp] theorem fourierLebesguePhysicalPhaseFlow_frequency (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    B.fourierLebesguePhysicalFrequency s hs p hp h2p
      (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p t z)=
        B.fourierLebesguePhysicalFrequency s hs p hp h2p z := by
  funext n
  unfold fourierLebesguePhysicalFrequency
  rw [B.fourierLebesguePhysicalPhaseFlow_actions]

theorem fourierLebesguePhysicalPhaseFlow_add (t u : ℝ)
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p t
      (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p u z)=
        B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p (t+u) z := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rw [B.fourierLebesguePhysicalPhaseFlow_apply,B.fourierLebesguePhysicalPhaseFlow_frequency,
    B.fourierLebesguePhysicalPhaseFlow_apply,B.fourierLebesguePhysicalPhaseFlow_apply,
    add_mul,ofReal_add,add_mul,Complex.exp_add]
  ring

@[simp] theorem norm_fourierLebesguePhysicalPhaseFlow (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    ‖B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p t z‖=‖z‖ :=
  norm_physicalRealMeanZeroPhaseFlow _ _ _ t z

theorem fourierLebesguePhysicalPhaseFlow_support (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    Function.support (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p t z).val.val=
      Function.support z.val.val :=
  physicalRealMeanZeroPhaseFlow_support _ _ _ t z

end BasePhysicalFrequencyExtension
end NLS.Articles.KdVConvexity
