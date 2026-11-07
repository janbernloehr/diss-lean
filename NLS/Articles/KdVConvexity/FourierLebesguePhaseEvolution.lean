import NLS.Articles.KdVConvexity.FourierLebesguePhysicalPhaseFlow
import NLS.KdV.HillRoughFourierLebesgueHomeomorph
import NLS.Dynamics.ConjugatedContinuousEvolution

/-! # Native global evolution through the SAME physical Birkhoff map

This constructs the global continuous group at the actual physical
frequencies, with continuous complete trajectories and convergence
uniform on compact time sets. Theorem 1.3 additionally requires actual
KdV PDE recovery and uniqueness in its approximation solution notion.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity
variable (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
  (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]

def fourierLebesguePhaseEvolution (t : ℝ)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p :=
  NLS.Dynamics.conjugatedEvolution (D.fourierLebesgueHomeomorph s hs p hp h2p)
    (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p) t q

theorem fourierLebesguePhaseEvolution_coordinates (t : ℝ)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    D.fourierLebesgueForward s hs p hp h2p (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q)=
      B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p t (D.fourierLebesgueForward s hs p hp h2p q) :=
  NLS.Dynamics.conjugatedEvolution_coordinates
    (D.fourierLebesgueHomeomorph s hs p hp h2p) (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p) t q

@[simp] theorem fourierLebesguePhaseEvolution_zero
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    D.fourierLebesguePhaseEvolution B s hs p hp h2p 0 q=q :=
  NLS.Dynamics.conjugatedEvolution_zero _ _ (B.fourierLebesguePhysicalPhaseFlow_zero s hs p hp h2p) q

theorem fourierLebesguePhaseEvolution_add (t u : ℝ)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    D.fourierLebesguePhaseEvolution B s hs p hp h2p t
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p u q)=
        D.fourierLebesguePhaseEvolution B s hs p hp h2p (t+u) q :=
  NLS.Dynamics.conjugatedEvolution_add _ _ (B.fourierLebesguePhysicalPhaseFlow_add s hs p hp h2p) t u q

theorem continuous_fourierLebesguePhaseEvolution :
    Continuous (fun x : ℝ × physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p =>
      D.fourierLebesguePhaseEvolution B s hs p hp h2p x.1 x.2) :=
  NLS.Dynamics.continuous_conjugatedEvolution _ _
    (B.continuous_fourierLebesguePhysicalPhaseFlow s hs p hp h2p)

def fourierLebesgueTrajectoryMap :
    C(physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p,
      C(ℝ,physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)) :=
  NLS.Dynamics.conjugatedTrajectoryMap (D.fourierLebesgueHomeomorph s hs p hp h2p)
    (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p)
    (B.continuous_fourierLebesguePhysicalPhaseFlow s hs p hp h2p)

@[simp] theorem fourierLebesgueTrajectoryMap_apply
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) (t : ℝ) :
    D.fourierLebesgueTrajectoryMap B s hs p hp h2p q t=
      D.fourierLebesguePhaseEvolution B s hs p hp h2p t q := rfl

/-- Native initial-data convergence gives uniform convergence of the
actual phase evolutions on EVERY compact time set, with no frequency bound. -/
theorem tendstoUniformlyOn_fourierLebesguePhaseEvolution {ι : Type*} {l : Filter ι}
    {q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p}
    {u : ι → physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p}
    (hu : Tendsto u l (𝓝 q)) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun i t => D.fourierLebesguePhaseEvolution B s hs p hp h2p t (u i))
      (fun t => D.fourierLebesguePhaseEvolution B s hs p hp h2p t q) l K :=
  NLS.Dynamics.tendstoUniformlyOn_conjugatedEvolution _ _
    (B.continuous_fourierLebesguePhysicalPhaseFlow s hs p hp h2p) hu K hK

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
