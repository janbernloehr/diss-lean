import NLS.KdV.HillOriginalGlobalInverse

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

/-- The FIXED ORIGINAL real coordinate: the real part of the literal full
physical Cartesian, retaining its action, Dirichlet sheet and entire phase. -/
def hillOriginalBirkhoffX (q : hillRealMeanZeroSourceSubmodule) (n : ℕ+) : ℝ :=
  (hillSpectralCartesian q.val.val q.val.property.1 q.val.property.2 n n.pos).re

/-- The FIXED ORIGINAL canonical real partner. The minus sign is forced by
the verified positive 2*i mixed complex Gardner bracket. -/
def hillOriginalBirkhoffY (q : hillRealMeanZeroSourceSubmodule) (n : ℕ+) : ℝ :=
  -(hillSpectralCartesian q.val.val q.val.property.1 q.val.property.2 n n.pos).im

/-- Decoding the ACTUAL global spectral homeomorphism yields the fixed
original real pair, with its exact positive-index normalization. -/
theorem hillOriginalBaseSpectralSequence_birkhoff_pair
    (q : hillRealMeanZeroSourceSubmodule) (k : ℕ) :
    hillOriginalMeanZeroRealSpectralMap q k =
      (Real.sqrt (2*Real.pi*(k+1 : ℕ)) : ℂ)*
        ((hillOriginalBirkhoffX q ⟨k+1,by omega⟩ : ℂ)-
          I*(hillOriginalBirkhoffY q ⟨k+1,by omega⟩ : ℂ)) := by
  change hillOriginalBaseSpectralSequence (⟨q.val.val,q.val.property⟩ : RealPeriodOneHillPotential) k = _
  rw [hillOriginalBaseSpectralSequence_apply]
  congr 1
  apply Complex.ext <;>
    simp [hillSignedSpectralCartesian,hillOriginalBirkhoffX,hillOriginalBirkhoffY]

/-- The literal real pair has the SAME physical action, not merely a
compatible total norm. Every positive closed gap is included. -/
theorem hillOriginalBirkhoff_action_identity
    (q : hillRealMeanZeroSourceSubmodule) (n : ℕ+) :
    (hillOriginalBirkhoffX q n)^2+(hillOriginalBirkhoffY q n)^2 =
      2*hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 n 0 := by
  dsimp only [hillOriginalBirkhoffX,hillOriginalBirkhoffY]
  rw [neg_sq]
  exact hillSpectralCartesian_action_identity (by simp) (by intro k; simp)
    q.val.val q.val.property.1 q.val.property.2 n n.pos

end NLS.KdV
