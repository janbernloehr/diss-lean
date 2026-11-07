import NLS.Articles.KdVKdV2Frequencies.NativeActionNormalization
import NLS.Articles.KdVKdV2Frequencies.GlobalWeakFrequencyNormalization
import NLS.Articles.KdVKdV2Frequencies.SignedPhaseFlow

/-! The ACTUAL globally calibrated KdV frequencies on normalized native
Birkhoff targets. Reality is proved before taking real parts. -/
noncomputable section
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def nativeTargetActions (z : physicalRealDeletedSubmodule) : Coeff 1 :=
  quadraticActionsExponent (q := 1) (deletedToSignedPair actionIndexEquiv z.val)

def nativeTargetWeakActions (t : ℝ) (ht : 0≤t) (z : physicalRealDeletedSubmodule) : Coeff 1 :=
  normalizedSobolevWeakActionInclusion (2*t-1) (by linarith) (nativeTargetActions z)

theorem nativeTargetActions_nonnegative (z : physicalRealDeletedSubmodule) :
    nativeTargetActions z∈Coeff.nonnegativeLocus 1 :=
  Coeff.quadraticActions_mem_nonnegativeLocus _ (deletedToSignedPair_real _ _ z.property)

theorem continuous_nativeTargetWeakActions (t : ℝ) (ht : 0≤t) :
    Continuous (nativeTargetWeakActions t ht) := by
  have hQ : Continuous (quadraticActionsExponent (p := 2) (q := 1)) :=
    continuousOn_univ.mp analyticOnNhd_quadraticActionsExponent.continuousOn
  exact (normalizedSobolevWeakActionInclusion (2*t-1) (by linarith)).continuous.comp
    (hQ.comp ((deletedToSignedPair actionIndexEquiv).continuous.comp continuous_subtype_val))

theorem nativeTargetWeakActions_nonnegative (t : ℝ) (ht : 0≤t) (z : physicalRealDeletedSubmodule) :
    nativeTargetWeakActions t ht z∈Coeff.nonnegativeLocus 1 :=
  normalizedSobolevWeakActionInclusion_nonnegative _ _ _ (nativeTargetActions_nonnegative z)

theorem calibrated_frequency_correction_real
    (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a : Coeff 1) (ha : a∈Coeff.nonnegativeLocus 1) (n : ℕ+) : (G n a).im=0 := by
  obtain ⟨P,z,hz,hzr,rfl⟩ := exists_physical_pair_of_nonnegative_actions D a ha
  rw [hrec P z hz hzr n]
  exact physicalMiuraFrequencyChart_real D P.source_chart (P.potential z)
    (P.real_potential z hz hzr) (P.mean_zero z hz) (P.source_mem z hz) n

def nativeTargetKdVFrequency (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ)
    (z : physicalRealDeletedSubmodule) (n : ℕ+) : ℝ :=
  (2*(n:ℝ)*Real.pi)^3+(G n (nativeTargetWeakActions t ht z)).re

def nativeTargetKdVNaturalFrequency (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ)
    (z : physicalRealDeletedSubmodule) (n : ℕ) : ℝ :=
  if hn : 0<n then nativeTargetKdVFrequency t ht G z ⟨n,hn⟩ else 0

def nativeTargetKdVSignedFrequency (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ)
    (z : physicalRealDeletedSubmodule) : ℤ → ℝ :=
  signedHamiltonianFrequency (nativeTargetKdVNaturalFrequency t ht G z)

theorem nativeTargetKdVSignedFrequency_odd (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (z : physicalRealDeletedSubmodule) (j : ℤ) :
    nativeTargetKdVSignedFrequency t ht G z (-j)= -nativeTargetKdVSignedFrequency t ht G z j :=
  signedHamiltonianFrequency_neg _ j

theorem nativeTargetKdVSignedFrequency_positive (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (z : physicalRealDeletedSubmodule) (n : ℕ+) :
    nativeTargetKdVSignedFrequency t ht G z (n:ℤ)=nativeTargetKdVFrequency t ht G z n := by
  simp only [nativeTargetKdVSignedFrequency,signedHamiltonianFrequency,
    if_pos (by exact_mod_cast n.pos : (0:ℤ)<n),Int.natAbs_natCast,
    nativeTargetKdVNaturalFrequency,dif_pos n.pos]
  apply congrArg (nativeTargetKdVFrequency t ht G z)
  exact Subtype.ext rfl

theorem continuous_nativeTargetKdVFrequency (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1))
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V) (n : ℕ+) :
    Continuous (fun z => nativeTargetKdVFrequency t ht G z n) := by
  have hc : Continuous (fun z => G n (nativeTargetWeakActions t ht z)) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (hG n _ (hCV (nativeTargetWeakActions_nonnegative t ht z))).continuousAt.comp
        (continuous_nativeTargetWeakActions t ht).continuousAt)
  exact continuous_const.add (Complex.continuous_re.comp hc)

theorem nativeTargetKdVFrequency_actual_source
    (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a : physicalRealDeletedSubmodule) (n : ℕ+) :
    (nativeTargetKdVFrequency t ht G (D.realNativeForward t ht a) n:ℂ)=
      roughKdVFrequency D G n (GlobalRoughAbelianForwardData.realNativeSource t ht a) := by
  have hr := calibrated_frequency_correction_real D G hrec _
    (nativeTargetWeakActions_nonnegative t ht (D.realNativeForward t ht a)) n
  have he : ( (G n (nativeTargetWeakActions t ht (D.realNativeForward t ht a))).re:ℂ)=
      G n (nativeTargetWeakActions t ht (D.realNativeForward t ht a)) := Complex.ext rfl (by simpa using hr.symm)
  change (((2*(n:ℝ)*Real.pi)^3+(G n (nativeTargetWeakActions t ht (D.realNativeForward t ht a))).re:ℝ):ℂ)=_
  rw [Complex.ofReal_add,he]
  change _=(2*(n:ℂ)*Real.pi)^3+G n (roughWeakActionCoordinates D _)
  have hw := nativeActionCoordinates_weak D t ht a
  change nativeTargetWeakActions t ht (D.realNativeForward t ht a)=_ at hw
  rw [hw]
  push_cast
  rfl

end NLS.Articles.KdVKdV2Frequencies
