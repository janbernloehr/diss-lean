import NLS.Articles.KdVKdV2Frequencies.OriginalKdVBirkhoffFlow
import NLS.Articles.KdVKdV2Frequencies.ActualNativeFlowCompatibility
import NLS.Articles.KdVKdV2Frequencies.Corollary15BoundedL2
import NLS.SequenceSpaces.RealPhaseSmoothing

/-! The actual KdV phase contribution to Corollary 1.7 gains ONE
full derivative with an EXACT linear time bound. Its constant is uniform
on EVERY bounded original L2 source set. Full physical one-smoothing
still requires the forward/inverse Birkhoff-minus-Fourier remainders. -/
noncomputable section
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def airySignedFrequency (j : ℤ) : ℝ := (2*(j:ℝ)*Real.pi)^3

theorem airySignedFrequency_odd (j : ℤ) : airySignedFrequency (-j)= -airySignedFrequency j := by
  unfold airySignedFrequency
  rw [Int.cast_neg]
  ring

def NativeKdVPhaseGainAt (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (C : ℝ) (a : physicalRealDeletedSubmodule) : Prop :=
  ∀ time : ℝ, ∃ T : WeightedCoeff (Weight.sobolev ((1:ℝ)-1/2)) 2 →L[ℂ]
      WeightedCoeff (Weight.sobolev ((1:ℝ)-1/2+1)) 2,
      ‖T‖≤|time| * C ∧
      (∀ b j, (T b).val j=(Complex.exp (((time*nativeTargetKdVSignedFrequency 1 (by norm_num) G
        (D.realNativeForward 1 (by norm_num) a) j:ℝ):ℂ)*I)-
        Complex.exp (((time*airySignedFrequency j:ℝ):ℂ)*I))*b.val j) ∧
      WeightedCoeff.sobolevInclusion (by norm_num : (1:ℝ)-1/2≤1-1/2+1)
        (T (D.realNativeTarget 1 (by norm_num) a))=
        D.realNativeTarget 1 (by norm_num) (nativeKdVSourceFlow D 1 (by norm_num) G time a)-
          WeightedCoeff.phaseFlow (Weight.sobolev ((1:ℝ)-1/2)) airySignedFrequency time
            (D.realNativeTarget 1 (by norm_num) a)

def ActualNativeKdVPhaseGain (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ) : Prop :=
  ∀ S : Set physicalRealDeletedSubmodule, Bornology.IsBounded S → ∃ C : ℝ, 0≤C ∧
    ∀ a∈S, NativeKdVPhaseGainAt D G C a

def OriginalKdVPhaseGain (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ) : Prop :=
  ∀ S : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))),
    Bornology.IsBounded S → ∃ C : ℝ, 0≤C ∧ ∀ q∈S, NativeKdVPhaseGainAt D G C
      ((physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((0:ℕ):ℝ))
        (Weight.sobolev_neg ((0:ℕ):ℝ))).symm q)

theorem exists_actual_native_kdv_phase_gain
    (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : NLS.Articles.KdVConvexity.PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z) :
    ActualNativeKdVPhaseGain D G := by
  intro S hS
  obtain ⟨M,hM,hb⟩ := exists_native_bounded_l2_frequency_bound D G V hV hCV hG hrec S hS
  refine ⟨2*M,by positivity,?_⟩
  intro a ha time
  let ω := nativeTargetKdVSignedFrequency 1 (by norm_num) G (D.realNativeForward 1 (by norm_num) a)
  have hpos (n : ℕ+) : (n:ℝ) * |ω (n:ℤ)-airySignedFrequency (n:ℤ)|≤M := by
    have he : ((ω (n:ℤ)-airySignedFrequency (n:ℤ):ℝ):ℂ)=
        roughKdVFrequency D G n (GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) a)-
          8*(n:ℂ)^3*(Real.pi:ℂ)^3 := by
      dsimp only [ω]
      rw [nativeTargetKdVSignedFrequency_positive,Complex.ofReal_sub,
        nativeTargetKdVFrequency_actual_source D 1 (by norm_num) G hrec]
      unfold airySignedFrequency
      push_cast
      ring
    have hn := congrArg norm he
    rw [Complex.norm_real,Real.norm_eq_abs] at hn
    simpa only [hn] using hb a ha n
  have hω := odd_frequency_bracket_bound_of_positive ω airySignedFrequency
    (nativeTargetKdVSignedFrequency_odd 1 (by norm_num) G _) airySignedFrequency_odd M hM hpos
  obtain ⟨T,hT,hTn⟩ := WeightedCoeff.exists_sobolev_real_phase_gain_multiplier (p := 2)
    ((1:ℝ)-1/2) time ω airySignedFrequency (2*M) (by positivity) hω
  refine ⟨T,hTn,hT,?_⟩
  rw [nativeKdVSourceFlow_raw_target]
  apply Subtype.ext
  funext j
  rw [WeightedCoeff.sobolevInclusion_apply,hT]
  rw [WeightedCoeff.sub_val,WeightedCoeff.phaseFlow_apply,WeightedCoeff.phaseFlow_apply]
  ring

theorem original_kdv_phase_gain_of_native
    (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (h : ActualNativeKdVPhaseGain D G) : OriginalKdVPhaseGain D G := by
  intro S hS
  let e := (physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((0:ℕ):ℝ))
    (Weight.sobolev_neg ((0:ℕ):ℝ))).symm
  have hS' : Bornology.IsBounded (e '' S) := e.isometry.lipschitz.isBounded_image hS
  obtain ⟨C,hC,hall⟩ := h (e '' S) hS'
  exact ⟨C,hC,fun q hq => hall (e q) ⟨q,hq,rfl⟩⟩

theorem GlobalRoughAbelianForwardData.corollary_1_7_actual_phase_dependency (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
      ∃ hCV : Coeff.nonnegativeLocus 1⊆V, ∃ hG : ∀ n, AnalyticOnNhd ℂ (G n) V,
      IsOpen V ∧ (∀ (B : PhysicalMiuraFrequencyChart) (q : PeriodOneHminusOne),
        IsRealPeriodOneHminusOne q → q.val 0=0 → q∈B.domain → ∀ n : ℕ+,
          roughKdVFrequency D G n q=(2*(n:ℂ)*Real.pi)^3+B.correction n q) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)), ∀ n : ℕ+,
        roughKdVFrequency D G n (nativeHillSource 1 q.val)=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n:ℂ)) ∧
      (∀ (s : ℝ) (hs : -1≤s),
        Continuous (fun x : ℝ × physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) =>
          originalKdVBirkhoffFlow D s hs G x.1 x.2) ∧
        (∀ T : ℝ, Continuous (originalKdVBirkhoffTrajectory D s hs G V
          hCV hG T)) ∧
        (∀ q, originalKdVBirkhoffFlow D s hs G 0 q=q) ∧
        ∀ time u q, originalKdVBirkhoffFlow D s hs G time (originalKdVBirkhoffFlow D s hs G u q)=
          originalKdVBirkhoffFlow D s hs G (time+u) q) ∧
      OriginalKdVPhaseGain D G ∧
      (∀ (t : ℝ) (ht : 0≤t) time a,
        physicalRealSobolevInclusion (by linarith : (-1:ℝ)≤t-1) (nativeKdVSourceFlow D t ht G time a)=
          nativeKdVSourceFlow D 0 (by norm_num) G time
            (physicalRealSobolevInclusion (by linarith : (-1:ℝ)≤t-1) a)) ∧
      ∀ (t : ℝ) (ht : 0≤t) a n,
        (nativeTargetKdVFrequency t ht G (D.realNativeForward t ht a) n:ℂ)=
          roughKdVFrequency D G n (GlobalRoughAbelianForwardData.realNativeSource t ht a) := by
  obtain ⟨V,G,hV,hCV,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  refine ⟨V,G,hCV,hG,hV,?_,roughKdVFrequency_native_recovery D G hrec,?_,
    original_kdv_phase_gain_of_native D G (exists_actual_native_kdv_phase_gain D G V hV hCV hG hrec),
    (fun t ht time a => nativeKdVSourceFlow_weak D t ht G time a),
    (fun t ht a n => nativeTargetKdVFrequency_actual_source D t ht G hrec a n)⟩
  · intro B q hr hm hq n
    rw [roughKdVFrequency,roughKdVFrequencyCorrection_eq_physical D G hrec B q hr hm hq n]
  · intro s hs
    exact ⟨continuous_originalKdVBirkhoffFlow D s hs G V hCV hG,
      continuous_originalKdVBirkhoffTrajectory D s hs G V hCV hG,
      originalKdVBirkhoffFlow_zero D s hs G,originalKdVBirkhoffFlow_add D s hs G⟩

end NLS.Articles.KdVKdV2Frequencies
