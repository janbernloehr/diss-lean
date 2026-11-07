import NLS.Articles.KdVKdV2Frequencies.WeightedPairRenormalizedRecovery
import NLS.SequenceSpaces.FinitePairActionIdentity
import NLS.SequenceSpaces.RealFormIdentity

/-! ONE complex pair neighborhood identifies the FULL physical
correction with the SAME global weak scalar frequency in the original
Sobolev actions. Finite physical data suffice; all closed gaps remain. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_complex_sobolev_frequency_agreement
    (D : GlobalRoughAbelianForwardData) (B : PhysicalMiuraFrequencyChart) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (R : (Coeff 2 × Coeff 2) → PeriodOneHminusOne) (U : Set (Coeff 2 × Coeff 2)) (hU : IsOpen U)
    (hRreal : ∀ z∈U, z∈Coeff.realPairLocus 2 → IsRealPeriodOneHminusOne (R z))
    (hRzero : ∀ z∈U, (R z).val 0=0) (hRB : ∀ z∈U, R z∈B.domain)
    (hRsigned : ∀ z∈U, z∈Coeff.realPairLocus 2 → ∀ j : ℤ,
      (D.signed (R z)).val j=(signedPairToDeleted actionIndexEquiv z).val j/(Weight.sobolev (t-1/2) j : ℂ))
    (f : ℕ+ → (Coeff 2 × Coeff 2) → ℂ) (hf : ∀ n, AnalyticOnNhd ℂ (f n) U)
    (hphysical : ∀ n, ∀ z∈U, f n z=B.correction n (R z)+12*sourceComplexHigherAction
      (by norm_num) (by norm_num) (n:ℤ) 1 (hillMiuraDiagonal (B.psi.miura.lift (R z))))
    (z₀ : Coeff 2 × Coeff 2) (hz₀ : z₀∈U) (hzr : z₀∈Coeff.realPairLocus 2) :
    ∃ ρ : ℝ, 0<ρ ∧ ball z₀ ρ⊆U ∧
      (∀ z∈ball z₀ ρ, normalizedSobolevWeakActionInclusion (2*t-1) (by linarith)
        (quadraticActionsExponent (q := 1) z)∈V) ∧
      ∀ n, ∀ z∈ball z₀ ρ, f n z=normalizedSobolevRenormalizedFrequency (2*t-1)
        (by linarith) G n (quadraticActionsExponent (q := 1) z) := by
  let Q := quadraticActionsExponent (p := 2) (q := 1)
  let κ := normalizedSobolevWeakActionInclusion (2*t-1) (by linarith : -1≤2*t-1)
  let W := Q ⁻¹' (κ ⁻¹' V)
  have hQa : AnalyticOnNhd ℂ Q univ := analyticOnNhd_quadraticActionsExponent
  have hW : IsOpen W := (hV.preimage κ.continuous).preimage (continuousOn_univ.mp hQa.continuousOn)
  have hrealW : ∀ z∈Coeff.realPairLocus 2, z∈W := fun z hz =>
    hCV (normalizedSobolevWeakActionInclusion_nonnegative (2*t-1) (by linarith) _
      (Coeff.quadraticActions_mem_nonnegativeLocus z hz))
  let g := fun n z => normalizedSobolevRenormalizedFrequency (2*t-1) (by linarith) G n (Q z)
  have hg (n : ℕ+) : AnalyticOnNhd ℂ (g n) W := by
    intro z hz
    exact (normalizedSobolevRenormalizedFrequency_analytic (2*t-1) (by linarith) G V hG n
      (Q z) hz).comp (hQa z (mem_univ _))
  have hreal (n : ℕ+) (z : Coeff 2 × Coeff 2) (hz : z∈U) (hzreal : z∈Coeff.realPairLocus 2) :
      f n z=g n z := by
    apply Coeff.eq_of_finite_pair_action_agreement (q := 1) (by norm_num : (2 : ℝ≥0∞)≠⊤)
      U W hU hW (f n) (g n) (hf n).continuousOn (hg n).continuousOn _
      z hz z (hrealW z hzreal) hzreal hzreal rfl
    intro S u hu v _hv hur _hvr huS _hvS huv
    have hc := finite_weighted_pair_global_renormalized_calibration D B t ht G hrec
      (R u) (hRreal u hu hur) (hRzero u hu) (hRB u hu) u hur (hRsigned u hu hur) S huS n
    rw [hphysical n u hu]
    change _=normalizedSobolevRenormalizedFrequency (2*t-1) _ G n (quadraticActionsExponent (q := 1) v)
    rw [huv]
    exact hc.symm
  obtain ⟨ρ,hρ,hsub⟩ := Metric.isOpen_iff.mp (hU.inter hW) z₀ ⟨hz₀,hrealW z₀ hzr⟩
  refine ⟨ρ,hρ,(fun z hz => (hsub hz).1),(fun z hz => (hsub hz).2),?_⟩
  intro n
  exact Coeff.eqOn_of_realPair_agreement (f n) (g n) (ball z₀ ρ) isOpen_ball (convex_ball z₀ ρ)
    z₀ (mem_ball_self hρ) hzr ((hf n).mono (fun z hz => (hsub hz).1)).differentiableOn
    ((hg n).mono (fun z hz => (hsub hz).2)).differentiableOn
    (fun z hz hzreal => hreal n z (hsub hz).1 hzreal)

end NLS.Articles.KdVKdV2Frequencies
