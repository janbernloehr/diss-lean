import NLS.ComplexAnalysis.SquareRootExteriorShift
import NLS.KdV.HillEnergyCircleFrequencySeparation
import NLS.KdV.HillHminusOneRealMiuraEnergyPsi
import NLS.ZakharovShabat.SourcePsiCriticalQuotientExterior
import NLS.KdV.HillHminusOneCriticalPoints
/-! # Actual Miura energy numerators on complete exterior energy circles

The fixed complex energy translation is retained. Both square-root signs
and both antisymmetrized source terms are controlled without a real-type
restriction or a prescribed exterior decay hypothesis.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem exists_hillHminusMiuraEnergyPsi_critical_quotient_bound
    (C : HillHminusMiuraChart) (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n)
    (n : ℤ) (q : PeriodOneHminusOne) (hq : q ∈ C.domain) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      deriv (hillHminusDiscriminant q) E ≠ 0 ∧
      ‖hillHminusMiuraEnergyPsi C s n (E,q)/deriv (hillHminusDiscriminant q) E‖ ≤
        32/centralCircleRadius k := by
  obtain ⟨R,hR,hbound⟩ := exists_threshold_sourcePsiCandidate_criticalQuotient_le
    (by simp : (2 : ENNReal) ≠ ⊤) (by norm_num : 1 < (2 : ENNReal)) n
    (s n (C.criticalSource q) : Coeff 2) (C.criticalSource q)
    (by positivity : 0 < Real.pi/8) (by linarith [Real.pi_pos] : Real.pi/8 ≤ Real.pi/4)
  obtain ⟨K,hK⟩ := exists_nat_gt ((R+2*Real.pi/8+‖C.energyShift‖/(Real.pi/8)+1)/Real.pi)
  refine ⟨K,?_⟩
  intro k hk E hE
  let z := sqrt E
  let w := sqrt (E+C.energyShift)
  let ρ := centralCircleRadius k
  have hρ : 0 < ρ := centralCircleRadius_pos k
  have hz : ‖z‖ = ρ := by
    simpa only [mem_sphere,dist_zero_right] using hillEnergyCircle_sqrt_mem_centralCircle k E hE
  have hKρ : R+2*Real.pi/8+‖C.energyShift‖/(Real.pi/8)+1 < ρ := by
    have ht := (div_lt_iff₀ Real.pi_pos).mp hK
    have hkn : (K : ℝ) ≤ k := by exact_mod_cast hk
    dsimp only [ρ,centralCircleRadius]
    nlinarith [Real.pi_pos]
  have hsmall : ‖C.energyShift‖ ≤ (Real.pi/8)*‖z‖ := by
    rw [hz]
    have ht := (div_le_iff₀ (by positivity : 0 < Real.pi/8)).mp
      (show ‖C.energyShift‖/(Real.pi/8) ≤ ρ by linarith [Real.pi_pos])
    nlinarith
  have hsq : w^2 = z^2+C.energyShift := by dsimp only [w,z];rw [sq_sqrt,sq_sqrt]
  obtain ⟨hwnorm,hwsep⟩ := shifted_square_root_separation w z C.energyShift hsq
    (Real.pi/8) (Real.pi/8) (by rw [hz];exact hρ) hsmall (fun m => by
      have ht := hillEnergyCircle_sqrt_free_separation k E hE m
      change Real.pi/8+Real.pi/8 ≤ ‖sqrt E-(Real.pi : ℂ)*m‖
      linarith)
  have hcpos : 0 ≤ ‖C.energyShift‖/(Real.pi/8) := by positivity
  have hwR : R ≤ ‖w‖ := by rw [hz] at hwnorm;linarith [Real.pi_pos]
  have hwpos : 0 < ‖w‖ := hR.trans_le hwR
  have hw : w ≠ 0 := norm_pos_iff.mp hwpos
  have hwρ : ρ/2 ≤ ‖w‖ := by
    rw [hz] at hwnorm
    have hn : 0 ≤ ‖C.energyShift‖/(Real.pi/8) := by positivity
    linarith [Real.pi_pos]
  have hwE : w^2-C.energyShift = E := by dsimp only [w];rw [sq_sqrt,add_sub_cancel_right]
  have hplus := hbound w hwR hwsep
  have hminus := hbound (-w) (by simpa only [norm_neg] using hwR) (fun m => by
    simpa only [Int.cast_neg,mul_neg,sub_neg_eq_add,neg_sub_left,norm_neg,add_comm] using hwsep (-m))
  let D := deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q)))
  have hD : D w = (2*w)*deriv (hillHminusDiscriminant q) E := by
    dsimp only [D]
    rw [C.frequency_derivative_eq q hq,hwE]
  have hDm : D (-w) = -(D w) := by
    dsimp only [D]
    rw [C.frequency_derivative_eq q hq,C.frequency_derivative_eq q hq,neg_sq]
    ring
  have hd : deriv (hillHminusDiscriminant q) E ≠ 0 := by
    intro he
    exact hplus.1 (by change D w = 0;rw [hD,he,mul_zero])
  have hfactor := hillHminusMiuraEnergyPsi_factor C s n q w
  rw [hwE] at hfactor
  have heq : hillHminusMiuraEnergyPsi C s n (E,q)/deriv (hillHminusDiscriminant q) E =
      hillHminusMiuraSourcePsi C s n (w,q)/D w+
        hillHminusMiuraSourcePsi C s n (-w,q)/D (-w) := by
    rw [hDm,hD]
    field_simp [hw,hd]
    linear_combination hfactor
  refine ⟨hd,?_⟩
  rw [heq]
  have hbplus : ‖hillHminusMiuraSourcePsi C s n (w,q)/D w‖ ≤ 8/‖w‖ := hplus.2
  have hbminus : ‖hillHminusMiuraSourcePsi C s n (-w,q)/D (-w)‖ ≤ 8/‖w‖ := by
    simpa only [norm_neg,hillHminusMiuraSourcePsi,D] using! hminus.2
  apply (norm_add_le _ _).trans
  have hsum := add_le_add hbplus hbminus
  apply hsum.trans
  change 8/‖w‖+8/‖w‖ ≤ 32/ρ
  calc
    8/‖w‖+8/‖w‖ = 16/‖w‖ := by ring
    _ ≤ 32/ρ := by
      apply (div_le_div_iff₀ hwpos hρ).mpr
      nlinarith
end NLS.KdV
