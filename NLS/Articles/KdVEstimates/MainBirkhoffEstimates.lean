import NLS.KdV.HillOriginalBirkhoffSobolevRestriction
import NLS.KdV.HillOriginalBirkhoffWeightedRestriction
import NLS.KdV.HillOriginalBirkhoffActions
import NLS.Articles.KdVEstimates.IntegerSpectralEstimates
import NLS.Articles.KdVEstimates.WeightedSpectralEstimate

noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.KdV
namespace NLS.Articles.KdVEstimates

/-- Main Theorem 1 for the ONE fixed ORIGINAL real Birkhoff map. Source
and target have the exact paper norms, and both restrictions retain
literally the same raw coordinate pairs of that global analytic map. -/
theorem theorem1 (m : ℕ) (hm : 1 ≤ m) :
    ∃ c d : ℝ, 0<c ∧ 0<d ∧
      ∀ p : RealHillWeightedPotential (hillIntegerWeight m), ∀ hmean : p.val.val 0=0,
      let b := hillRealNativeIntegerLower m (m-1) (by omega) p
      let S := ‖hillOriginalBirkhoffSobolevRestriction m m le_rfl p hmean‖
      let T := ‖hillOriginalBirkhoffSobolevRestriction m (m-1) (by omega) p hmean‖
      (S ≤ c*(‖p.val‖+(1+‖b.val‖)^m*‖b.val‖)) ∧
      (‖p.val‖ ≤ d*(S+(1+T)^m*T)) := by
  obtain ⟨c,d,hc,hd,hbound⟩ := integer_hillSpectralSequence_estimates (by simp) (by intro k; simp) m hm
  refine ⟨c,d,hc,hd,?_⟩
  intro p hmean
  dsimp only
  rw [norm_hillOriginalBirkhoffSobolevRestriction,norm_hillOriginalBirkhoffSobolevRestriction]
  exact hbound p hmean

/-- Main Theorem 2 expressed in the actions of the SAME fixed original
real Birkhoff map, with convergence and physical action identity proved. -/
theorem theorem2 (m : ℕ) (hm : 1 ≤ m) :
    ∃ c d : ℝ, 0<c ∧ 0<d ∧
      ∀ p : RealHillWeightedPotential (hillIntegerWeight m), ∀ hmean : p.val.val 0=0,
      let q := hillOriginalWeightedMeanZeroSource (hillIntegerWeight m) p hmean
      let A := fun j : ℕ => ∑' k : ℕ, (2*Real.pi*(k+1 : ℕ))^(2*j+1)*hillOriginalBirkhoffAction q k
      let b := hillRealNativeIntegerLower m (m-1) (by omega) p
      (A m ≤ c^2*(‖p.val‖^2+(1+‖b.val‖)^(2*m)*‖b.val‖^2)) ∧
      (‖p.val‖^2 ≤ d^2*(A m+(1+A (m-1))^m*A (m-1))) := by
  obtain ⟨c,d,hc,hd,hbound⟩ := theorem2_native m hm
  refine ⟨c,d,hc,hd,?_⟩
  intro p hmean
  dsimp only
  rw [hillOriginalBirkhoffActionMass_eq_native m m le_rfl,
    hillOriginalBirkhoffActionMass_eq_native m (m-1) (by omega)]
  exact hbound p hmean

/-- Main Theorem 3(i), including target membership of the SAME fixed
real map for the full source weight class, including exponential weights. -/
theorem theorem3_birkhoff (r : ℝ) (hr0 : 0≤r) (hr1 : r≤1/2) (v : SpectralWeight) :
    let w := SpectralWeight.product (SpectralWeight.sobolev r hr0) v
    ∃ c : ℝ, 0<c ∧ ∀ p : RealHillWeightedPotential w, ∀ hmean : p.val.val 0=0,
      ‖hillOriginalBirkhoffWeightedRestriction w p hmean‖ ≤
        c*((1+‖p.val‖)+w.realExtension (16*‖p.val‖^(3/2-r)))*‖p.val‖ := by
  obtain ⟨c,hc,hbound⟩ := weighted_hillSpectralSequence_bound (by simp) (by intro k; simp) r hr0 hr1 v
  refine ⟨c,hc,?_⟩
  intro p hmean
  rw [norm_hillOriginalBirkhoffWeightedRestriction]
  exact hbound p hmean

/-- BOTH parts of Main Theorem 3 with ONE common constant and the actions
of that SAME fixed original real Birkhoff map. -/
theorem theorem3 (r : ℝ) (hr0 : 0≤r) (hr1 : r≤1/2) (v : SpectralWeight) :
    let w := SpectralWeight.product (SpectralWeight.sobolev r hr0) v
    ∃ c : ℝ, 0<c ∧ ∀ p : RealHillWeightedPotential w, ∀ hmean : p.val.val 0=0,
      (‖hillOriginalBirkhoffWeightedRestriction w p hmean‖ ≤
        c*((1+‖p.val‖)+w.realExtension (16*‖p.val‖^(3/2-r)))*‖p.val‖) ∧
      ((∑' k : ℕ, (w (2*((k+1 : ℕ) : ℤ)))^2*(2*Real.pi*(k+1 : ℕ))*
        hillOriginalBirkhoffAction (hillOriginalWeightedMeanZeroSource w p hmean) k) ≤
        c^2*((1+‖p.val‖)^2+(w.realExtension (16*‖p.val‖^(3/2-r)))^2)*‖p.val‖^2) := by
  obtain ⟨c,hc,hforward⟩ := theorem3_birkhoff r hr0 hr1 v
  obtain ⟨d,hd,haction⟩ := theorem3_actions r hr0 hr1 v
  dsimp only at hforward haction ⊢
  let w := SpectralWeight.product (SpectralWeight.sobolev r hr0) v
  refine ⟨c+d,by positivity,?_⟩
  intro p hmean
  constructor
  · apply (hforward p hmean).trans
    have hB : 0 ≤ ((1+‖p.val‖)+w.realExtension (16*‖p.val‖^(3/2-r)))*‖p.val‖ :=
      mul_nonneg (add_nonneg (by positivity) (w.realExtension_pos _).le) (norm_nonneg _)
    dsimp only [w] at hB
    nlinarith [mul_nonneg hd.le hB]
  · simp_rw [hillOriginalBirkhoffAction_weighted_source]
    apply (haction p hmean).trans
    have hB : 0 ≤ ((1+‖p.val‖)^2+(w.realExtension (16*‖p.val‖^(3/2-r)))^2)*‖p.val‖^2 := by positivity
    have he : d^2 ≤ (c+d)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right he hB
    simpa only [mul_assoc,w] using hh

end NLS.Articles.KdVEstimates
