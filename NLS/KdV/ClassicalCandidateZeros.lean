import NLS.KdV.ClassicalNormalizedResidues
import NLS.KdV.PositiveEnergyResolventKernel

/-! # Analytic candidate root coordinates on one sequence neighborhood

The actual selected critical frequencies are analytic. A small Hilbert
sequence displacement stays in every fixed positive frequency disc, with
uniform quadratic separation from all different critical energies.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillCriticalFrequency (N : ℕ) (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) : ℂ :=
  Complex.sqrt (classicalHillUniformCriticalPoint N k q)

def classicalHillCandidateDomain (V : Set (NLS.LinearVolterra.Curve ℂ)) :
    Set (NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) :=
  ball (0 : NLS.Coeff 2) (Real.pi/16) ×ˢ V

def classicalHillCandidateFrequency (N : ℕ) (k : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) : ℂ :=
  classicalHillCriticalFrequency N k t.2+t.1 (k : ℤ)

def classicalHillCandidateEnergy (N : ℕ) (k : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) : ℂ :=
  classicalHillCandidateFrequency N k t^2

theorem norm_le_of_positiveFrequencyDisc (k : ℕ+) (z : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    ‖z‖ ≤ (5*Real.pi/4)*(k : ℝ) := by
  have hzc := mem_closedBall_iff_norm.mp hz
  have ht := norm_le_norm_sub_add z ((Real.pi : ℂ)*(k : ℕ))
  have hcn : ‖(Real.pi : ℂ)*(k : ℕ)‖ = Real.pi*(k : ℝ) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_natCast]
  rw [hcn] at ht
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  nlinarith [Real.pi_pos]

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem critical_frequency_re_lower (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    Real.pi/2*(k : ℝ) ≤ (classicalHillCriticalFrequency N k q).re := by
  have hc := D.critical_close k q hq
  have hh := Complex.re_le_norm ((Real.pi : ℂ)*(k : ℕ)-classicalHillCriticalFrequency N k q)
  rw [norm_sub_rev] at hh
  have ht := hh.trans_lt hc
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.natCast_re,
    Complex.ofReal_im,Complex.natCast_im,mul_zero,sub_zero] at ht
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  nlinarith [Real.pi_pos]

theorem critical_frequency_re_pos (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    0 < (classicalHillCriticalFrequency N k q).re :=
  (by positivity : (0 : ℝ) < Real.pi/2*(k : ℝ)).trans_le (D.critical_frequency_re_lower k q hq)

theorem critical_energy_mem_slitPlane (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    classicalHillUniformCriticalPoint N k q ∈ slitPlane := by
  let w := classicalHillCriticalFrequency N k q
  have hre : 0 < w.re := D.critical_frequency_re_pos k q hq
  have hs : w^2 = classicalHillUniformCriticalPoint N k q := sq_sqrt _
  rw [← hs,Complex.mem_slitPlane_iff]
  by_cases him : w.im = 0
  · left
    simpa only [pow_two,Complex.mul_re,him,mul_zero,sub_zero] using sq_pos_of_pos hre
  · right
    rw [pow_two,Complex.mul_im]
    convert mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hre)) him using 1
    ring

theorem critical_frequency_analytic (k : ℕ+) :
    AnalyticOnNhd ℂ (classicalHillCriticalFrequency N k) V := by
  intro q hq
  exact (Complex.differentiableOn_sqrt.analyticAt
    (Complex.isOpen_slitPlane.mem_nhds (D.critical_energy_mem_slitPlane k q hq))).comp
      (D.critical_analytic k q hq)

theorem candidate_frequency_analytic (k : ℕ+) :
    AnalyticOnNhd ℂ (classicalHillCandidateFrequency N k) (classicalHillCandidateDomain V) := by
  intro t ht
  have hc := (D.critical_frequency_analytic k t.2 ht.2).comp
    (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => s.2) analyticAt_snd
  have he := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).analyticAt t.1).comp
    (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => s.1) analyticAt_fst
  exact hc.add he

theorem candidate_energy_analytic (k : ℕ+) :
    AnalyticOnNhd ℂ (classicalHillCandidateEnergy N k) (classicalHillCandidateDomain V) :=
  (D.candidate_frequency_analytic k).pow 2

theorem candidate_frequency_mem_disc (k : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    classicalHillCandidateFrequency N k t ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
  have he := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) t.1 (k : ℤ)
  have ht0 : ‖t.1‖ < Real.pi/16 := by simpa only [mem_ball,dist_zero_right] using ht.1
  have hc := D.critical_close k t.2 ht.2
  change ‖classicalHillCriticalFrequency N k t.2-(Real.pi : ℂ)*(k : ℕ)‖ < Real.pi/8 at hc
  have hb := norm_add_le (classicalHillCriticalFrequency N k t.2-(Real.pi : ℂ)*(k : ℕ)) (t.1 (k : ℤ))
  apply mem_closedBall_iff_norm.mpr
  have hh : classicalHillCandidateFrequency N k t-(Real.pi : ℂ)*(k : ℕ) =
      (classicalHillCriticalFrequency N k t.2-(Real.pi : ℂ)*(k : ℕ))+t.1 (k : ℤ) := by
    dsimp only [classicalHillCandidateFrequency]
    ring
  rw [hh]
  linarith [Real.pi_pos]

theorem candidate_energy_separation (k m : ℕ+) (hkm : k ≠ m)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    Real.pi^2/4*|(k : ℝ)^2-(m : ℝ)^2| ≤
      ‖classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N m t.2‖ := by
  have hm : classicalHillCriticalFrequency N m t.2 ∈ closedBall ((Real.pi : ℂ)*(m : ℕ)) (Real.pi/4) :=
    mem_closedBall_iff_norm.mpr ((D.critical_close m t.2 ht.2).le.trans (by linarith [Real.pi_pos]))
  simpa only [classicalHillCandidateEnergy,classicalHillCriticalFrequency,sq_sqrt] using
    highEnergyDiscs_separation m k (Ne.symm hkm) (classicalHillCandidateFrequency N k t) _
      (D.candidate_frequency_mem_disc k t ht) hm

theorem critical_frequency_norm_lower (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    Real.pi/2*(k : ℝ) ≤ ‖classicalHillCriticalFrequency N k q‖ :=
  (D.critical_frequency_re_lower k q hq).trans (Complex.re_le_norm _)

theorem critical_frequency_ne_zero (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    classicalHillCriticalFrequency N k q ≠ 0 :=
  norm_pos_iff.mp ((by positivity : (0 : ℝ) < Real.pi/2*(k : ℝ)).trans_le
    (D.critical_frequency_norm_lower k q hq))

theorem candidate_energy_sub_ne_zero (k m : ℕ+) (hkm : k ≠ m)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N m t.2 ≠ 0 := by
  have hd : (k : ℝ)^2-(m : ℝ)^2 ≠ 0 := positiveIndex_squared_sub_ne_zero k m hkm
  exact norm_pos_iff.mp ((mul_pos (by positivity : (0 : ℝ) < Real.pi^2/4)
    (abs_pos.mpr hd)).trans_le (D.candidate_energy_separation k m hkm t ht))

theorem norm_candidate_energy_sub_critical_le (k n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    ‖classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2‖ ≤
      4*Real.pi^2*((k : ℝ)^2+(n : ℝ)^2) := by
  have hz0 := norm_le_of_positiveFrequencyDisc k _ (D.candidate_frequency_mem_disc k t ht)
  have hz : ‖classicalHillCandidateFrequency N k t‖ ≤ 2*Real.pi*(k : ℝ) := by
    nlinarith [Real.pi_pos]
  have hnmem : classicalHillCriticalFrequency N n t.2 ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) :=
    mem_closedBall_iff_norm.mpr ((D.critical_close n t.2 ht.2).le.trans (by linarith [Real.pi_pos]))
  have hw0 := norm_le_of_positiveFrequencyDisc n _ hnmem
  have hw : ‖classicalHillCriticalFrequency N n t.2‖ ≤ 2*Real.pi*(n : ℝ) := by
    nlinarith [Real.pi_pos]
  have hsq : (classicalHillCriticalFrequency N n t.2)^2 = classicalHillUniformCriticalPoint N n t.2 := sq_sqrt _
  calc
    _ ≤ ‖classicalHillCandidateFrequency N k t‖^2+‖classicalHillCriticalFrequency N n t.2‖^2 := by
      simpa only [classicalHillCandidateEnergy,← hsq,norm_pow] using
        norm_sub_le (classicalHillCandidateEnergy N k t) (classicalHillUniformCriticalPoint N n t.2)
    _ ≤ (2*Real.pi*(k : ℝ))^2+(2*Real.pi*(n : ℝ))^2 :=
      add_le_add (pow_le_pow_left₀ (norm_nonneg _) hz 2) (pow_le_pow_left₀ (norm_nonneg _) hw 2)
    _ = _ := by ring

theorem norm_candidate_zero_multiplier_le (n k : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    ‖(classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2)/
      (2*classicalHillCriticalFrequency N k t.2*(k : ℂ))‖ ≤ 4*Real.pi*(1+(n : ℝ)^2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hk : (0 : ℝ) < k := by exact_mod_cast k.pos
  have hξ := D.critical_frequency_norm_lower k t.2 ht.2
  have hdiv : ((k : ℝ)^2+(n : ℝ)^2)/(k : ℝ)^2 ≤ 1+(n : ℝ)^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hk)).mpr
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (show 0 ≤ (k : ℝ)^2-1 by nlinarith)]
  rw [norm_div,norm_mul,norm_mul,norm_ofNat,Complex.norm_natCast]
  calc
    _ ≤ (4*Real.pi^2*((k : ℝ)^2+(n : ℝ)^2))/(2*(Real.pi/2*(k : ℝ))*(k : ℝ)) := by
      gcongr
      exact D.norm_candidate_energy_sub_critical_le k n t ht
    _ = (4*Real.pi)*(((k : ℝ)^2+(n : ℝ)^2)/(k : ℝ)^2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiv (by positivity)

theorem norm_candidate_zero_local_factor_le (k : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    ‖1+t.1 (k : ℤ)/(2*classicalHillCriticalFrequency N k t.2)‖ ≤ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hξ := D.critical_frequency_norm_lower k t.2 ht.2
  have hx := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) t.1 (k : ℤ)
  have hx0 : ‖t.1‖ < Real.pi/16 := by simpa only [mem_ball,dist_zero_right] using ht.1
  have hden : Real.pi ≤ 2*‖classicalHillCriticalFrequency N k t.2‖ := by
    nlinarith [Real.pi_pos]
  have hquot : ‖t.1 (k : ℤ)/(2*classicalHillCriticalFrequency N k t.2)‖ ≤ 1 := by
    rw [norm_div,norm_mul,norm_ofNat]
    apply (div_le_one (by nlinarith [Real.pi_pos] : 0 < 2*‖classicalHillCriticalFrequency N k t.2‖)).mpr
    linarith [Real.pi_pos]
  exact (norm_add_le _ _).trans (by rw [norm_one]; linarith)

end ClassicalAllContourPeriodData
end NLS.KdV
