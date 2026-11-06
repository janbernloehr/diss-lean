import NLS.KdV.HillL2DirichletFourierEstimate
import NLS.KdV.HillDirichletFrequencyDisplacement
import NLS.ComplexAnalysis.SineEnergyReconstruction

/-! # The actual complex Dirichlet energy has its Fourier leading term

The mean potential is retained. The error after subtracting the cosine
Fourier pair is quadratic in the L2 source with inverse-index decay.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillDirichletEnergy_moving_fourier_bound (k : ℕ+) (u : Coeff 2) (E : ℂ)
    (hu : ‖u‖ ≤ 1/(16*Real.exp 1))
    (hE : ‖E-freeHillEnergy k‖ ≤ (k : ℝ)/16)
    (hzero : hillL2DirichletCharacteristic (Coeff.periodDouble u) E = 0) :
    ‖E-freeHillEnergy k-u 0+(u (-(k : ℤ))+u (k : ℤ))/2‖ ≤
      1024*(Real.exp 1)^4*‖u‖^2/(k : ℝ) := by
  let z := sqrt E
  let c : ℂ := (k : ℂ)*Real.pi
  let δ := z-c
  let s : ℂ := (-1)^(k : ℕ)
  let v := (u (-(k : ℤ))+u (k : ℤ))/2
  obtain ⟨hzlo,_,hδhalf,hδ⟩ := hillDirichlet_frequency_displacement_bound k (Coeff.periodDouble u) E
    (by simpa only [Coeff.norm_periodDouble] using hu) hE hzero
  rw [Coeff.norm_periodDouble] at hδ
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hkp : (0 : ℝ) < k := by positivity
  have hzn : 0 < ‖z‖ := hkp.trans_le hzlo
  have hδ1 : ‖z-c‖ ≤ 1 := by
    simpa only [z,c,mul_comm] using hδhalf.trans (by norm_num : (1/2 : ℝ) ≤ 1)
  have hδ' : ‖z-c‖ ≤ 8*(Real.exp 1)^2*‖u‖/(k : ℝ) := by simpa only [z,c,mul_comm] using hδ
  have hsmall : 4*Real.exp 1*‖u‖ ≤ ‖z‖ := by
    have h := (le_div_iff₀ (by positivity : 0 < 16*Real.exp 1)).mp hu
    nlinarith
  have hres := hillL2Dirichlet_fourier_residual_bound u (k : ℕ) z (norm_pos_iff.mp hzn) hδ1 hsmall
  have hsq : z^2 = E := sq_sqrt E
  rw [hsq,hzero,mul_zero] at hres
  have hsc : cos c = s := by
    have h := congrArg Complex.ofReal (Real.cos_nat_mul_pi (k : ℕ))
    push_cast at h
    exact h
  have hss : sin c = 0 := Complex.sin_nat_mul_pi (k : ℕ)
  have hs : sin z = s*sin δ := by
    have he : z = δ+c := by dsimp only [δ]; ring
    conv_lhs => rw [he,sin_add,hss,hsc]
    ring
  have hc : cos z = s*cos δ := by
    have he : z = δ+c := by dsimp only [δ]; ring
    conv_lhs => rw [he,cos_add,hss,hsc]
    ring
  have hsnorm : ‖s‖ = 1 := by simp only [s,norm_pow,norm_neg,norm_one,one_pow]
  have hid : 0-2*z*sin z-((-1 : ℂ)^(k : ℕ)*(u (-(k : ℤ))+u (k : ℤ))/2-cos z*u 0) =
      (-s)*(2*z*sin δ+v-cos δ*u 0) := by
    rw [hs,hc]
    dsimp only [s,v]
    ring
  rw [hid,norm_mul,norm_neg,hsnorm,one_mul] at hres
  have hres' : ‖2*z*sin δ+v-cos δ*u 0‖ ≤ 32*(Real.exp 1)^3*‖u‖^2/(k : ℝ) := by
    apply hres.trans
    calc
      _ ≤ 16*(Real.exp 1)^3*‖u‖^2/(k : ℝ)+
          2*Real.exp 1*(8*(Real.exp 1)^2*‖u‖/(k : ℝ))*‖u‖ := by gcongr
      _ = _ := by ring
  have hzup : ‖z‖ ≤ 5*(k : ℝ) := by
    have ht := norm_le_norm_sub_add z c
    have hcnorm : ‖c‖ = (k : ℝ)*Real.pi := by
      simp only [c,norm_mul,Complex.norm_natCast,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    rw [hcnorm] at ht
    nlinarith [hδ1,Real.pi_lt_four]
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have ht1 : ‖u‖ ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 16*Real.exp 1)).mp hu
    have hm := mul_nonneg (sub_nonneg.mpr he) (norm_nonneg u)
    nlinarith
  have hm : ‖u 0‖ ≤ ‖u‖ := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) u 0
  have h := norm_quadratic_energy_error_of_sine_residual z c (u 0) v (k : ℝ) ‖u‖ (Real.exp 1)
    hk ht1 he hzup hm hδ1 hδ' hres'
  have hfree : freeHillEnergy k = c^2 := by
    simp only [freeHillEnergy,c,ofReal_pow,ofReal_mul,ofReal_natCast]
  rwa [hsq,← hfree] at h

end NLS.KdV
