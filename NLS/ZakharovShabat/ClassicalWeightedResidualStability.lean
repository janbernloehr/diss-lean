import NLS.ZakharovShabat.ClassicalFundamentalSolution
import NLS.ComplexAnalysis.NormalizedDuhamelBound
import NLS.FunctionalAnalysis.IntegralGronwall

/-! # Residual stability with the actual exponential frequency weight

Free-propagator Duhamel estimates avoid the two extra fundamental-column
growth factors in the adjugate estimate. The constant depends only on the
potential, while the forcing and error retain their common time weight.
-/

noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

theorem classical_zero_initial_forced_duhamel (Φ g : Curve (ℂ × ℂ)) (z : ℂ)
    (u : ℝ → ℂ × ℂ) (hu : Continuous u) (h0 : u 0 = 0)
    (hd : ∀ s : Icc (0 : ℝ) 1, HasDerivAt u
      (classicalODECoefficient (Φ s) z (u s) + g s) s) (t : Icc (0 : ℝ) 1) :
    (u t).1 = ∫ s in (0 : ℝ)..t.val, exp (-I*z*(t.val-s)) *
      (I*(extend Φ s).1*(u s).2 + (extend g s).1) ∧
    (u t).2 = ∫ s in (0 : ℝ)..t.val, exp (I*z*(t.val-s)) *
      ((-I)*(extend Φ s).2*(u s).1 + (extend g s).2) := by
  have hΦ := continuous_extend Φ
  have hgcont := continuous_extend g
  have hc₁ : Continuous (fun s => I*(extend Φ s).1*(u s).2 + (extend g s).1) := by
    fun_prop
  have hc₂ : Continuous (fun s => (-I)*(extend Φ s).2*(u s).1 + (extend g s).2) := by
    fun_prop
  constructor
  · have h := scalar_duhamel (-I*z) (fun s => (u s).1) _ t t.property.1 hu.fst hc₁ (by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le.trans t.property.2⟩
      simpa [classicalODECoefficient_apply, Prod.fst_add, NLS.LinearVolterra.extend,
        projIcc_of_mem _ hs', add_assoc] using (HasFDerivAt.hasDerivAt (hd ⟨s, hs'⟩).fst))
    simpa only [h0, Prod.fst_zero, mul_zero, zero_add, ofReal_sub] using h
  · have h := scalar_duhamel (I*z) (fun s => (u s).2) _ t t.property.1 hu.snd hc₂ (by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le.trans t.property.2⟩
      simpa [classicalODECoefficient_apply, Prod.snd_add, NLS.LinearVolterra.extend,
        projIcc_of_mem _ hs', add_comm, add_left_comm, add_assoc] using (HasFDerivAt.hasDerivAt (hd ⟨s, hs'⟩).snd))
    simpa only [h0, Prod.snd_zero, mul_zero, zero_add, ofReal_sub] using h

theorem norm_zero_initial_forced_le_exp_weight (Φ g : Curve (ℂ × ℂ)) (z : ℂ)
    (u : ℝ → ℂ × ℂ) (hu : Continuous u) (h0 : u 0 = 0)
    (hd : ∀ s : Icc (0 : ℝ) 1, HasDerivAt u
      (classicalODECoefficient (Φ s) z (u s) + g s) s)
    (D : ℝ) (hD : 0 ≤ D)
    (hg : ∀ s : Icc (0 : ℝ) 1, ‖g s‖ ≤ D * Real.exp (|z.im| * s.val))
    (t : Icc (0 : ℝ) 1) :
    ‖u t‖ ≤ D * Real.exp ‖Φ‖ * Real.exp (|z.im| * t.val) := by
  let f : ℝ → ℝ := fun s => Real.exp (-(|z.im| * s)) * ‖u s‖
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hbound (s : Icc (0 : ℝ) 1) : f s ≤ D + ‖Φ‖ * ∫ x in (0 : ℝ)..s.val, f x := by
    let H : ℝ → ℝ := fun x => ‖Φ‖ * ‖u x‖ + D * Real.exp (|z.im| * x)
    have hH : Continuous H := by dsimp [H]; fun_prop
    have hmajor (x : ℝ) (hx : x ∈ Icc 0 s.val) :
        ‖I*(extend Φ x).1*(u x).2 + (extend g x).1‖ ≤ H x ∧
        ‖(-I)*(extend Φ x).2*(u x).1 + (extend g x).2‖ ≤ H x := by
      have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans s.property.2⟩
      have hgx : ‖extend g x‖ ≤ D * Real.exp (|z.im| * x) := by
        simpa only [NLS.LinearVolterra.extend, projIcc_of_mem _ hx'] using hg ⟨x, hx'⟩
      constructor
      · apply (norm_add_le _ _).trans
        dsimp [H]
        simp only [norm_mul, norm_I, one_mul]
        exact add_le_add (mul_le_mul
          ((norm_fst_le _).trans (Φ.norm_coe_le_norm _)) (norm_snd_le _)
          (norm_nonneg _) (norm_nonneg _)) ((norm_fst_le _).trans hgx)
      · apply (norm_add_le _ _).trans
        dsimp [H]
        simp only [norm_mul, norm_neg, norm_I, one_mul]
        exact add_le_add (mul_le_mul
          ((norm_snd_le _).trans (Φ.norm_coe_le_norm _)) (norm_fst_le _)
          (norm_nonneg _) (norm_nonneg _)) ((norm_snd_le _).trans hgx)
    have h₁ := norm_exp_integral_weighted_le (-I*z) |z.im| s.val
      (by simpa [mul_re] using le_abs_self z.im) s.property.1 _ H hH
      (fun x hx => (hmajor x hx).1)
    have h₂ := norm_exp_integral_weighted_le (I*z) |z.im| s.val
      (by simpa [mul_re] using neg_le_abs z.im) s.property.1 _ H hH
      (fun x hx => (hmajor x hx).2)
    obtain ⟨he₁, he₂⟩ := classical_zero_initial_forced_duhamel Φ g z u hu h0 hd s
    have he : (∫ x in (0 : ℝ)..s.val, Real.exp (-|z.im| * x) * H x) =
        ‖Φ‖ * (∫ x in (0 : ℝ)..s.val, f x) + D * s.val := by
      have heq (x : ℝ) : Real.exp (-|z.im| * x) * H x = ‖Φ‖ * f x + D := by
        dsimp [H, f]
        rw [mul_add]
        have hex : Real.exp (-|z.im| * x) * Real.exp (|z.im| * x) = 1 := by
          rw [← Real.exp_add, show -|z.im| * x + |z.im| * x = 0 by ring, Real.exp_zero]
        rw [show Real.exp (-|z.im| * x) * (D * Real.exp (|z.im| * x)) = D by
          calc
            _ = D * (Real.exp (-|z.im| * x) * Real.exp (|z.im| * x)) := by ring
            _ = D := by rw [hex, mul_one]]
        rw [neg_mul]
        ring
      simp_rw [heq]
      have hi : IntervalIntegrable (fun x => ‖Φ‖ * f x) volume 0 s.val :=
        (hf.const_mul ‖Φ‖).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hi intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, mul_comm s.val D]
    rw [he] at h₁ h₂
    have hnorm : f s ≤ ‖Φ‖ * (∫ x in (0 : ℝ)..s.val, f x) + D * s.val := by
      dsimp [f]
      rw [Prod.norm_def, mul_max_of_nonneg _ _ (Real.exp_nonneg _)]
      apply max_le
      · rw [he₁]
        simpa only [ofReal_sub, neg_mul, f] using h₁
      · rw [he₂]
        simpa only [ofReal_sub, neg_mul, f] using h₂
    have hDs : D * s.val ≤ D := mul_le_of_le_one_right hD s.property.2
    linarith
  have hb := le_exp_of_le_const_add_integral f hf 1 D ‖Φ‖ hD (norm_nonneg _)
    (fun x _ => by dsimp [f]; positivity) (fun x hx => hbound ⟨x, hx⟩) t t.property
  have hsmall : f t ≤ D * Real.exp ‖Φ‖ := hb.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_of_le_one_right (norm_nonneg _) t.property.2)) hD)
  have he := mul_le_mul_of_nonneg_right hsmall (Real.exp_nonneg (|z.im| * t.val))
  have hex : Real.exp (-(|z.im| * t.val)) * Real.exp (|z.im| * t.val) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  simpa only [f, mul_right_comm _ ‖u t‖, hex, one_mul] using he

end NLS.ZakharovShabat
