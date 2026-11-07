import NLS.Fourier.PeriodicVariationalUniqueness
import NLS.ZakharovShabat.ContinuousPotentialL2Class
import NLS.ZakharovShabat.SourcePhysicalL2Equiv

/-! # Pointwise uniqueness of continuous periodic physical Hilbert gradients -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

private theorem integral_pair_continuous_class (g : ℝ → ℂ × ℂ) (Φ : Curve (ℂ × ℂ)) :
    (∫ x in (0:ℝ)..1, (g x).1*(continuousPotentialL2Class Φ).ofLp.1 x+
      (g x).2*(continuousPotentialL2Class Φ).ofLp.2 x) =
    ∫ x in (0:ℝ)..1, (g x).1*(extend Φ x).1+(g x).2*(extend Φ x).2 := by
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  filter_upwards [continuousPotentialL2Class_representative Φ] with x hx
  rw [show (continuousPotentialL2Class Φ).ofLp.1 x = (extend Φ x).1 from congrArg Prod.fst hx,
    show (continuousPotentialL2Class Φ).ofLp.2 x = (extend Φ x).2 from congrArg Prod.snd hx]

theorem eq_of_continuous_periodic_physical_L2_pairings (f g : ℝ → ℂ × ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (h : ∀ u : IntervalPairL2,
      (∫ x in (0:ℝ)..1, (f x).1*u.ofLp.1 x+(f x).2*u.ofLp.2 x) =
      ∫ x in (0:ℝ)..1, (g x).1*u.ofLp.1 x+(g x).2*u.ofLp.2 x) : f = g := by
  have ht (v : ℝ → ℂ) (hv : Continuous v) :
      (∫ x in (0:ℝ)..1, (f x).1*v x) = (∫ x in (0:ℝ)..1, (g x).1*v x) ∧
      (∫ x in (0:ℝ)..1, (f x).2*v x) = (∫ x in (0:ℝ)..1, (g x).2*v x) := by
    let Φ₁ : Curve (ℂ × ℂ) := ⟨fun x => (v x,0),(hv.comp continuous_subtype_val).prodMk continuous_const⟩
    let Φ₂ : Curve (ℂ × ℂ) := ⟨fun x => (0,v x),continuous_const.prodMk (hv.comp continuous_subtype_val)⟩
    have h₁ := h (continuousPotentialL2Class Φ₁)
    have h₂ := h (continuousPotentialL2Class Φ₂)
    rw [integral_pair_continuous_class,integral_pair_continuous_class] at h₁ h₂
    have he₁ (k : ℝ → ℂ × ℂ) :
        (∫ x in (0:ℝ)..1, (k x).1*(extend Φ₁ x).1+(k x).2*(extend Φ₁ x).2) =
        ∫ x in (0:ℝ)..1, (k x).1*v x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) 1 := by simpa using hx
      simp [NLS.LinearVolterra.extend,Φ₁,projIcc_of_mem _ hx']
    have he₂ (k : ℝ → ℂ × ℂ) :
        (∫ x in (0:ℝ)..1, (k x).1*(extend Φ₂ x).1+(k x).2*(extend Φ₂ x).2) =
        ∫ x in (0:ℝ)..1, (k x).2*v x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) 1 := by simpa using hx
      simp [NLS.LinearVolterra.extend,Φ₂,projIcc_of_mem _ hx']
    exact ⟨(he₁ f).symm.trans (h₁.trans (he₁ g)),(he₂ f).symm.trans (h₂.trans (he₂ g))⟩
  have h₁ := NLS.Fourier.eq_of_periodic_integral_mul_eq (fun x => (f x).1) (fun x => (g x).1)
    hf.fst hg.fst (fun x => congrArg Prod.fst (hpf x)) (fun x => congrArg Prod.fst (hpg x))
    (fun v hv _ => by simpa only [mul_comm] using (ht v hv.continuous).1)
  have h₂ := NLS.Fourier.eq_of_periodic_integral_mul_eq (fun x => (f x).2) (fun x => (g x).2)
    hf.snd hg.snd (fun x => congrArg Prod.snd (hpf x)) (fun x => congrArg Prod.snd (hpg x))
    (fun v hv _ => by simpa only [mul_comm] using (ht v hv.continuous).2)
  funext x
  exact Prod.ext (congrFun h₁ x) (congrFun h₂ x)

end NLS.ZakharovShabat
