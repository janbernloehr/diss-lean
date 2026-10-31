import NLS.Dynamics.UnboundedPhaseObstruction
import NLS.SequenceSpaces.PhaseRotation

/-! # Successive-frequency separation in Section 22

Diverging frequencies admit a strictly increasing subsequence with a
prescribed gap. Its relative phase is minus one at positive times no
larger than the prescribed horizon. Varying amplitudes retain the exact
amplitude-minus-sequence-error bound and eventual half-amplitude separation.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Dynamics

/-- Diverging real frequencies have a strictly increasing subsequence
with any prescribed lower bound on successive frequency gaps. -/
theorem exists_frequency_gap_subsequence (freq : ℕ → ℝ)
    (hfreq : Tendsto freq atTop atTop) (L : ℝ) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ m, L ≤ freq (r (m+1))-freq (r m) := by
  classical
  have hstep (j : ℕ) : ∃ k : ℕ, j < k ∧ freq j+L ≤ freq k :=
    ((eventually_gt_atTop j).and (hfreq.eventually (eventually_ge_atTop (freq j+L)))).exists
  choose next hnext hgap using hstep
  let r : ℕ → ℕ := Nat.rec 0 (fun _ j => next j)
  have hs (m : ℕ) : r (m+1) = next (r m) := rfl
  refine ⟨r,strictMono_nat_of_lt_succ (fun m => ?_),fun m => ?_⟩
  · rw [hs]
    exact hnext (r m)
  · rw [hs]
    linarith [hgap (r m)]

/-- The printed successive-frequency construction: every selected gap
has a positive time at most T at which its relative phase is minus one. -/
theorem exists_phase_separating_times (freq : ℕ → ℝ)
    (hfreq : Tendsto freq atTop atTop) (T : ℝ) (hT : 0 < T) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ time : ℕ → ℝ,
      (∀ m, 0 < time m ∧ time m ≤ T) ∧
      ∀ m, Complex.exp ((((time m*(freq (r (m+1))-freq (r m)) : ℝ) : ℂ))*Complex.I) = -1 := by
  obtain ⟨r,hr,hgap⟩ := exists_frequency_gap_subsequence freq hfreq (Real.pi/T)
  let time : ℕ → ℝ := fun m => Real.pi/(freq (r (m+1))-freq (r m))
  have hd (m : ℕ) : 0 < freq (r (m+1))-freq (r m) :=
    (div_pos Real.pi_pos hT).trans_le (hgap m)
  refine ⟨r,hr,time,fun m => ⟨div_pos Real.pi_pos (hd m),?_⟩,fun m => ?_⟩
  · apply (div_le_iff₀ (hd m)).mpr
    have h := (div_le_iff₀ hT).mp (hgap m)
    nlinarith
  · dsimp [time]
    rw [div_mul_cancel₀ _ (hd m).ne',Complex.exp_pi_mul_I]

/-- A separated relative phase gives the source's amplitude-minus-error
lower bound, with both initial amplitudes allowed to vary. -/
theorem norm_phase_pair_lower (freq₀ freq₁ t : ℝ) (a b : ℂ)
    (hphase : 1 ≤ ‖Complex.exp ((((t*(freq₁-freq₀) : ℝ) : ℂ))*Complex.I)-1‖) :
    ‖a‖-‖b-a‖ ≤ ‖Complex.exp ((((t*freq₁ : ℝ) : ℂ))*Complex.I)*b-
      Complex.exp ((((t*freq₀ : ℝ) : ℂ))*Complex.I)*a‖ := by
  let e := Complex.exp ((((t*(freq₁-freq₀) : ℝ) : ℂ))*Complex.I)
  have he : Complex.exp ((((t*freq₁ : ℝ) : ℂ))*Complex.I) =
      Complex.exp ((((t*freq₀ : ℝ) : ℂ))*Complex.I)*e := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hn : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hfact : ‖Complex.exp ((((t*freq₁ : ℝ) : ℂ))*Complex.I)*b-
      Complex.exp ((((t*freq₀ : ℝ) : ℂ))*Complex.I)*a‖ = ‖e*b-a‖ := by
    rw [he,mul_assoc,← mul_sub,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  rw [hfact]
  have htri : ‖(e-1)*a‖ ≤ ‖e*b-a‖+‖b-a‖ := by
    calc
      _ = ‖(e*b-a)-e*(b-a)‖ := by congr 1; ring
      _ ≤ ‖e*b-a‖+‖e*(b-a)‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul,hn,one_mul]
  have hamp : ‖a‖ ≤ ‖(e-1)*a‖ := by
    rw [norm_mul]
    exact (one_mul ‖a‖).symm.trans_le (mul_le_mul_of_nonneg_right hphase (norm_nonneg a))
  linarith

end NLS.Dynamics

namespace NLS.Coeff

/-- The displayed coordinate separation along a subsequence, including the
amplitude-minus-sequence-error bound and eventual half-amplitude separation. -/
theorem exists_phase_separated_subsequence {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (freq : ℕ → ℝ) (hfreq : Tendsto freq atTop atTop)
    (z : ℕ → Coeff p) (z₀ : Coeff p) (hz : Tendsto z atTop (𝓝 z₀))
    (n : ℤ) (hn : z₀ n ≠ 0) (T : ℝ) (hT : 0 < T) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ time : ℕ → ℝ,
      (∀ m, 0 < time m ∧ time m ≤ T) ∧
      (∀ m, 1 ≤ ‖Complex.exp ((((time m*(freq (r (m+1))-freq (r m)) : ℝ) : ℂ))*Complex.I)-1‖ ∧
        ‖z (r m) n‖-‖z (r (m+1))-z (r m)‖ ≤
          ‖Complex.exp ((((time m*freq (r (m+1)) : ℝ) : ℂ))*Complex.I)*z (r (m+1)) n-
            Complex.exp ((((time m*freq (r m) : ℝ) : ℂ))*Complex.I)*z (r m) n‖) ∧
      ∀ᶠ m : ℕ in atTop, ‖z₀ n‖/2 ≤
        ‖Complex.exp ((((time m*freq (r (m+1)) : ℝ) : ℂ))*Complex.I)*z (r (m+1)) n-
          Complex.exp ((((time m*freq (r m) : ℝ) : ℂ))*Complex.I)*z (r m) n‖ := by
  obtain ⟨r,hr,time,ht,he⟩ := NLS.Dynamics.exists_phase_separating_times freq hfreq T hT
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne'
  have hphase (m : ℕ) : 1 ≤ ‖Complex.exp ((((time m*(freq (r (m+1))-freq (r m)) : ℝ) : ℂ))*Complex.I)-1‖ := by
    rw [he m]
    norm_num
  have hlower (m : ℕ) : ‖z (r m) n‖-‖z (r (m+1))-z (r m)‖ ≤
      ‖Complex.exp ((((time m*freq (r (m+1)) : ℝ) : ℂ))*Complex.I)*z (r (m+1)) n-
        Complex.exp ((((time m*freq (r m) : ℝ) : ℂ))*Complex.I)*z (r m) n‖ := by
    have hs := NLS.Dynamics.norm_phase_pair_lower (freq (r m)) (freq (r (m+1))) (time m)
      (z (r m) n) (z (r (m+1)) n) (hphase m)
    have hd : ‖z (r (m+1)) n-z (r m) n‖ ≤ ‖z (r (m+1))-z (r m)‖ :=
      lp.norm_apply_le_norm hp0 (z (r (m+1))-z (r m)) n
    linarith
  refine ⟨r,hr,time,ht,fun m => ⟨hphase m,hlower m⟩,?_⟩
  have hz₁ := hz.comp hr.tendsto_atTop
  have hr₂ : StrictMono (fun m : ℕ => r (m+1)) := fun i j hij => hr (Nat.add_lt_add_right hij 1)
  have hz₂ := hz.comp hr₂.tendsto_atTop
  have heval : Tendsto (fun m => z (r m) n) atTop (𝓝 (z₀ n)) :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.continuousAt.tendsto).comp hz₁
  have hlim : Tendsto (fun m : ℕ => ‖z (r m) n‖-‖z (r (m+1))-z (r m)‖)
      atTop (𝓝 ‖z₀ n‖) := by
    simpa only [sub_self,norm_zero,sub_zero,Function.comp_def] using heval.norm.sub (hz₂.sub hz₁).norm
  have hnpos : 0 < ‖z₀ n‖ := norm_pos_iff.mpr hn
  filter_upwards [hlim.eventually (lt_mem_nhds (show ‖z₀ n‖/2 < ‖z₀ n‖ by linarith))] with m hm
  exact hm.le.trans (hlower m)

end NLS.Coeff
