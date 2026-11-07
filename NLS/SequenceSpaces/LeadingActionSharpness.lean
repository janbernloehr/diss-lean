import NLS.SequenceSpaces.FrequencyLeadingAction
import NLS.SequenceSpaces.NonnegativeActions

/-! A literal nonzero leading action term prevents every stronger
locally uniform frequency bound. Packets remain in the positive cone. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.Coeff

theorem exists_action_packet_frequency_lower_bound
    (e : ℤ ≃ ℕ+) (a₀ : Coeff 1) (ha₀ : a₀∈nonnegativeLocus 1)
    (ρ : ℝ) (hρ : 0<ρ) (α r : ℝ) (hαr : α<r)
    (f g : ℕ+ → Coeff 1 → ℂ)
    (he : ∀ n a, g n a=f n a+6*(a (e.symm n)/(Weight.sobolev α (n:ℤ):ℂ)))
    (htail : ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈ball a₀ ρ, ∀ n : ℕ+,
      K≤(n:ℤ).natAbs → Weight.sobolev α (n:ℤ)*‖g n a‖≤ε)
    (M : ℝ) (hM : 0≤M) (K : ℕ) :
    ∃ a∈ball a₀ ρ∩nonnegativeLocus 1, ∃ n : ℕ+,
      K≤(n:ℤ).natAbs ∧ M<Weight.sobolev r (n:ℤ)*‖f n a‖ := by
  classical
  let δ := ρ/2
  have hδ : 0<δ := half_pos hρ
  obtain ⟨L,hL⟩ := htail δ hδ
  obtain ⟨J,hJ⟩ := Weight.exists_sobolev_ratio_tail α r hαr
    (div_pos hδ (by linarith : 0<M+1))
  let n : ℕ+ := ⟨max K (max L J)+1,by omega⟩
  have hnK : K≤(n:ℤ).natAbs := by change K≤max K (max L J)+1;omega
  have hnL : L≤(n:ℤ).natAbs := by change L≤max K (max L J)+1;omega
  have hnJ : J≤(n:ℤ).natAbs := by change J≤max K (max L J)+1;omega
  let a : Coeff 1 := a₀+lp.single 1 (e.symm n) (δ:ℂ)
  have hab : a∈ball a₀ ρ := by
    rw [mem_ball,dist_eq_norm]
    change ‖a₀+lp.single 1 (e.symm n) (δ:ℂ)-a₀‖<ρ
    rw [add_sub_cancel_left,lp.norm_single (by norm_num : (0:ℝ≥0∞)<1),
      Complex.norm_real,Real.norm_of_nonneg hδ.le]
    exact half_lt_self hρ
  have hac : a∈nonnegativeLocus 1 := by
    intro j
    change ((a₀ j+(lp.single (E := fun _ : ℤ => ℂ) 1 (e.symm n) (δ:ℂ)) j)).im=0 ∧
      0≤((a₀ j+(lp.single (E := fun _ : ℤ => ℂ) 1 (e.symm n) (δ:ℂ)) j)).re
    by_cases hj : j=e.symm n
    · subst j
      simpa [lp.single_apply] using And.intro (ha₀ (e.symm n)).1
        (add_nonneg (ha₀ (e.symm n)).2 hδ.le)
    · simpa [lp.single_apply,hj] using ha₀ j
  have hcoord : δ≤‖a (e.symm n)‖ := by
    have hre : δ≤(a (e.symm n)).re := by
      change δ≤(a₀ (e.symm n)+(lp.single (E := fun _ : ℤ => ℂ) 1 (e.symm n) (δ:ℂ)) (e.symm n)).re
      simp only [lp.single_apply,Pi.single_eq_same,add_re,ofReal_re]
      linarith [(ha₀ (e.symm n)).2]
    exact hre.trans (Complex.re_le_norm _)
  refine ⟨a,⟨hab,hac⟩,n,hnK,?_⟩
  by_contra! hbad
  have hsmall : Weight.sobolev α (n:ℤ)*‖f n a‖≤δ := by
    have hw := (Weight.sobolev r).positive (n:ℤ)
    calc
      _=(Weight.sobolev α (n:ℤ)/Weight.sobolev r (n:ℤ))*(Weight.sobolev r (n:ℤ)*‖f n a‖) := by field_simp
      _ ≤ (δ/(M+1))*M := mul_le_mul (hJ (n:ℤ) hnJ).le hbad
        (by positivity) (by positivity)
      _ ≤ δ := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by linarith : 0<M+1)).mpr
        nlinarith
  have hc : Weight.sobolev α (n:ℤ)*‖(6:ℂ)*(a (e.symm n)/(Weight.sobolev α (n:ℤ):ℂ))‖=6*‖a (e.symm n)‖ := by
    rw [norm_mul,norm_div,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_of_nonneg ((Weight.sobolev α).positive (n:ℤ)).le]
    field_simp [((Weight.sobolev α).positive (n:ℤ)).ne']
    exact mul_div_cancel_left₀ _ ((Weight.sobolev α).positive (n:ℤ)).ne'
  have hn := mul_le_mul_of_nonneg_left (norm_sub_le (g n a) (f n a))
    ((Weight.sobolev α).positive (n:ℤ)).le
  have hs : g n a-f n a=(6:ℂ)*(a (e.symm n)/(Weight.sobolev α (n:ℤ):ℂ)) := by
    rw [he]
    ring
  rw [hs,mul_add,hc] at hn
  have hg := hL a hab n hnL
  nlinarith

end NLS.Coeff
