import NLS.SequenceSpaces.QuadraticFrequencyBounds
import NLS.SequenceSpaces.PositiveCoordinateAnalytic
import Mathlib.Analysis.Complex.SqrtDeriv

/-! The simultaneous slit domain for EVERY positive energy index is
OPEN. A single high-index coercivity estimate and a FINITE low-index
intersection prove this; no countable intersection is declared open. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.LpSequence

theorem analyticAt_quadraticLatticeEnergy (α : ℝ) (m : ℕ+)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : AnalyticAt ℂ (quadraticLatticeEnergy α m) t := by
  have he := ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).analyticAt t.2).comp
    (f := Prod.snd) analyticAt_snd
  exact (analyticAt_const.add (analyticAt_const.mul he)).add analyticAt_fst

theorem continuous_quadraticLatticeEnergy (α : ℝ) (m : ℕ+) : Continuous (quadraticLatticeEnergy α m) :=
  continuous_iff_continuousAt.mpr (fun t => (analyticAt_quadraticLatticeEnergy α m t).continuousAt)

theorem quadraticLatticeEnergy_re_pos_of_norm_bound (α : ℝ) (m : ℕ+)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (hsize : ‖t.2‖+‖t.1‖ < α^2*(m:ℕ)) :
    0 < (quadraticLatticeEnergy α m t).re := by
  have hm : (0:ℝ) < (m:ℕ) := by exact_mod_cast m.pos
  have hm1 : (1:ℝ) ≤ (m:ℕ) := by exact_mod_cast m.property
  have hd := (abs_le.mp ((abs_re_le_norm (t.2 m)).trans
    (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) t.2 m))).1
  have hc := (abs_le.mp (abs_re_le_norm t.1)).1
  have hdm := mul_le_mul_of_nonneg_left hd hm.le
  have hcm : ‖t.1‖ ≤ (m:ℕ)*‖t.1‖ := le_mul_of_one_le_left (norm_nonneg _) hm1
  have hmul : 0 < (m:ℕ)*(α^2*(m:ℕ)-‖t.2‖-‖t.1‖) :=
    mul_pos hm (by linarith)
  have he : (quadraticLatticeEnergy α m t).re = (α*(m:ℕ))^2+(m:ℕ)*(t.2 m).re+t.1.re := by
    simp only [quadraticLatticeEnergy,add_re,mul_re,pow_two,ofReal_re,natCast_re,
      ofReal_im,natCast_im,mul_zero,sub_zero,zero_mul,mul_im,add_zero]
  rw [he]
  nlinarith

def quadraticFrequencyDomain (α : ℝ) : Set (ℂ × lp (fun _ : ℕ+ => ℂ) 2) :=
  {t | ∀ m : ℕ+, quadraticLatticeEnergy α m t ∈ slitPlane}

theorem exists_quadraticFrequencyDomain_neighborhood (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (ht : t ∈ quadraticFrequencyDomain α) :
    ∃ U : Set (ℂ × lp (fun _ : ℕ+ => ℂ) 2), IsOpen U ∧ t ∈ U ∧ U ⊆ quadraticFrequencyDomain α := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((‖t.2‖+‖t.1‖+2)/α^2)
  have hN' : ‖t.2‖+‖t.1‖+2 < α^2*(N:ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ (sq_pos_of_pos hα)).mp hN
  let U₀ : Set (ℂ × lp (fun _ : ℕ+ => ℂ) 2) := {s | ‖s.1‖ < ‖t.1‖+1 ∧ ‖s.2‖ < ‖t.2‖+1}
  have hU₀ : IsOpen U₀ := (isOpen_lt continuous_fst.norm continuous_const).inter
    (isOpen_lt continuous_snd.norm continuous_const)
  let V : ℕ → Set (ℂ × lp (fun _ : ℕ+ => ℂ) 2) :=
    fun j => (quadraticLatticeEnergy α ⟨j+1,by omega⟩) ⁻¹' slitPlane
  have hV (j : ℕ) : IsOpen (V j) := isOpen_slitPlane.preimage (continuous_quadraticLatticeEnergy α _)
  let U := U₀ ∩ ⋂ j ∈ Finset.range N,V j
  refine ⟨U,hU₀.inter (isOpen_biInter_finset (fun j _ => hV j)),?_,?_⟩
  · refine ⟨⟨by linarith,by linarith⟩,?_⟩
    exact mem_iInter₂.mpr (fun j _ => ht ⟨j+1,by omega⟩)
  · intro s hs m
    by_cases hm : (m:ℕ) ≤ N
    · have hj : (m:ℕ)-1 ∈ Finset.range N := by simp only [Finset.mem_range]; have hp := m.pos; omega
      have he : (⟨(m:ℕ)-1+1,by omega⟩ : ℕ+) = m := by
        apply Subtype.ext
        exact Nat.sub_add_cancel m.property
      have hv := mem_iInter₂.mp hs.2 ((m:ℕ)-1) hj
      change quadraticLatticeEnergy α ⟨(m:ℕ)-1+1,by omega⟩ s ∈ slitPlane at hv
      rw [he] at hv
      exact hv
    · have hNm : (N:ℝ) ≤ (m:ℕ) := by exact_mod_cast (by omega : N ≤ (m:ℕ))
      have hlarge := hN'.trans_le (mul_le_mul_of_nonneg_left hNm (sq_nonneg α))
      have hsize : ‖s.2‖+‖s.1‖ < α^2*(m:ℕ) := by
        have hs₀ := hs.1
        change ‖s.1‖ < ‖t.1‖+1 ∧ ‖s.2‖ < ‖t.2‖+1 at hs₀
        linarith
      exact mem_slitPlane_iff.mpr (Or.inl (quadraticLatticeEnergy_re_pos_of_norm_bound α m s hsize))

theorem isOpen_quadraticFrequencyDomain (α : ℝ) (hα : 0 < α) : IsOpen (quadraticFrequencyDomain α) := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  obtain ⟨U,hU,htU,hsub⟩ := exists_quadraticFrequencyDomain_neighborhood α hα t ht
  exact Filter.mem_of_superset (hU.mem_nhds htU) hsub

end NLS.LpSequence
