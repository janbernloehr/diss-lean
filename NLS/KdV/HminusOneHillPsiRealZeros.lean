import NLS.KdV.HminusOneLocalHillEnergyCycles
import NLS.KdV.MiuraHillPsiRealZeros

/-! Every retained original positive real Hill gap contains a zero of
the actual local energy numerator. Full original endpoint labels and
the exact physical constant shift are retained at every index. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillHminusDirichletBall

theorem exists_psiNumerator_zero_in_original_gap (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A) (hr : IsRealPeriodOneHminusOne q)
    (n m : ℕ+) (hmn : m ≠ n) :
    ∃ E : ℝ, E ∈ Icc (hillHminusLabels q hr (2*(m:ℕ)-1)) (hillHminusLabels q hr (2*(m:ℕ))) ∧
      B.psiNumerator A n ((E:ℂ),q) = 0 := by
  let u : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift q,B.miuraBall.actionBall.lift_real q hq.1 hr⟩
  obtain ⟨x,hx,hzero⟩ := A.exists_retained_energy_zero u n m hmn
  have ha := hillMiura_positive_gap_left_pos u ((m:ℕ):ℤ) (by exact_mod_cast m.pos)
  change 0 < (hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re at ha
  have hxpos : 0 ≤ x := ha.le.trans hx.1
  have hl : (hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re^2 ≤ x^2 := by
    simpa only [pow_two] using mul_self_le_mul_self ha.le hx.1
  have hh : x^2 ≤ (hillMiuraDiracRight u.val ((m:ℕ):ℤ)).re^2 := by
    simpa only [pow_two] using mul_self_le_mul_self hxpos hx.2
  have he := hillHminusLabels_pair_eq_squared_miuraDirac q hr u B.miuraBall.actionBall.shift
    (B.miuraBall.actionBall.image q hq.1) (B.miuraBall.actionBall.outside q hq.1) (m:ℕ) m.pos
  refine ⟨x^2-B.miuraBall.actionBall.shift,?_,?_⟩
  · rw [he.1,he.2]
    exact ⟨sub_le_sub_right hl _,sub_le_sub_right hh _⟩
  · simpa only [psiNumerator,Complex.ofReal_sub,Complex.ofReal_pow,sub_add_cancel] using hzero

theorem psiNumerator_zero_at_real_collapsed_gap (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A) (hr : IsRealPeriodOneHminusOne q)
    (n m : ℕ+) (hmn : m ≠ n)
    (hc : hillHminusLabels q hr (2*(m:ℕ)-1) = hillHminusLabels q hr (2*(m:ℕ))) :
    B.psiNumerator A n ((hillHminusLabels q hr (2*(m:ℕ)):ℂ),q) = 0 := by
  obtain ⟨E,hE,hzero⟩ := B.exists_psiNumerator_zero_in_original_gap A q hq hr n m hmn
  have he : E = hillHminusLabels q hr (2*(m:ℕ)) := by rw [hc] at hE; exact le_antisymm hE.2 hE.1
  simpa only [he] using hzero

end HillHminusDirichletBall
end NLS.KdV
